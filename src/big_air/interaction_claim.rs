//! # Big AIR Interaction Claims
//!
//! This module defines the interaction claim structures for the Big AIR STARK proof system.
//! It contains the main interaction claim struct that combines all individual component
//! interaction claims and provides utilities for managing lookup relations.
//!
//! # Overview
//!
//! The Big AIR system combines multiple STARK proof components into a single proof.
//! Each component generates its own interaction claims that must be coordinated
//! to ensure the overall proof system maintains soundness and completeness.
//!
//! # Components
//!
//! - **BigInteractionClaim**: Main interaction claim struct containing all component claims
//! - **Interaction Management**: Functions for mixing claims and computing total sums
//! - **Lookup Relations**: Ensures all lookup relations are properly balanced
//! - **Trace Generation**: Coordinates interaction trace generation across all components
//!
//! # Architecture
//!
//! The module coordinates interaction claims across:
//! - NTT operations (forward and inverse transforms)
//! - Arithmetic operations (addition, multiplication, subtraction)
//! - Range checking and signature bound validation
//! - Root of unity precomputation and validation
//!
//! This ensures that all lookup relations are properly balanced and the
//! overall proof system maintains cryptographic soundness.

use crate::{
    HIGH_SIG_BOUND, LOW_SIG_BOUND, POLY_LOG_SIZE,
    big_air::{
        claim::AllTraces,
        relation::{INTTInputLookupElements, InputLookupElements, LookupElements},
    },
    impl_big_ic,
    ntts::{intt, ntt, roots},
    polys::{euclidean_norm, mul, sub},
    zq::{Q, range_check},
};
use itertools::{Itertools, chain};
use stwo::{
    core::fields::{m31::M31, qm31::QM31},
    prover::{
        backend::simd::SimdBackend,
        poly::{BitReversedOrder, circle::CircleEvaluation},
    },
};

impl_big_ic!(
    #[derive(Debug, Clone)]
    pub struct BigInteractionClaim {
        pub f_ntt_butterfly: ntt::butterfly::InteractionClaim,
        pub f_ntt_merges: Vec<ntt::InteractionClaim>,
        pub g_ntt_butterfly: ntt::butterfly::InteractionClaim,
        pub g_ntt_merges: Vec<ntt::InteractionClaim>,
        pub mul: mul::InteractionClaim,
        pub intt_merges: Vec<intt::InteractionClaim>,
        pub ibutterfly: intt::ibutterfly::InteractionClaim,
        pub sub: sub::InteractionClaim,
        pub euclidean_norm: euclidean_norm::InteractionClaim,
        pub half_range_check: range_check::InteractionClaim,
        pub low_sig_bound_check: range_check::InteractionClaim,
        pub high_sig_bound_check: range_check::InteractionClaim,
        pub range_check: range_check::InteractionClaim,
        pub roots: Vec<roots::preprocessed::InteractionClaim>,
        pub inv_roots: Vec<roots::inv_preprocessed::InteractionClaim>,
    }
);

impl BigInteractionClaim {
    /// Generates interaction traces for all components in the Big AIR system.
    ///
    /// This function coordinates the generation of interaction traces across all
    /// proof components, ensuring that lookup relations are properly established
    /// and balanced. It generates traces for NTT operations, arithmetic operations,
    /// range checking, and root of unity validation.
    ///
    /// # Parameters
    ///
    /// - `lookup_elements`: The lookup elements for range checking and validation
    /// - `traces`: All execution traces from the main proof components
    ///
    /// # Returns
    ///
    /// Returns a tuple containing:
    /// - Combined interaction traces for all components
    /// - The complete big interaction claim with all component claims
    ///
    /// # Algorithm
    ///
    /// 1. Generates NTT butterfly interaction traces and claims
    /// 2. Generates NTT merge interaction traces and claims for each stage
    /// 3. Generates multiplication interaction traces and claims
    /// 4. Generates INTT split interaction traces and claims for each stage
    /// 5. Generates inverse butterfly interaction traces and claims
    /// 6. Generates arithmetic operation interaction traces and claims
    /// 7. Generates range checking interaction traces and claims
    /// 8. Generates root of unity validation interaction traces and claims
    pub fn gen_interaction_trace(
        lookup_elements: &LookupElements,
        traces: &AllTraces,
    ) -> (
        Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Self,
    ) {
        // Generate interaction traces and claims for the forward NTT butterfly operation
        // This establishes lookup relations between the butterfly trace and range checking
        let (f_ntt_butterfly_interaction_trace, f_ntt_butterfly_interaction_claim) =
            ntt::butterfly::InteractionClaim::gen_interaction_trace(
                &traces.f_ntt_butterfly,
                &lookup_elements.rc,
                &lookup_elements.f_ntt_butterfly,
            );
        // Initialize vectors to collect interaction traces and claims for NTT merge stages
        let mut f_ntt_interaction_traces = vec![];
        let mut f_ntt_interaction_claims = vec![];

        // Generate interaction traces and claims for each NTT merge stage
        // Each stage processes different input lookup elements based on the stage index
        for (i, merge) in traces.f_ntt_merges.iter().enumerate() {
            let (f_ntt_interaction_trace, f_ntt_interaction_claim) =
                ntt::InteractionClaim::gen_interaction_trace(
                    merge,
                    &lookup_elements.rc,
                    &lookup_elements.f_ntt,
                    &if i == 0 {
                        InputLookupElements::Butterfly(lookup_elements.f_ntt_butterfly.clone())
                    } else {
                        InputLookupElements::NTT(lookup_elements.f_ntt.clone())
                    },
                    &lookup_elements.roots,
                );
            f_ntt_interaction_traces.push(f_ntt_interaction_trace);
            f_ntt_interaction_claims.push(f_ntt_interaction_claim);
        }

        // Generate interaction traces and claims for the G polynomial NTT butterfly operation
        // This is similar to the F polynomial but operates on the G polynomial trace
        let (g_ntt_butterfly_interaction_trace, g_ntt_butterfly_interaction_claim) =
            ntt::butterfly::InteractionClaim::gen_interaction_trace(
                &traces.g_ntt_butterfly,
                &lookup_elements.rc,
                &lookup_elements.g_ntt_butterfly,
            );
        let mut g_ntt_interaction_traces = vec![];
        let mut g_ntt_interaction_claims = vec![];
        for (i, merge) in traces.g_ntt_merges.iter().enumerate() {
            let (g_ntt_interaction_trace, g_ntt_interaction_claim) =
                ntt::InteractionClaim::gen_interaction_trace(
                    merge,
                    &lookup_elements.rc,
                    &lookup_elements.g_ntt,
                    &if i == 0 {
                        InputLookupElements::Butterfly(lookup_elements.g_ntt_butterfly.clone())
                    } else {
                        InputLookupElements::NTT(lookup_elements.g_ntt.clone())
                    },
                    &lookup_elements.roots,
                );
            g_ntt_interaction_traces.push(g_ntt_interaction_trace);
            g_ntt_interaction_claims.push(g_ntt_interaction_claim);
        }
        // Generate interaction traces and claims for modular multiplication operations
        // This establishes lookup relations for the multiplication component
        let (mul_interaction_trace, mul_interaction_claim) =
            mul::InteractionClaim::gen_interaction_trace(&traces.mul, lookup_elements);
        // Initialize vectors to collect interaction traces and claims for INTT merge stages
        // Each stage processes different input lookup elements based on the stage index
        let mut intt_interaction_traces = vec![];
        let mut intt_interaction_claims = vec![];

        // Generate interaction traces and claims for each INTT merge stage
        // The first stage uses multiplication lookup elements, subsequent stages use INTT output
        for (i, split) in traces.intt_merges.iter().enumerate() {
            let (intt_interaction_trace, intt_interaction_claim) =
                intt::InteractionClaim::gen_interaction_trace(
                    split,
                    &lookup_elements.rc,
                    &if i == 0 {
                        INTTInputLookupElements::Mul(lookup_elements.mul.clone())
                    } else {
                        INTTInputLookupElements::INTTOutput(lookup_elements.intt.clone())
                    },
                    &lookup_elements.intt,
                    &lookup_elements.inv_roots,
                );
            intt_interaction_traces.push(intt_interaction_trace);
            intt_interaction_claims.push(intt_interaction_claim);
        }
        // Generate interaction traces and claims for the inverse butterfly operation
        // This is the final stage of the INTT that converts back to coefficient form
        let (ibutterfly_interaction_trace, ibutterfly_interaction_claim) =
            intt::ibutterfly::InteractionClaim::gen_interaction_trace(
                &traces.ibutterfly,
                lookup_elements,
            );
        // Generate interaction traces and claims for modular subtraction operations
        // This establishes lookup relations for the subtraction component
        let (sub_interaction_trace, sub_interaction_claim) =
            sub::InteractionClaim::gen_interaction_trace(&traces.sub, lookup_elements);

        // Generate interaction traces and claims for Euclidean norm computation
        // This validates that signature polynomials meet size requirements
        let (euclidean_norm_interaction_trace, euclidean_norm_interaction_claim) =
            euclidean_norm::InteractionClaim::gen_interaction_trace(
                &traces.euclidean_norm,
                lookup_elements,
            );
        // Generate interaction traces and claims for half-range checking (0 to Q/2)
        // This validates that values are within the lower half of the field range
        let (half_range_check_interaction_trace, half_range_check_interaction_claim) =
            range_check::InteractionClaim::gen_interaction_trace::<{ Q / 2 }>(
                &traces.half_range_check,
                &lookup_elements.half_range_check,
            );
        // Generate interaction traces and claims for low signature bound checking
        // This validates the lower 14 bits of signature polynomial norms
        let (low_sig_bound_check_interaction_trace, low_sig_bound_check_interaction_claim) =
            range_check::InteractionClaim::gen_interaction_trace::<LOW_SIG_BOUND>(
                &traces.low_sig_bound_check,
                &lookup_elements.low_sig_bound_check,
            );

        // Generate interaction traces and claims for high signature bound checking
        // This validates the upper bits of signature polynomial norms
        let (high_sig_bound_check_interaction_trace, high_sig_bound_check_interaction_claim) =
            range_check::InteractionClaim::gen_interaction_trace::<HIGH_SIG_BOUND>(
                &traces.high_sig_bound_check,
                &lookup_elements.high_sig_bound_check,
            );
        let (range_check_interaction_trace, range_check_interaction_claim) =
            range_check::InteractionClaim::gen_interaction_trace::<Q>(
                &traces.range_check,
                &lookup_elements.rc,
            );
        let mut roots_interaction_traces = vec![];
        let mut roots_interaction_claims = vec![];
        for (stage, stage_root_trace) in traces.roots.iter().enumerate() {
            let (roots_interaction_trace, roots_interaction_claim) =
                roots::preprocessed::InteractionClaim::gen_interaction_trace(
                    stage_root_trace,
                    &lookup_elements.roots,
                    stage + 2,
                );
            roots_interaction_traces.push(roots_interaction_trace);
            roots_interaction_claims.push(roots_interaction_claim);
        }
        let mut inv_roots_interaction_traces = vec![];
        let mut inv_roots_interaction_claims = vec![];
        for (stage, stage_root_trace) in traces.inv_roots.iter().enumerate() {
            let (inv_roots_interaction_trace, inv_roots_interaction_claim) =
                roots::inv_preprocessed::InteractionClaim::gen_interaction_trace(
                    stage_root_trace,
                    &lookup_elements.inv_roots,
                    POLY_LOG_SIZE as usize - stage,
                );
            inv_roots_interaction_traces.push(inv_roots_interaction_trace);
            inv_roots_interaction_claims.push(inv_roots_interaction_claim);
        }
        (
            chain!(
                f_ntt_butterfly_interaction_trace,
                f_ntt_interaction_traces
                    .iter()
                    .flatten()
                    .cloned()
                    .collect_vec(),
                g_ntt_butterfly_interaction_trace,
                g_ntt_interaction_traces
                    .iter()
                    .flatten()
                    .cloned()
                    .collect_vec(),
                mul_interaction_trace,
                intt_interaction_traces
                    .iter()
                    .flatten()
                    .cloned()
                    .collect_vec(),
                ibutterfly_interaction_trace,
                sub_interaction_trace,
                euclidean_norm_interaction_trace,
                half_range_check_interaction_trace,
                low_sig_bound_check_interaction_trace,
                high_sig_bound_check_interaction_trace,
                range_check_interaction_trace,
                roots_interaction_traces
                    .iter()
                    .flatten()
                    .cloned()
                    .collect_vec(),
                inv_roots_interaction_traces
                    .iter()
                    .flatten()
                    .cloned()
                    .collect_vec(),
            )
            .collect_vec(),
            Self {
                f_ntt_butterfly: f_ntt_butterfly_interaction_claim,
                f_ntt_merges: f_ntt_interaction_claims,
                g_ntt_butterfly: g_ntt_butterfly_interaction_claim,
                g_ntt_merges: g_ntt_interaction_claims,
                mul: mul_interaction_claim,
                intt_merges: intt_interaction_claims,
                ibutterfly: ibutterfly_interaction_claim,
                sub: sub_interaction_claim,
                euclidean_norm: euclidean_norm_interaction_claim,
                half_range_check: half_range_check_interaction_claim,
                low_sig_bound_check: low_sig_bound_check_interaction_claim,
                high_sig_bound_check: high_sig_bound_check_interaction_claim,
                range_check: range_check_interaction_claim,
                roots: roots_interaction_claims,
                inv_roots: inv_roots_interaction_claims,
            },
        )
    }
}
