use crate::{
    HIGH_SIG_BOUND, LOW_SIG_BOUND,
    big_air::relation::LookupElements,
    ntts::{intt, ntt},
    polys::{euclidean_norm, mul, sub},
    zq::{Q, range_check},
};
use itertools::{Itertools, chain};
use stwo::{
    core::{
        channel::Channel,
        fields::{m31::M31, qm31::QM31},
    },
    prover::{
        backend::simd::SimdBackend,
        poly::{BitReversedOrder, circle::CircleEvaluation},
    },
};

#[derive(Debug, Clone)]
pub struct BigInteractionClaim {
    /// Interaction claim for butterfly operations
    pub f_ntt_butterfly: ntt::butterfly::InteractionClaim,
    /// Interaction claim for NTT operations
    pub f_ntt: ntt::InteractionClaim,
    /// Interaction claim for butterfly operations
    pub g_ntt_butterfly: ntt::butterfly::InteractionClaim,
    /// Interaction claim for NTT operations
    pub g_ntt: ntt::InteractionClaim,
    /// Interaction claim for multiplication operations
    pub mul: mul::InteractionClaim,
    /// Interaction claim for INTT operations
    pub intt: intt::InteractionClaim,
    /// Interaction claim for subtraction operations
    pub sub: sub::InteractionClaim,
    /// Interaction claim for euclidean norm operations
    pub euclidean_norm: euclidean_norm::InteractionClaim,
    /// Interaction claim for half range checking
    pub half_range_check: range_check::InteractionClaim,
    /// Interaction claim for signature bound checking
    pub low_sig_bound_check: range_check::InteractionClaim,
    /// Interaction claim for signature bound checking
    pub high_sig_bound_check: range_check::InteractionClaim,
    /// Interaction claim for range checking
    pub range_check: range_check::InteractionClaim,
}

impl BigInteractionClaim {
    /// Mixes all interaction claims into the Fiat-Shamir channel.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.f_ntt_butterfly.mix_into(channel);
        self.f_ntt.mix_into(channel);
        self.g_ntt_butterfly.mix_into(channel);
        self.g_ntt.mix_into(channel);
        self.mul.mix_into(channel);
        self.intt.mix_into(channel);
        self.sub.mix_into(channel);
        self.euclidean_norm.mix_into(channel);
        self.half_range_check.mix_into(channel);
        self.low_sig_bound_check.mix_into(channel);
        self.high_sig_bound_check.mix_into(channel);
        self.range_check.mix_into(channel);
    }

    /// Computes the total claimed sum across all interactions.
    ///
    /// This sum should equal zero for a valid proof, ensuring that
    /// all lookup relations are properly satisfied.
    pub fn claimed_sum(&self) -> QM31 {
        self.f_ntt_butterfly.claimed_sum
            + self.f_ntt.claimed_sum
            + self.g_ntt_butterfly.claimed_sum
            + self.g_ntt.claimed_sum
            + self.mul.claimed_sum
            + self.intt.claimed_sum
            + self.sub.claimed_sum
            + self.euclidean_norm.claimed_sum
            + self.half_range_check.claimed_sum
            + self.low_sig_bound_check.claimed_sum
            + self.high_sig_bound_check.claimed_sum
            + self.range_check.claimed_sum
    }

    /// Generates interaction traces for all components.
    ///
    /// # Parameters
    ///
    /// - `lookup_elements`: The lookup elements for range checking
    /// - `add_trace`: Trace columns from modular addition
    /// - `mul_trace`: Trace columns from modular multiplication
    /// - `sub_trace`: Trace columns from modular subtraction
    /// - `range_check_trace`: Trace column from range checking
    ///
    /// # Returns
    ///
    /// Returns the combined interaction traces and the big interaction claim.
    pub fn gen_interaction_trace(
        lookup_elements: &LookupElements,
        f_ntt_butterfly_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        f_ntt_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        g_ntt_butterfly_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        g_ntt_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        mul_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        intt_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        sub_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        euclidean_norm_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        half_range_check_trace: &CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
        low_sig_bound_check_trace: &CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
        high_sig_bound_check_trace: &CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
        range_check_trace: &CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
    ) -> (
        Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Self,
    ) {
        let (f_ntt_butterfly_interaction_trace, f_ntt_butterfly_interaction_claim) =
            ntt::butterfly::InteractionClaim::gen_interaction_trace(
                f_ntt_butterfly_trace,
                &lookup_elements.rc,
                &lookup_elements.f_ntt_butterfly,
            );
        let (f_ntt_interaction_trace, f_ntt_interaction_claim) =
            ntt::InteractionClaim::gen_interaction_trace(
                f_ntt_trace,
                &lookup_elements.rc,
                &lookup_elements.f_ntt,
                &lookup_elements.f_ntt_butterfly,
            );

        let (g_ntt_butterfly_interaction_trace, g_ntt_butterfly_interaction_claim) =
            ntt::butterfly::InteractionClaim::gen_interaction_trace(
                g_ntt_butterfly_trace,
                &lookup_elements.rc,
                &lookup_elements.g_ntt_butterfly,
            );
        let (g_ntt_interaction_trace, g_ntt_interaction_claim) =
            ntt::InteractionClaim::gen_interaction_trace(
                g_ntt_trace,
                &lookup_elements.rc,
                &lookup_elements.g_ntt,
                &lookup_elements.g_ntt_butterfly,
            );
        let (mul_interaction_trace, mul_interaction_claim) =
            mul::InteractionClaim::gen_interaction_trace(
                mul_trace,
                &lookup_elements.rc,
                &lookup_elements.f_ntt,
                &lookup_elements.g_ntt,
                &lookup_elements.mul,
            );
        let (intt_interaction_trace, intt_interaction_claim) =
            intt::InteractionClaim::gen_interaction_trace(
                intt_trace,
                &lookup_elements.rc,
                &lookup_elements.mul,
                &lookup_elements.intt,
            );
        let (sub_interaction_trace, sub_interaction_claim) =
            sub::InteractionClaim::gen_interaction_trace(
                sub_trace,
                &lookup_elements.rc,
                &lookup_elements.intt,
                &lookup_elements.sub,
            );
        let (euclidean_norm_interaction_trace, euclidean_norm_interaction_claim) =
            euclidean_norm::InteractionClaim::gen_interaction_trace(
                euclidean_norm_trace,
                &lookup_elements.half_range_check,
                &lookup_elements.sub,
                &lookup_elements.low_sig_bound_check,
                &lookup_elements.high_sig_bound_check,
            );
        let (half_range_check_interaction_trace, half_range_check_interaction_claim) =
            range_check::InteractionClaim::gen_interaction_trace::<{ Q / 2 }>(
                half_range_check_trace,
                &lookup_elements.half_range_check,
            );
        let (low_sig_bound_check_interaction_trace, low_sig_bound_check_interaction_claim) =
            range_check::InteractionClaim::gen_interaction_trace::<LOW_SIG_BOUND>(
                low_sig_bound_check_trace,
                &lookup_elements.low_sig_bound_check,
            );
        let (high_sig_bound_check_interaction_trace, high_sig_bound_check_interaction_claim) =
            range_check::InteractionClaim::gen_interaction_trace::<HIGH_SIG_BOUND>(
                high_sig_bound_check_trace,
                &lookup_elements.high_sig_bound_check,
            );
        let (range_check_interaction_trace, range_check_interaction_claim) =
            range_check::InteractionClaim::gen_interaction_trace::<Q>(
                range_check_trace,
                &lookup_elements.rc,
            );
        (
            chain!(
                f_ntt_butterfly_interaction_trace,
                f_ntt_interaction_trace,
                g_ntt_butterfly_interaction_trace,
                g_ntt_interaction_trace,
                mul_interaction_trace,
                intt_interaction_trace,
                sub_interaction_trace,
                euclidean_norm_interaction_trace,
                half_range_check_interaction_trace,
                low_sig_bound_check_interaction_trace,
                high_sig_bound_check_interaction_trace,
                range_check_interaction_trace,
            )
            .collect_vec(),
            Self {
                f_ntt_butterfly: f_ntt_butterfly_interaction_claim,
                f_ntt: f_ntt_interaction_claim,
                g_ntt_butterfly: g_ntt_butterfly_interaction_claim,
                g_ntt: g_ntt_interaction_claim,
                mul: mul_interaction_claim,
                intt: intt_interaction_claim,
                sub: sub_interaction_claim,
                euclidean_norm: euclidean_norm_interaction_claim,
                half_range_check: half_range_check_interaction_claim,
                low_sig_bound_check: low_sig_bound_check_interaction_claim,
                high_sig_bound_check: high_sig_bound_check_interaction_claim,
                range_check: range_check_interaction_claim,
            },
        )
    }
}
