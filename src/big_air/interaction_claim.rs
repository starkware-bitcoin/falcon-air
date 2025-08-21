use crate::{
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
    /// Interaction claim for NTT operations
    pub f_ntt: ntt::InteractionClaim,
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
    /// Interaction claim for range checking
    pub range_check: range_check::InteractionClaim,
}

impl BigInteractionClaim {
    /// Mixes all interaction claims into the Fiat-Shamir channel.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.f_ntt.mix_into(channel);
        self.g_ntt.mix_into(channel);
        self.mul.mix_into(channel);
        self.intt.mix_into(channel);
        self.sub.mix_into(channel);
        self.euclidean_norm.mix_into(channel);
        self.range_check.mix_into(channel);
    }

    /// Computes the total claimed sum across all interactions.
    ///
    /// This sum should equal zero for a valid proof, ensuring that
    /// all lookup relations are properly satisfied.
    pub fn claimed_sum(&self) -> QM31 {
        self.f_ntt.claimed_sum
            + self.g_ntt.claimed_sum
            + self.mul.claimed_sum
            + self.intt.claimed_sum
            + self.sub.claimed_sum
            + self.euclidean_norm.claimed_sum
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
        f_ntt_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        g_ntt_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        mul_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        intt_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        sub_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        euclidean_norm_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        range_check_trace: &CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
    ) -> (
        Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Self,
    ) {
        let (f_ntt_interaction_trace, f_ntt_interaction_claim) =
            ntt::InteractionClaim::gen_interaction_trace(
                f_ntt_trace,
                &lookup_elements.rc,
                &lookup_elements.f_ntt,
            );
        let (g_ntt_interaction_trace, g_ntt_interaction_claim) =
            ntt::InteractionClaim::gen_interaction_trace(
                g_ntt_trace,
                &lookup_elements.rc,
                &lookup_elements.g_ntt,
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
                &lookup_elements.rc,
                &lookup_elements.sub,
            );
        let (range_check_interaction_trace, range_check_interaction_claim) =
            range_check::InteractionClaim::gen_interaction_trace::<Q>(
                range_check_trace,
                &lookup_elements.rc,
            );
        (
            chain!(
                f_ntt_interaction_trace,
                g_ntt_interaction_trace,
                mul_interaction_trace,
                intt_interaction_trace,
                sub_interaction_trace,
                euclidean_norm_interaction_trace,
                range_check_interaction_trace,
            )
            .collect_vec(),
            Self {
                f_ntt: f_ntt_interaction_claim,
                g_ntt: g_ntt_interaction_claim,
                mul: mul_interaction_claim,
                intt: intt_interaction_claim,
                sub: sub_interaction_claim,
                euclidean_norm: euclidean_norm_interaction_claim,
                range_check: range_check_interaction_claim,
            },
        )
    }
}
