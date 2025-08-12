//! # Modular Multiplication Component
//!
//! This module implements STARK proof components for modular multiplication operations.
//!
//! The modular multiplication operation computes (a * b) mod q, where q = 12289.
//! The operation is decomposed into:
//! - a * b = quotient * q + remainder
//! - where remainder ∈ [0, q)
//!
//! The component generates traces for the operands (a, b), quotient, and remainder,
//! and enforces the constraint that the remainder is within the valid range.

use num_traits::One;
use stwo::{
    core::{
        ColumnVec,
        channel::Channel,
        fields::{m31::M31, qm31::SecureField},
        poly::circle::CanonicCoset,
    },
    prover::{
        backend::simd::{SimdBackend, column::BaseColumn, m31::LOG_N_LANES, qm31::PackedQM31},
        poly::{BitReversedOrder, circle::CircleEvaluation},
    },
};
use stwo_constraint_framework::{
    FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry, relation,
};

use crate::{
    ntts::{mul, ntt},
    zq::{Q, mul::MulMod, range_check},
};

relation!(LookupElements, 1);

// This is a helper function for the prover to generate the trace for the mul component
#[derive(Debug, Clone)]
pub struct Claim {
    /// The log base 2 of the trace size
    pub log_size: u32,
}

impl Claim {
    /// Mixes the claim parameters into the Fiat-Shamir channel.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    /// Generates the trace for the mul component
    /// Generates 2 random numbers and creates a trace for the mul component
    /// returns the columns in this order: a, b, quotient, remainder
    pub fn gen_trace(
        &self,
        a: &[u32],
        b: &[u32],
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Vec<M31>,
    ) {
        assert!(a.len() == b.len(), "a and b must have the same length");
        let quotient = a
            .iter()
            .zip(b.iter())
            .map(|(a, b)| M31::from_u32_unchecked((a * b) / Q))
            .collect::<Vec<_>>();
        let remainder = a
            .iter()
            .zip(b.iter())
            .map(|(a, b)| M31::from_u32_unchecked((a * b) % Q))
            .collect::<Vec<_>>();
        let a = a
            .iter()
            .map(|a| M31::from_u32_unchecked(*a))
            .collect::<Vec<_>>();
        let b = b
            .iter()
            .map(|b| M31::from_u32_unchecked(*b))
            .collect::<Vec<_>>();
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        (
            [a, b, quotient, remainder.clone()]
                .into_iter()
                .map(|col| {
                    CircleEvaluation::<SimdBackend, _, BitReversedOrder>::new(
                        domain,
                        BaseColumn::from_iter(col),
                    )
                })
                .collect::<Vec<_>>(),
            remainder,
        )
    }
}

// Actual component that is used in the framework
#[derive(Debug, Clone)]
pub struct Eval {
    /// The claim parameters
    pub claim: Claim,
    /// Lookup elements for range checking
    pub rc_lookup_elements: range_check::LookupElements,
    /// Lookup elements for NTT operations
    pub f_ntt_lookup_elements: ntt::LookupElements,
    /// Lookup elements for NTT operations
    pub g_ntt_lookup_elements: ntt::LookupElements,
    /// Lookup elements for mul operations
    pub mul_lookup_elements: mul::LookupElements,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.claim.log_size + 1
    }

    fn evaluate<E: stwo_constraint_framework::EvalAtRow>(&self, mut eval: E) -> E {
        // Those values were filled during the trace generation
        let a = eval.next_trace_mask();
        let b = eval.next_trace_mask();
        let quotient = eval.next_trace_mask();
        let remainder = eval.next_trace_mask();
        MulMod::new(a.clone(), b.clone(), quotient, remainder.clone())
            .evaluate(&self.rc_lookup_elements, &mut eval);
        eval.add_to_relation(RelationEntry::new(
            &self.mul_lookup_elements,
            E::EF::one(),
            &[remainder],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.f_ntt_lookup_elements,
            -E::EF::one(),
            &[a],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.g_ntt_lookup_elements,
            -E::EF::one(),
            &[b],
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}

#[derive(Debug, Clone)]
pub struct InteractionClaim {
    /// The claimed sum for the interaction
    pub claimed_sum: SecureField,
}

impl InteractionClaim {
    /// Mixes the interaction claim into the Fiat-Shamir channel.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }

    /// Generates the interaction trace for modular multiplication.
    ///
    /// This method creates the interaction trace that connects the multiplication component
    /// with the range check component through the lookup protocol.
    ///
    /// # Parameters
    ///
    /// - `trace`: The trace columns from the multiplication component
    /// - `lookup_elements`: The lookup elements for range checking
    ///
    /// # Returns
    ///
    /// Returns the interaction trace and the interaction claim.
    pub fn gen_interaction_trace(
        trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        rc_lookup_elements: &range_check::LookupElements,
        mul_lookup_elements: &mul::LookupElements,
        f_ntt_lookup_elements: &ntt::LookupElements,
        g_ntt_lookup_elements: &ntt::LookupElements,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        InteractionClaim,
    ) {
        let log_size = trace[0].domain.log_size();
        let mut logup_gen = LogupTraceGenerator::new(log_size);

        // link range_check and intt intput as mul output
        for i in 0..2 {
            let mut col_gen = logup_gen.new_col();
            for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                // Get the remainder value from the trace (column 3)
                let result_packed = trace[3].data[vec_row];

                // Create the denominator using the lookup elements
                let (numerator, denom): (PackedQM31, PackedQM31) = if i == 0 {
                    (
                        -PackedQM31::one(),
                        rc_lookup_elements.combine(&[result_packed]),
                    )
                } else {
                    (
                        PackedQM31::one(),
                        mul_lookup_elements.combine(&[result_packed]),
                    )
                };

                col_gen.write_frac(vec_row, numerator, denom);
            }
            col_gen.finalize_col();
        }

        // link both ntt ouputs as mul input
        for i in 0..2 {
            let mut col_gen = logup_gen.new_col();
            for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                // Get the remainder value from the trace (column 3)
                let result_packed = trace[i].data[vec_row];

                // Create the denominator using the lookup elements
                let denom: PackedQM31 = if i == 0 {
                    f_ntt_lookup_elements.combine(&[result_packed])
                } else {
                    g_ntt_lookup_elements.combine(&[result_packed])
                };

                let numerator = -PackedQM31::one();

                col_gen.write_frac(vec_row, numerator, denom);
            }
            col_gen.finalize_col();
        }

        let (interaction_trace, claimed_sum) = logup_gen.finalize_last();
        (interaction_trace, InteractionClaim { claimed_sum })
    }
}

/// Type alias for the modular multiplication component.
pub type Component = FrameworkComponent<Eval>;
