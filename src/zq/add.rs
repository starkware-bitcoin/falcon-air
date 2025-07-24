//! # Modular Addition Component
//!
//! This module implements STARK proof components for modular addition operations.
//!
//! The modular addition operation computes (a + b) mod q, where q = 12289.
//! The operation is decomposed into:
//! - a + b = quotient * q + remainder
//! - where remainder ∈ [0, q)
//!
//! The component generates traces for the operands (a, b), quotient, and remainder,
//! and enforces the constraint that the remainder is within the valid range.

use num_traits::One;
use rand::Rng;
use stwo::{
    core::{
        ColumnVec,
        channel::Channel,
        fields::{m31::M31, qm31::SecureField},
        pcs::TreeVec,
        poly::circle::CanonicCoset,
    },
    prover::{
        backend::simd::{SimdBackend, column::BaseColumn, m31::LOG_N_LANES, qm31::PackedQM31},
        poly::{BitReversedOrder, circle::CircleEvaluation},
    },
};
use stwo_constraint_framework::{
    FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
};

use crate::zq::Q;

// This is a helper function for the prover to generate the trace for the add component
#[derive(Debug, Clone)]
pub struct Claim {
    /// The log base 2 of the trace size
    pub log_size: u32,
}

impl Claim {
    /// Returns the log sizes for the traces.
    ///
    /// [preprocessed_trace, trace, interaction_trace]
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let trace_log_sizes = vec![self.log_size];
        TreeVec::new(vec![vec![], trace_log_sizes, vec![]])
    }

    /// Mixes the claim parameters into the Fiat-Shamir channel.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    /// Generates the trace for modular addition operations.
    ///
    /// # Returns
    ///
    /// Returns a tuple containing:
    /// - A vector of 4 trace columns: [a, b, quotient, remainder]
    /// - A vector of remainder values for range checking
    ///
    /// # Algorithm
    ///
    /// 1. Generates random operands a, b ∈ [0, q)
    /// 2. Computes quotient = ⌊(a + b) / q⌋
    /// 3. Computes remainder = (a + b) mod q
    /// 4. Creates trace columns for all values
    pub fn gen_trace(
        &self,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Vec<M31>,
    ) {
        let mut rng = rand::thread_rng();
        let a = (0..(1 << self.log_size))
            .map(|_| rng.gen_range(0..Q))
            .collect::<Vec<_>>();
        let b = (0..(1 << self.log_size))
            .map(|_| rng.gen_range(0..Q))
            .collect::<Vec<_>>();
        let quotient = a
            .iter()
            .zip(b.iter())
            .map(|(a, b)| M31::from_u32_unchecked((a + b) / Q))
            .collect::<Vec<_>>();
        let remainder = a
            .iter()
            .zip(b.iter())
            .map(|(a, b)| M31::from_u32_unchecked((a + b) % Q))
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

/// Evaluation component for modular addition constraints.
///
/// This struct implements the constraint evaluation logic for modular addition,
/// ensuring that the arithmetic relationship holds and the remainder is properly range-checked.
#[derive(Debug, Clone)]
pub struct Eval {
    /// The claim parameters
    pub claim: Claim,
    /// Lookup elements for range checking
    pub lookup_elements: super::range_check::LookupElements,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.claim.log_size + 1
    }

    /// Evaluates the modular addition constraints.
    ///
    /// # Constraints
    ///
    /// 1. **Arithmetic constraint**: a + b = quotient * Q + remainder
    /// 2. **Range check**: remainder ∈ [0, Q) via lookup table
    fn evaluate<E: stwo_constraint_framework::EvalAtRow>(&self, mut eval: E) -> E {
        // Extract trace values
        let a = eval.next_trace_mask();
        let b = eval.next_trace_mask();
        let quotient = eval.next_trace_mask();
        let remainder = eval.next_trace_mask();

        // Constraint: a + b = quotient * Q + remainder
        eval.add_constraint(
            a + b - quotient * E::F::from(M31::from_u32_unchecked(Q)) - remainder.clone(),
        );
        // Now we need to check that the remainder is in the range [0, Q)
        // We do this by using the range check we defined. Here we increment the multiplicity of
        // this value (remainder) by 1 because we want to range check it and the logup sum has to be exactly 0
        // So here we increment and in the range_check we decrements
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            E::EF::one(),
            &[remainder],
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Interaction claim for modular addition.
///
/// Contains the claimed sum for the interaction between the addition component
/// and the range check component.
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

    /// Generates the interaction trace for modular addition.
    ///
    /// This method creates the interaction trace that connects the addition component
    /// with the range check component through the lookup protocol.
    ///
    /// # Parameters
    ///
    /// - `trace`: The trace columns from the addition component
    /// - `lookup_elements`: The lookup elements for range checking
    ///
    /// # Returns
    ///
    /// Returns the interaction trace and the interaction claim.
    pub fn gen_interaction_trace(
        trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        lookup_elements: &super::range_check::LookupElements,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        InteractionClaim,
    ) {
        let log_size = trace[0].domain.log_size();
        let mut logup_gen = LogupTraceGenerator::new(log_size);
        let mut col_gen = logup_gen.new_col();

        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            // Get the remainder value from the trace (column 3)
            let result_packed = trace[3].data[vec_row];

            // Create the denominator using the lookup elements
            let denom: PackedQM31 = lookup_elements.combine(&[result_packed]);

            // The numerator is 1 (we want to check that remainder is in the range)
            let numerator = PackedQM31::one();

            col_gen.write_frac(vec_row, numerator, denom);
        }
        col_gen.finalize_col();

        let (interaction_trace, claimed_sum) = logup_gen.finalize_last();
        (interaction_trace, InteractionClaim { claimed_sum })
    }
}

/// Type alias for the modular addition component.
pub type Component = FrameworkComponent<Eval>;
