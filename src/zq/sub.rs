//! # Modular Subtraction Component
//!
//! This module implements STARK proof components for modular subtraction operations.
//!
//! The modular subtraction operation computes (a - b) mod q, where q = 12289.
//! The operation is decomposed into:
//! - a - b = remainder (mod q)
//! - where remainder ∈ [0, q)
//!
//! The component generates traces for the operands (a, b) and remainder,
//! and enforces the constraint that the remainder is within the valid range.

use num_traits::One;
use rand::Rng;
use stwo::{
    core::{
        ColumnVec,
        channel::Channel,
        fields::{
            m31::M31,
            qm31::{SECURE_EXTENSION_DEGREE, SecureField},
        },
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

// This is a helper function for the prover to generate the trace for the sub component
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
        TreeVec::new(vec![
            vec![],
            trace_log_sizes,
            vec![self.log_size; SECURE_EXTENSION_DEGREE],
        ])
    }

    /// Mixes the claim parameters into the Fiat-Shamir channel.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    /// Generates the trace for the sub component
    /// Generates 2 random numbers and creates a trace for the sub component
    /// returns the columns in this order: a, b, borrow, remainder
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
        let borrow = a
            .iter()
            .zip(b.iter())
            .map(|(a, b)| M31::from_u32_unchecked((a < b) as u32))
            .collect::<Vec<_>>();
        let remainder = a
            .iter()
            .zip(b.iter())
            .map(|(a, b)| M31::from_u32_unchecked(a + (a < b) as u32 * Q - b))
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
            [a, b, borrow, remainder.clone()]
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
    pub lookup_elements: super::range_check::LookupElements,
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
        let borrow = eval.next_trace_mask();
        let remainder = eval.next_trace_mask();

        // this is the constraint for add_mod_12289
        // a - b = remainder + borrow * Q
        eval.add_constraint(
            a - b - remainder.clone() + borrow.clone() * E::F::from(M31::from_u32_unchecked(Q)),
        );
        eval.add_constraint(borrow.clone() * (borrow - E::F::one()));

        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            E::EF::one(),
            &[remainder],
        ));
        eval.finalize_logup();
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

    /// Generates the interaction trace for modular subtraction.
    ///
    /// This method creates the interaction trace that connects the subtraction component
    /// with the range check component through the lookup protocol.
    ///
    /// # Parameters
    ///
    /// - `trace`: The trace columns from the subtraction component
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
            // Get the remainder value from the trace (column 2)
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

/// Type alias for the modular subtraction component.
pub type Component = FrameworkComponent<Eval>;
