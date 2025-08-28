//! # Modular Subtraction Component
//!
//! This module implements STARK proof components for modular subtraction operations
//! over the finite field Z_q where q = 12289.
//!
//! # Mathematical Foundation
//!
//! The modular subtraction operation computes (a - b) mod q, where a, b ∈ [0, q).
//! The operation is decomposed into:
//!
//! a - b = borrow * q + remainder
//!
//! where:
//! - remainder ∈ [0, q) (the result of modular subtraction)
//! - borrow ∈ {0, 1} (indicates if a < b, requiring field addition)
//!
//! # Algorithm Details
//!
//! The subtraction is implemented using the following logic:
//! - If a ≥ b: borrow = 0, remainder = a - b
//! - If a < b: borrow = 1, remainder = a + q - b
//!
//! This ensures that the result is always in the range [0, q) and properly
//! handles the modular arithmetic requirements.
//!
//! # Trace Structure
//!
//! The component generates traces with the following columns:
//! - Column 0: First operand a
//! - Column 1: Second operand b  
//! - Column 2: Borrow bit (0 or 1)
//! - Column 3: Remainder (result of modular subtraction)
//!
//! # Range Checking
//!
//! The component enforces constraints that ensure:
//! - All operands are within [0, q)
//! - The remainder is within [0, q)
//! - The borrow bit is either 0 or 1
//! - The modular arithmetic relationship holds: a - b = borrow * q + remainder
//!
//! # Usage
//!
//! This component is used in polynomial arithmetic operations where modular
//! subtraction is required, such as in the Falcon signature scheme for
//! coefficient-wise polynomial operations.

use num_traits::One;
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

use crate::{
    big_air::relation::{IButterflyLookupElements, RCLookupElements, SubLookupElements},
    zq::{Q, sub::SubMod},
};

/// Claim parameters for the modular subtraction circuit.
///
/// Contains the logarithmic size of the trace, which determines the number of
/// subtraction operations that can be proven.
#[derive(Debug, Clone)]
pub struct Claim {
    /// The log base 2 of the trace size (determines number of operations: 2^log_size)
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

    /// Mixes the claim parameters into the Fiat-Shamir channel for non-interactive proof generation.
    ///
    /// This ensures the proof is bound to the specific trace size used and prevents
    /// parameter substitution attacks.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    /// Generates the trace for the modular subtraction component.
    ///
    /// Creates a trace representing modular subtraction operations for pairs of operands.
    /// Each operation is decomposed into borrow and remainder parts.
    ///
    /// # Algorithm
    ///
    /// For each pair (a, b):
    /// - borrow = (a < b) ? 1 : 0
    /// - remainder = a + borrow * Q - b
    ///
    /// # Parameters
    ///
    /// - `a`: First operand array with values in [0, Q)
    /// - `b`: Second operand array with values in [0, Q)
    ///
    /// # Returns
    ///
    /// Returns a tuple containing:
    /// - `ColumnVec<CircleEvaluation<...>>`: The computation trace columns (a, b, borrow, remainder)
    /// - `Vec<M31>`: Remainder values for range checking
    pub fn gen_trace(
        &self,
        a: &[u32],
        b: &[u32],
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Vec<M31>,
    ) {
        assert!(a.len() == b.len(), "a and b must have the same length");
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

/// Component used in the framework for modular subtraction evaluation.
#[derive(Debug, Clone)]
pub struct Eval {
    /// The claim parameters
    pub claim: Claim,
    /// Lookup elements for range checking
    pub rc_lookup_elements: RCLookupElements,
    /// Lookup elements for INTT operations
    pub ibutterfly_lookup_elements: IButterflyLookupElements,
    /// Lookup elements for subtraction operations
    pub sub_lookup_elements: SubLookupElements,
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

        SubMod::new(a, b.clone(), borrow, remainder.clone())
            .evaluate(&self.rc_lookup_elements, &mut eval);

        eval.add_to_relation(RelationEntry::new(
            &self.sub_lookup_elements,
            -E::EF::one(),
            &[remainder],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.ibutterfly_lookup_elements,
            E::EF::one(),
            &[b],
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
    /// Creates the interaction trace that connects the subtraction component
    /// with the range check component through the lookup protocol.
    pub fn gen_interaction_trace(
        trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        rc_lookup_elements: &RCLookupElements,
        ibutterfly_lookup_elements: &IButterflyLookupElements,
        sub_lookup_elements: &SubLookupElements,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        InteractionClaim,
    ) {
        let log_size = trace[0].domain.log_size();
        let mut logup_gen = LogupTraceGenerator::new(log_size);

        // Range check for remainder values
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            // Get the remainder value from the trace (column 3)
            let result_packed = trace[3].data[vec_row];

            // Create the denominator using the lookup elements
            let denom: PackedQM31 = rc_lookup_elements.combine(&[result_packed]);

            // The numerator is 1 (we want to check that remainder is in the range)
            let numerator = PackedQM31::one();

            col_gen.write_frac(vec_row, numerator, denom);
        }
        col_gen.finalize_col();

        // Subtraction lookup
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            // Get the remainder value from the trace (column 3)
            let result_packed = trace[3].data[vec_row];

            // Create the denominator using the lookup elements
            let denom: PackedQM31 = sub_lookup_elements.combine(&[result_packed]);

            // The numerator is -1 (we're producing a value)
            let numerator = -PackedQM31::one();

            col_gen.write_frac(vec_row, numerator, denom);
        }
        col_gen.finalize_col();

        // INTT lookup for operand b
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let result_packed = trace[1].data[vec_row];

            // Create the denominator using the lookup elements
            let denom: PackedQM31 = ibutterfly_lookup_elements.combine(&[result_packed]);

            // The numerator is 1 (we're consuming a value)
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
