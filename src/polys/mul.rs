//! # Modular Multiplication Component
//!
//! This module implements STARK proof components for modular multiplication operations
//! over the finite field Z_q where q = 12289.
//!
//! # Mathematical Foundation
//!
//! The modular multiplication operation computes (a * b) mod q, where a, b ∈ [0, q).
//! The operation is decomposed into:
//!
//! a * b = quotient * q + remainder
//!
//! where:
//! - remainder ∈ [0, q) (the result of modular multiplication)
//! - quotient = ⌊(a * b) / q⌋ (the integer division result)
//!
//! # Algorithm Details
//!
//! The multiplication is implemented using standard integer arithmetic:
//! - quotient = (a * b) / q (integer division)
//! - remainder = (a * b) % q (modulo operation)
//!
//! This decomposition ensures that the result is always in the range [0, q) and
//! provides efficient verification through range checking of the remainder.
//!
//! # Trace Structure
//!
//! The component generates traces with the following columns:
//! - Column 0: First operand a
//! - Column 1: Second operand b
//! - Column 2: Quotient (integer division result)
//! - Column 3: Remainder (result of modular multiplication)
//!
//! # Range Checking
//!
//! The component enforces constraints that ensure:
//! - All operands are within [0, q)
//! - The remainder is within [0, q)
//! - The quotient is non-negative
//! - The modular arithmetic relationship holds: a * b = quotient * q + remainder
//!
//! # Usage
//!
//! This component is used in polynomial arithmetic operations where modular
//! multiplication is required, such as in the Falcon signature scheme for
//! polynomial evaluation multiplication and NTT computations.

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
    big_air::relation::{MulLookupElements, NTTLookupElements, RCLookupElements},
    zq::{Q, mul::MulMod},
};

/// Claim parameters for the modular multiplication circuit.
///
/// This struct defines the parameters needed to generate and verify modular multiplication proofs
/// for polynomial evaluations. The claim contains the logarithmic size of the trace, which determines
/// the number of multiplication operations that can be proven.
///
/// # Parameters
///
/// - `log_size`: The log base 2 of the trace size (e.g., 10 for 1024 operations)
///   This determines the number of multiplication operations and the size of the computation trace.
///
/// # Example
///
/// For a trace with 1024 multiplication operations on polynomial evaluations:
/// ```rust
/// let claim = Claim { log_size: 10 };
/// ```
#[derive(Debug, Clone)]
pub struct Claim {
    /// The log base 2 of the trace size
    ///
    /// This value determines:
    /// - Number of multiplication operations: 2^log_size
    /// - Trace size: 2^log_size rows
    /// - Memory requirements for proof generation
    pub log_size: u32,
}

impl Claim {
    /// Returns the log sizes for the traces used in the modular multiplication circuit.
    ///
    /// This method defines the structure of the proof system by specifying
    /// the logarithmic sizes of different trace components. The multiplication circuit
    /// uses three types of traces:
    ///
    /// # Trace Structure
    ///
    /// 1. **Preprocessed Trace**: Empty (no preprocessing required for multiplication)
    ///    - Contains no columns as multiplication doesn't require precomputed lookup tables
    ///
    /// 2. **Main Computation Trace**: Contains the multiplication computation steps
    ///    - Size: 2^log_size rows
    ///    - Contains columns for operands, quotient, and remainder
    ///
    /// 3. **Interaction Trace**: Empty (no interaction trace required)
    ///    - Range checking is handled through the main trace constraints
    ///
    /// # Returns
    ///
    /// Returns a tree structure containing the log sizes for each trace component:
    /// - `preprocessed_trace`: Empty vector (no preprocessing)
    /// - `trace`: Vector with single element `[log_size]` (main computation)
    /// - `interaction_trace`: Empty vector (no interaction trace)
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let trace_log_sizes = vec![self.log_size];
        TreeVec::new(vec![vec![], trace_log_sizes, vec![]])
    }

    /// Mixes the claim parameters into the Fiat-Shamir channel for non-interactive proof generation.
    ///
    /// This method incorporates the multiplication claim parameters into the Fiat-Shamir challenge
    /// generation process, ensuring that the proof is bound to the specific parameters
    /// used in the multiplication computation.
    ///
    /// # Parameters Mixed
    ///
    /// - `log_size`: The logarithmic size of the trace (determines number of operations)
    ///   This parameter affects the complexity and structure of the multiplication computation.
    ///
    /// # Security Properties
    ///
    /// By mixing the claim parameters into the channel:
    /// - The proof is bound to the specific trace size used
    /// - Prevents parameter substitution attacks
    /// - Ensures proof soundness for the claimed parameters
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    /// Generates the trace for the modular multiplication component.
    ///
    /// This function creates a trace that represents modular multiplication operations
    /// for pairs of polynomial evaluation operands. Each multiplication operation is decomposed
    /// into quotient and remainder parts for modular arithmetic verification.
    ///
    /// # Algorithm Details
    ///
    /// For each pair of polynomial evaluation operands (a, b), the function computes:
    /// - quotient = (a * b) / Q (integer division)
    /// - remainder = (a * b) % Q (modulo operation)
    ///
    /// This decomposition ensures that the result is always in the range [0, Q) and
    /// provides efficient verification through range checking of the remainder.
    ///
    /// # Parameters
    ///
    /// - `a`: First polynomial evaluation operand array with values in [0, Q)
    /// - `b`: Second polynomial evaluation operand array with values in [0, Q)
    ///   Both arrays must have the same length.
    ///
    /// # Returns
    ///
    /// Returns a tuple containing:
    /// - `ColumnVec<CircleEvaluation<...>>`: The computation trace columns
    ///   Columns are in order: a, b, quotient, remainder
    /// - `Vec<M31>`: Remainder values for range checking
    ///
    /// # Trace Structure
    ///
    /// The generated trace contains 4 columns per operation:
    /// - Column 0: First polynomial evaluation operand a
    /// - Column 1: Second polynomial evaluation operand b
    /// - Column 2: Quotient (integer division result)
    /// - Column 3: Remainder (result of modular multiplication)
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
    pub rc_lookup_elements: RCLookupElements,
    /// Lookup elements for f_ntt
    pub f_ntt_lookup_elements: NTTLookupElements,
    /// Lookup elements for g_ntt
    pub g_ntt_lookup_elements: NTTLookupElements,
    /// Lookup elements for multiplication
    pub mul_lookup_elements: MulLookupElements,
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
        let q = eval.next_trace_mask();
        let r = eval.next_trace_mask();
        MulMod::new(a.clone(), b.clone(), q, r.clone())
            .evaluate(&self.rc_lookup_elements, &mut eval);
        eval.add_to_relation(RelationEntry::new(
            &self.f_ntt_lookup_elements,
            E::EF::one(),
            &[a],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.g_ntt_lookup_elements,
            E::EF::one(),
            &[b],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.mul_lookup_elements,
            -E::EF::one(),
            &[r],
            // &[E::F::zero()],
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
        rc_lookup_elements: &RCLookupElements,
        f_ntt_lookup_elements: &NTTLookupElements,
        g_ntt_lookup_elements: &NTTLookupElements,
        mul_lookup_elements: &MulLookupElements,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        InteractionClaim,
    ) {
        let log_size = trace[0].domain.log_size();
        let mut logup_gen = LogupTraceGenerator::new(log_size);
        // Range check
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

        // f_ntt
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            // Get the remainder value from the trace (column 3)
            let result_packed = trace[0].data[vec_row];

            // Create the denominator using the lookup elements
            let denom: PackedQM31 = f_ntt_lookup_elements.combine(&[result_packed]);

            // The numerator is 1 (we want to check that remainder is in the range)
            let numerator = PackedQM31::one();

            col_gen.write_frac(vec_row, numerator, denom);
        }
        col_gen.finalize_col();
        // g_ntt
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            // Get the remainder value from the trace (column 3)
            let result_packed = trace[1].data[vec_row];

            // Create the denominator using the lookup elements
            let denom: PackedQM31 = g_ntt_lookup_elements.combine(&[result_packed]);

            // The numerator is 1 (we want to check that remainder is in the range)
            let numerator = PackedQM31::one();

            col_gen.write_frac(vec_row, numerator, denom);
        }
        col_gen.finalize_col();

        // mul output
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            // Get the remainder value from the trace (column 3)
            let result_packed = trace[3].data[vec_row];

            // Create the denominator using the lookup elements
            let denom: PackedQM31 = mul_lookup_elements.combine(&[result_packed]);

            // The numerator is 1 (we want to check that remainder is in the range)
            let numerator = -PackedQM31::one();

            col_gen.write_frac(vec_row, numerator, denom);
        }
        col_gen.finalize_col();

        let (interaction_trace, claimed_sum) = logup_gen.finalize_last();
        (interaction_trace, InteractionClaim { claimed_sum })
    }
}

/// Type alias for the modular multiplication component.
pub type Component = FrameworkComponent<Eval>;
