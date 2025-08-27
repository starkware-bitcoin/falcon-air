//! Number Theoretic Transform (NTT) implementation for polynomial evaluation.
//!
//! This module implements a complete NTT circuit that performs polynomial evaluation
//! over a finite field using modular arithmetic operations. The NTT is a generalization
//! of the Fast Fourier Transform (FFT) that works over finite fields.
//!
//! The NTT algorithm works by:
//! 1. **Initial Butterfly Phase**: Performs the first level of NTT computation
//! 2. **Recursive Merging Phase**: Combines intermediate results using roots of unity
//! 3. **Final Evaluation**: Produces the polynomial in evaluation form
//!
//! Key characteristics:
//! - Uses roots of unity for polynomial evaluation
//! - Input is in coefficient form, output is in evaluation form
//! - Each arithmetic operation is decomposed for modular arithmetic verification
//! - Includes range checking to ensure values remain within field bounds
//!
//! The NTT is the forward transform that converts from coefficient form to evaluation form,
//! which is the inverse of the INTT (Inverse Number Theoretic Transform).

use num_traits::One;
use stwo::{
    core::{
        ColumnVec,
        channel::Channel,
        fields::{m31::M31, qm31::SecureField},
        poly::circle::CanonicCoset,
        utils::bit_reverse,
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
    POLY_SIZE,
    big_air::relation::{IButterflyLookupElements, INTTLookupElements, RCLookupElements},
    ntts::{I2, SQ1},
    zq::{Q, add::AddMod, inverses::INVERSES_MOD_Q, mul::MulMod, sub::SubMod},
};

#[derive(Debug, Clone)]
pub struct Claim {
    /// The log base 2 of the trace size
    pub log_size: u32,
}

impl Claim {
    /// Mixes the claim parameters into the Fiat-Shamir channel for non-interactive proof generation.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    /// Generates the complete NTT computation trace.
    ///
    /// This function creates a trace that represents the entire NTT computation,
    /// including the initial butterfly phase and the recursive merging phase. Each
    /// arithmetic operation is decomposed into quotient and remainder parts for
    /// modular arithmetic verification.
    ///
    /// The NTT algorithm:
    /// 1. Starts with polynomial in coefficient form [1, 2, ..., n]
    /// 2. Applies bit-reversal permutation for in-place computation
    /// 3. Performs initial butterfly operations using SQ1
    /// 4. Recursively merges results using roots of unity
    /// 5. Produces polynomial in evaluation form
    ///
    /// # Returns
    ///
    /// Returns a tuple containing:
    /// - `ColumnVec<CircleEvaluation<...>>`: The main computation trace columns
    /// - `Vec<Vec<M31>>`: Remainder values organized by operation type (MUL, ADD, SUB)
    #[allow(clippy::type_complexity)]
    pub fn gen_trace(
        &self,
        polys: &[Vec<u32>],
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Vec<Vec<M31>>,
        Vec<u32>,
    ) {
        let mut butterflied_poly = Vec::with_capacity(POLY_SIZE);
        let mut f_ntt_0_col = vec![];
        let mut f_ntt_1_col = vec![];
        let mut f_ntt_0_plus_f_ntt_1_quotient_col = vec![];
        let mut f_ntt_0_plus_f_ntt_1_remainder_col = vec![];
        let mut i2_times_f_ntt_0_plus_f_ntt_1_quotient_col = vec![];
        let mut i2_times_f_ntt_0_plus_f_ntt_1_remainder_col = vec![];
        let mut f_ntt_0_minus_f_ntt_1_quotient_col = vec![];
        let mut f_ntt_0_minus_f_ntt_1_remainder_col = vec![];
        let mut i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_quotient_col = vec![];
        let mut i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder_col = vec![];

        // Phase 1: Initial Butterfly Operations
        //
        // This phase implements the first level of NTT computation using the butterfly pattern:
        //   f_ntt[0] = (f[0] + sqr1 * f[1]) % q
        //   f_ntt[1] = (f[0] - sqr1 * f[1]) % q
        //
        // Each butterfly operation requires 8 trace columns to represent:
        // - f0, f1: Input coefficients
        // - f1 * sqr1 / Q, f1 * sqr1 % Q: Multiplication decomposition
        // - f0 + f1 * sqr1 / Q, f0 + f1 * sqr1 % Q: Addition decomposition
        // - f0 - f1 * sqr1 / Q, f0 - f1 * sqr1 % Q: Subtraction decomposition
        polys.iter().for_each(|poly| {
            debug_assert_eq!(poly.len(), 2);
            let f_ntt_0 = poly[0];
            let f_ntt_1 = poly[1];
            f_ntt_0_col.push(f_ntt_0);
            f_ntt_1_col.push(f_ntt_1);

            // Step 1: Add the final two coefficients
            // f_ntt[0] + f_ntt[1]
            let f_ntt_0_plus_f_ntt_1_quotient = (f_ntt_0 + f_ntt_1) / Q;
            let f_ntt_0_plus_f_ntt_1_remainder = (f_ntt_0 + f_ntt_1) % Q;

            f_ntt_0_plus_f_ntt_1_quotient_col.push(f_ntt_0_plus_f_ntt_1_quotient);
            f_ntt_0_plus_f_ntt_1_remainder_col.push(f_ntt_0_plus_f_ntt_1_remainder);

            // Step 2: Apply scaling factor I2 to the sum
            // I2 * (f_ntt[0] + f_ntt[1]) where I2 = 1/2
            let i2_times_f_ntt_0_plus_f_ntt_1_quotient = (I2 * f_ntt_0_plus_f_ntt_1_remainder) / Q;
            let i2_times_f_ntt_0_plus_f_ntt_1_remainder = (I2 * f_ntt_0_plus_f_ntt_1_remainder) % Q;

            i2_times_f_ntt_0_plus_f_ntt_1_quotient_col.push(i2_times_f_ntt_0_plus_f_ntt_1_quotient);
            i2_times_f_ntt_0_plus_f_ntt_1_remainder_col
                .push(i2_times_f_ntt_0_plus_f_ntt_1_remainder);
            butterflied_poly.push(i2_times_f_ntt_0_plus_f_ntt_1_remainder);

            // Step 3: Subtract the final two coefficients
            // f_ntt[0] - f_ntt[1] (with borrow handling)
            let f_ntt_0_minus_f_ntt_1_quotient = (f_ntt_0 < f_ntt_1) as u32;
            let f_ntt_0_minus_f_ntt_1_remainder =
                (f_ntt_0 + f_ntt_0_minus_f_ntt_1_quotient * Q - f_ntt_1) % Q;

            f_ntt_0_minus_f_ntt_1_quotient_col.push(f_ntt_0_minus_f_ntt_1_quotient);
            f_ntt_0_minus_f_ntt_1_remainder_col.push(f_ntt_0_minus_f_ntt_1_remainder);

            // Step 4: Apply scaling factor I2 and inverse of SQ1 to the difference
            // I2 * inv_sq1 * (f_ntt[0] - f_ntt[1]) where inv_sq1 = 1/sq1
            let i2_times_inv_sq1 = (I2 * INVERSES_MOD_Q[SQ1 as usize]) % Q;

            // I2 * inv_sq1 * (f_ntt[0] - f_ntt[1])
            let i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_quotient =
                (i2_times_inv_sq1 * f_ntt_0_minus_f_ntt_1_remainder) / Q;
            let i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder =
                (i2_times_inv_sq1 * f_ntt_0_minus_f_ntt_1_remainder) % Q;

            i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_quotient_col
                .push(i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_quotient);
            i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder_col
                .push(i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder);
            butterflied_poly.push(i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder);
        });

        let remainders = vec![
            f_ntt_0_plus_f_ntt_1_remainder_col
                .clone()
                .into_iter()
                .map(M31)
                .collect(),
            i2_times_f_ntt_0_plus_f_ntt_1_remainder_col
                .clone()
                .into_iter()
                .map(M31)
                .collect(),
            f_ntt_0_minus_f_ntt_1_remainder_col
                .clone()
                .into_iter()
                .map(M31)
                .collect(),
            i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder_col
                .clone()
                .into_iter()
                .map(M31)
                .collect(),
        ];

        let domain = CanonicCoset::new(self.log_size).circle_domain();
        bit_reverse(&mut butterflied_poly);
        (
            [
                f_ntt_0_col,
                f_ntt_1_col,
                f_ntt_0_plus_f_ntt_1_quotient_col,
                f_ntt_0_plus_f_ntt_1_remainder_col,
                i2_times_f_ntt_0_plus_f_ntt_1_quotient_col,
                i2_times_f_ntt_0_plus_f_ntt_1_remainder_col,
                f_ntt_0_minus_f_ntt_1_quotient_col,
                f_ntt_0_minus_f_ntt_1_remainder_col,
                i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_quotient_col,
                i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder_col,
            ]
            .into_iter()
            .map(|val| {
                CircleEvaluation::<SimdBackend, _, BitReversedOrder>::new(
                    domain,
                    BaseColumn::from_iter(val.into_iter().map(M31)),
                )
            })
            .collect::<Vec<_>>(),
            remainders,
            butterflied_poly,
        )
    }
}

/// Evaluation component for the NTT circuit.
///
/// This struct contains the necessary data to evaluate the NTT constraints
/// during proof generation. It includes claim parameters and lookup elements
/// for range checking of modular arithmetic operations.
///
/// The evaluation component ensures that all NTT operations (multiplication,
/// addition, subtraction) are correctly verified through range checking
/// and modular arithmetic constraints.
#[derive(Debug, Clone)]
pub struct Eval {
    /// The claim parameters defining the NTT computation
    pub claim: Claim,
    /// Lookup elements for range checking modular arithmetic operations
    pub rc_lookup_elements: RCLookupElements,
    /// Lookup elements for NTT operations
    pub intt_output_lookup_elements: INTTLookupElements,
    /// Lookup elements for butterfly operations
    pub ibutterfly_output_lookup_elements: IButterflyLookupElements,
}

impl FrameworkEval for Eval {
    /// Returns the log size of the trace.
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }

    /// Returns the maximum constraint degree bound for the NTT circuit.
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.claim.log_size + 1
    }

    /// Evaluates the NTT constraints during proof generation.
    ///
    /// This function generates the constraint evaluation trace that matches
    /// the computation trace generated by `gen_trace`. It ensures that all
    /// modular arithmetic operations are correctly verified through range checking.
    ///
    /// The evaluation process mirrors the NTT computation:
    /// 1. Evaluates initial butterfly operations using SQ1
    /// 2. Evaluates recursive merging operations using roots of unity
    /// 3. Verifies all modular arithmetic operations through range checking
    fn evaluate<E: stwo_constraint_framework::EvalAtRow>(&self, mut eval: E) -> E {
        let f_ntt_0 = eval.next_trace_mask();
        let f_ntt_1 = eval.next_trace_mask();

        eval.add_to_relation(RelationEntry::new(
            &self.intt_output_lookup_elements,
            E::EF::one(),
            &[f_ntt_0.clone()],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.intt_output_lookup_elements,
            E::EF::one(),
            &[f_ntt_1.clone()],
        ));

        let f_ntt_0_plus_f_ntt_1_quotient = eval.next_trace_mask();
        let f_ntt_0_plus_f_ntt_1_remainder = eval.next_trace_mask();
        AddMod::<E>::new(
            f_ntt_0.clone(),
            f_ntt_1.clone(),
            f_ntt_0_plus_f_ntt_1_quotient,
            f_ntt_0_plus_f_ntt_1_remainder.clone(),
        )
        .evaluate(&self.rc_lookup_elements, &mut eval);

        // (i2 * (f_ntt[0] + f_ntt[1])) % q
        let i2_times_f_ntt_0_plus_f_ntt_1_quotient = eval.next_trace_mask();
        let i2_times_f_ntt_0_plus_f_ntt_1_remainder = eval.next_trace_mask();
        MulMod::<E>::new(
            E::F::from(M31(I2)),
            f_ntt_0_plus_f_ntt_1_remainder.clone(),
            i2_times_f_ntt_0_plus_f_ntt_1_quotient,
            i2_times_f_ntt_0_plus_f_ntt_1_remainder.clone(),
        )
        .evaluate(&self.rc_lookup_elements, &mut eval);

        // f_ntt[0] - f_ntt[1]
        let f_ntt_0_minus_f_ntt_1_quotient = eval.next_trace_mask();
        let f_ntt_0_minus_f_ntt_1_remainder = eval.next_trace_mask();
        SubMod::<E>::new(
            f_ntt_0.clone(),
            f_ntt_1.clone(),
            f_ntt_0_minus_f_ntt_1_quotient,
            f_ntt_0_minus_f_ntt_1_remainder.clone(),
        )
        .evaluate(&self.rc_lookup_elements, &mut eval);

        let i2_times_inv_sq1 = (I2 * INVERSES_MOD_Q[SQ1 as usize]) % Q;

        // (i2 * inv_mod_q[sqr1] * (f_ntt[0] - f_ntt[1])) % q
        let i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_quotient = eval.next_trace_mask();
        let i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder = eval.next_trace_mask();
        MulMod::<E>::new(
            f_ntt_0_minus_f_ntt_1_remainder.clone(),
            E::F::from(M31(i2_times_inv_sq1)),
            i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_quotient,
            i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder.clone(),
        )
        .evaluate(&self.rc_lookup_elements, &mut eval);
        eval.add_to_relation(RelationEntry::new(
            &self.ibutterfly_output_lookup_elements,
            -E::EF::one(),
            &[i2_times_f_ntt_0_plus_f_ntt_1_remainder],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.ibutterfly_output_lookup_elements,
            -E::EF::one(),
            &[i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder],
        ));

        eval.finalize_logup();
        eval
    }
}

/// Claim for the interaction trace that connects NTT computation with range checking.
///
/// This struct contains the claimed sum that links the NTT computation trace
/// with the range checking component through the lookup protocol. The interaction
/// ensures that all modular arithmetic operations produce results within the
/// expected range.
///
/// The interaction trace verifies that all remainders from modular operations
/// (multiplication, addition, subtraction) are properly bounded within the field.
#[derive(Debug, Clone)]
pub struct InteractionClaim {
    /// The claimed sum for the interaction between NTT and range checking
    pub claimed_sum: SecureField,
}

impl InteractionClaim {
    /// Mixes the interaction claim into the Fiat-Shamir channel.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }

    /// Generates the interaction trace that connects NTT computation with range checking.
    ///
    /// This method creates an interaction trace that ensures all modular arithmetic
    /// operations in the NTT computation produce results within the expected range [0, Q).
    /// It uses the lookup protocol to verify that remainders from modular operations
    /// are properly bounded.
    ///
    /// The interaction trace covers:
    /// - Remainder values from the initial butterfly phase (columns 3, 5, 7)
    /// - Remainder values from the recursive merging phase (every other column after the initial phase)
    /// - Final NTT output values for linking with INTT input
    ///
    /// # Parameters
    ///
    /// - `trace`: The main NTT computation trace columns
    /// - `rc_lookup_elements`: The lookup elements for range checking
    /// - `ntt_lookup_elements`: The lookup elements for NTT operations
    ///
    /// # Returns
    ///
    /// Returns the interaction trace and the interaction claim.
    pub fn gen_interaction_trace(
        trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        rc_lookup_elements: &RCLookupElements,
        intt_lookup_elements: &INTTLookupElements,
        ibutterfly_output_lookup_elements: &IButterflyLookupElements,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        InteractionClaim,
    ) {
        let log_size = trace[0].domain.log_size();
        let mut logup_gen = LogupTraceGenerator::new(log_size);
        // NTT output linking column moved to the end to match evaluation order
        //
        // Phase 1: Interaction trace for the initial butterfly phase
        // Check remainder values from columns 3, 5, 7 of each 8-column group
        // These columns contain the remainder values from modular arithmetic operations
        for col in [0, 1] {
            let mut col_gen = logup_gen.new_col();
            for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                // Each butterfly operation uses 8 columns, so we access the remainder columns
                let result_packed = trace[col].data[vec_row];

                // Create the denominator using the lookup elements for range checking
                let denom: PackedQM31 = intt_lookup_elements.combine(&[result_packed]);
                col_gen.write_frac(vec_row, PackedQM31::one(), denom);
            }
            col_gen.finalize_col();
        }

        for col in [3, 5, 7, 9] {
            let mut col_gen = logup_gen.new_col();
            for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                // Each butterfly operation uses 8 columns, so we access the remainder columns
                let result_packed = trace[col].data[vec_row];

                // Create the denominator using the lookup elements for range checking
                let denom: PackedQM31 = rc_lookup_elements.combine(&[result_packed]);
                col_gen.write_frac(vec_row, PackedQM31::one(), denom);
            }
            col_gen.finalize_col();
        }

        for col in [5, 9] {
            let mut col_gen = logup_gen.new_col();
            for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                // Each butterfly operation uses 8 columns, so we access the remainder columns
                let result_packed = trace[col].data[vec_row];

                // Create the denominator using the lookup elements for range checking
                let denom: PackedQM31 = ibutterfly_output_lookup_elements.combine(&[result_packed]);
                col_gen.write_frac(vec_row, -PackedQM31::one(), denom);
            }
            col_gen.finalize_col();
        }
        let (interaction_trace, claimed_sum) = logup_gen.finalize_last();

        (interaction_trace, InteractionClaim { claimed_sum })
    }
}

/// Type alias for the NTT circuit component.
///
/// This represents the complete NTT circuit that can be used within
/// the constraint framework for proof generation and verification.
///
/// The NTT component performs polynomial evaluation from coefficient form
/// to evaluation form using modular arithmetic operations with range checking.
/// It supports polynomial sizes up to 1024 coefficients and uses the field Z_q
/// where q = 12289.
pub type Component = FrameworkComponent<Eval>;
