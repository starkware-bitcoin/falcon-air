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

use num_traits::{One, Zero};
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
        utils::{bit_reverse, bit_reverse_index},
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
    POLY_LOG_SIZE, POLY_SIZE,
    big_air::relation::{NTTLookupElements, RCLookupElements},
    ntts::{
        ROOTS, SQ1,
        ntt::merge::{Merge, MergeNTT},
    },
    zq::{Q, add::AddMod, mul::MulMod, sub::SubMod},
};

pub mod butterfly;
pub mod merge;

#[derive(Debug, Clone)]
pub struct Claim {
    /// The log base 2 of the trace size
    pub log_size: u32,
}

impl Claim {
    /// Returns the log sizes for the traces.
    ///
    /// Returns a tree structure containing the log sizes for:
    /// - `preprocessed_trace`: Empty (no preprocessing needed)
    /// - `trace`: Main NTT computation trace
    /// - `interaction_trace`: Range checking interaction trace
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let trace_log_sizes = vec![self.log_size];
        let interaction_log_sizes = vec![self.log_size; SECURE_EXTENSION_DEGREE];
        TreeVec::new(vec![vec![], trace_log_sizes, interaction_log_sizes])
    }

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
        poly: &[u32; POLY_SIZE],
        is_first_iteration: bool,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Vec<Vec<M31>>,
        Vec<u32>,
    ) {
        // Initialize the input polynomial with values [1, 2, ..., POLY_SIZE]
        let mut poly = poly.to_vec();

        // Apply bit-reversal permutation to prepare for in-place NTT computation
        // This ensures the polynomial is in the correct order for the butterfly operations
        bit_reverse(&mut poly);
        let bit_reversed_0 = bit_reverse_index(0, self.log_size);
        let mut remainders_counter = 0;

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
        let trace = poly
            .chunks(2)
            .map(|chunk| {
                let f0 = chunk[0];
                let f1 = chunk[1];

                // Step 1: Multiply f1 by SQ1 (first root of unity) and decompose
                // f1 * SQ1 = quotient * Q + remainder
                let f1_times_sq1_quotient = (f1 * SQ1) / Q;
                let f1_times_sq1_remainder = (f1 * SQ1) % Q;
                remainders_counter += 1;
                // Step 2: Add f0 to the remainder and decompose
                // f0 + f1 * SQ1 = quotient * Q + remainder
                let f0_plus_f1_times_sq1_quotient = (f0 + f1_times_sq1_remainder) / Q;
                let f0_plus_f1_times_sq1_remainder = (f0 + f1_times_sq1_remainder) % Q;
                remainders_counter += 1;
                // Step 3: Subtract the remainder from f0 and decompose
                // f0 - f1 * SQ1 = quotient * Q + remainder (with borrow handling)
                let f0_minus_f1_times_sq1_quotient = (f0 < f1_times_sq1_remainder) as u32;
                let f0_minus_f1_times_sq1_remainder =
                    (f0 + f0_minus_f1_times_sq1_quotient * Q - f1_times_sq1_remainder) % Q;
                remainders_counter += 1;
                [
                    f0,
                    f1,
                    f1_times_sq1_quotient,
                    f1_times_sq1_remainder,
                    f0_plus_f1_times_sq1_quotient,
                    f0_plus_f1_times_sq1_remainder,
                    f0_minus_f1_times_sq1_quotient,
                    f0_minus_f1_times_sq1_remainder,
                ]
            })
            .collect::<Vec<_>>();
        let final_trace = trace
            .iter()
            .flat_map(|coeff_row| {
                coeff_row.iter().map(|value| {
                    let mut col = vec![M31::zero(); 1 << self.log_size];
                    col[bit_reversed_0] = M31(*value);
                    col
                })
            })
            .collect::<Vec<_>>();
        let mut remainders = vec![];
        for poly_coeff in 0..(1 << (POLY_LOG_SIZE - 1)) {
            for col in [3, 5, 7] {
                remainders.push(final_trace[poly_coeff * 8 + col].clone());
            }
        }
        // Prepare data structures for the merging phase
        let mut polys = vec![vec![]; POLY_LOG_SIZE as usize];

        // Extract the output coefficients from the initial butterfly phase
        // These become the input for the merging phase
        for [_, _, _, _, _, left, _, right] in trace.iter() {
            polys[0].push(vec![*left, *right]);
        }

        let mut trace = vec![];

        // Phase 2: Recursive Merging Operations
        //
        // This phase implements the remaining NTT levels using recursive merging:
        //   f_ntt[2 * i + 0] = (f0_ntt[i] + w[2 * i] * f1_ntt[i]) % q
        //   f_ntt[2 * i + 1] = (f0_ntt[i] - w[2 * i] * f1_ntt[i]) % q
        //
        // Each merging operation requires 6 new trace columns:
        // - f1_ntt[i] * w[2 * i] / Q, f1_ntt[i] * w[2 * i] % Q: Multiplication with root
        // - f0_ntt[i] + f1_ntt[i] * w[2 * i] / Q, f0_ntt[i] + f1_ntt[i] * w[2 * i] % Q: Addition
        // - f0_ntt[i] - f1_ntt[i] * w[2 * i] / Q, f0_ntt[i] - f1_ntt[i] * w[2 * i] % Q: Subtraction
        //
        // The roots of unity (w[2 * i]) are precomputed and stored in ROOTS[i][2 * j]
        // Each level doubles the polynomial size until we reach the final evaluation form
        for i in 1..POLY_LOG_SIZE as usize {
            for coeffs in polys[i - 1].clone().chunks_exact(2) {
                let left = &coeffs[0]; // f0_ntt polynomial
                let right = &coeffs[1]; // f1_ntt polynomial

                // Process each coefficient pair from the two polynomials
                let mut merged_poly = vec![];
                for (j, (coeff_left, coeff_right)) in left.iter().zip(right.iter()).enumerate() {
                    // Get the appropriate root of unity for this position
                    // Each level uses different roots from the precomputed ROOTS array
                    let root = ROOTS[i][2 * j];

                    // Step 1: Multiply f1_ntt coefficient by root of unity
                    // f1_ntt[i] * w[2 * i] = quotient * Q + remainder
                    let root_times_f1_quotient = (*coeff_right * root) / Q;
                    let root_times_f1_remainder = (*coeff_right * root) % Q;
                    remainders_counter += 1;
                    trace.push(root_times_f1_quotient);
                    trace.push(root_times_f1_remainder);

                    // Step 2: Add f0_ntt coefficient to the multiplied result
                    // f0_ntt[i] + f1_ntt[i] * w[2 * i] = quotient * Q + remainder
                    let f0_plus_root_times_f1_quotient =
                        (*coeff_left + root_times_f1_remainder) / Q;
                    let f0_plus_root_times_f1_remainder =
                        (*coeff_left + root_times_f1_remainder) % Q;
                    remainders_counter += 1;
                    trace.push(f0_plus_root_times_f1_quotient);
                    trace.push(f0_plus_root_times_f1_remainder);

                    // Step 3: Subtract the multiplied result from f0_ntt coefficient
                    // f0_ntt[i] - f1_ntt[i] * w[2 * i] = quotient * Q + remainder (with borrow handling)
                    let f0_minus_root_times_f1_borrow =
                        (*coeff_left < root_times_f1_remainder) as u32;
                    let f0_minus_root_times_f1_remainder =
                        (*coeff_left + f0_minus_root_times_f1_borrow * Q - root_times_f1_remainder)
                            % Q;
                    trace.push(f0_minus_root_times_f1_borrow);
                    trace.push(f0_minus_root_times_f1_remainder);
                    remainders_counter += 1;
                    // Store the results for the next recursive level
                    merged_poly.push(f0_plus_root_times_f1_remainder);
                    merged_poly.push(f0_minus_root_times_f1_remainder);
                }
                polys[i].push(merged_poly);
            }
        }
        let trace = trace.into_iter().map(|val| {
            let mut col = vec![M31::zero(); 1 << self.log_size];
            col[bit_reversed_0] = M31(val);
            col
        });
        let remainders = remainders
            .into_iter()
            .chain(trace.clone().skip(1).step_by(2));

        // Convert the trace values to circle evaluations for the proof system
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        let mut is_first = vec![M31(0); 1 << self.log_size];
        is_first[bit_reversed_0] = M31(is_first_iteration as u32);

        (
            std::iter::once(is_first)
                .chain(final_trace)
                .chain(trace)
                .chain(polys.last().unwrap()[0].iter().map(|x| {
                    let mut col = vec![M31::zero(); 1 << self.log_size];
                    col[bit_reversed_0] = M31(*x);
                    col
                }))
                .map(|val| {
                    CircleEvaluation::<SimdBackend, _, BitReversedOrder>::new(
                        domain,
                        BaseColumn::from_iter(val),
                    )
                })
                .collect::<Vec<_>>(),
            remainders.collect(),
            polys.last().unwrap()[0].clone(),
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
    pub ntt_lookup_elements: NTTLookupElements,
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
        let sq1 = E::F::from(M31::from_u32_unchecked(SQ1));
        let mut base_f_ntt = Vec::with_capacity(POLY_SIZE);
        let is_first = eval.next_trace_mask();

        // Phase 1: Evaluate initial butterfly operations
        // This corresponds to the first phase of trace generation
        for _ in 0..1 << (POLY_LOG_SIZE - 1) {
            let f0 = eval.next_trace_mask();
            let f1 = eval.next_trace_mask();
            let f1_times_sq1_quotient = eval.next_trace_mask();
            let f1_times_sq1_remainder = eval.next_trace_mask();

            let f0_plus_f1_times_sq1_quotient = eval.next_trace_mask();
            let f0_plus_f1_times_sq1_remainder = eval.next_trace_mask();

            let f0_minus_f1_times_sq1_quotient = eval.next_trace_mask();
            let f0_minus_f1_times_sq1_remainder = eval.next_trace_mask();

            MulMod::new(
                f1,
                sq1.clone(),
                f1_times_sq1_quotient.clone(),
                f1_times_sq1_remainder.clone(),
            )
            .evaluate(&self.rc_lookup_elements, &mut eval);
            AddMod::new(
                f0.clone(),
                f1_times_sq1_remainder.clone(),
                f0_plus_f1_times_sq1_quotient,
                f0_plus_f1_times_sq1_remainder.clone(),
            )
            .evaluate(&self.rc_lookup_elements, &mut eval);
            SubMod::new(
                f0,
                f1_times_sq1_remainder,
                f0_minus_f1_times_sq1_quotient,
                f0_minus_f1_times_sq1_remainder.clone(),
            )
            .evaluate(&self.rc_lookup_elements, &mut eval);
            base_f_ntt.push(vec![
                f0_plus_f1_times_sq1_remainder,
                f0_minus_f1_times_sq1_remainder,
            ]);
        }
        // Phase 2: Evaluate merging operations
        // Initialize the polynomial array for all NTT levels
        let mut poly: Vec<Vec<Vec<E::F>>> = vec![vec![]; POLY_LOG_SIZE as usize];
        poly[0] = base_f_ntt;

        // Perform POLY_LOG_SIZE - 1 merging iterations to complete the NTT
        // Each iteration doubles the polynomial size until we reach the final result
        for i in 1..POLY_LOG_SIZE as usize {
            // Process pairs of polynomials from the previous iteration
            for coeffs in poly[i - 1].clone().chunks_exact(2) {
                let mut merges = MergeNTT::default();
                let left = &coeffs[0]; // f0_ntt polynomial
                let right = &coeffs[1]; // f1_ntt polynomial

                // Process each coefficient pair using the appropriate root of unity
                for (j, (coeff_left, coeff_right)) in left.iter().zip(right.iter()).enumerate() {
                    let root = ROOTS[i][2 * j];

                    // Step 1: Multiply f1_ntt coefficient by root of unity
                    let root_times_f1 = MulMod::<E>::new(
                        coeff_right.clone(),
                        E::F::from(M31(root)),
                        eval.next_trace_mask(),
                        eval.next_trace_mask(),
                    );
                    // Step 2: Add f0_ntt coefficient to the multiplied result
                    let f0_plus_root_times_f1 = AddMod::<E>::new(
                        coeff_left.clone(),
                        root_times_f1.r.clone(),
                        eval.next_trace_mask(),
                        eval.next_trace_mask(),
                    );
                    // Step 3: Subtract the multiplied result from f0_ntt coefficient
                    let f0_minus_root_times_f1 = SubMod::<E>::new(
                        coeff_left.clone(),
                        root_times_f1.r.clone(),
                        eval.next_trace_mask(),
                        eval.next_trace_mask(),
                    );
                    // Create a merge operation combining all three steps
                    let merge =
                        Merge::new(root_times_f1, f0_plus_root_times_f1, f0_minus_root_times_f1);
                    merges.push(merge);
                }

                // Evaluate the merge operations and store the result
                let merged_poly = MergeNTT::evaluate(merges, &self.rc_lookup_elements, &mut eval);
                poly[i].push(merged_poly);
            }
        }

        poly.last().unwrap()[0].clone().into_iter().for_each(|x| {
            let output_col = eval.next_trace_mask();
            eval.add_constraint(x - output_col.clone());
            eval.add_to_relation(RelationEntry::new(
                &self.ntt_lookup_elements,
                -E::EF::from(is_first.clone()),
                &[output_col],
            ));
        });

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
        ntt_lookup_elements: &NTTLookupElements,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        InteractionClaim,
    ) {
        let log_size = trace[0].domain.log_size();
        let mut logup_gen = LogupTraceGenerator::new(log_size);
        let is_first = trace[0].clone();
        let trace = trace.iter().skip(1).collect::<Vec<_>>();
        // NTT output linking column moved to the end to match evaluation order
        //
        // Phase 1: Interaction trace for the initial butterfly phase
        // Check remainder values from columns 3, 5, 7 of each 8-column group
        // These columns contain the remainder values from modular arithmetic operations
        let first_ntt_size = 1 << (POLY_LOG_SIZE - 1);
        for operation_element_index in 0..first_ntt_size {
            for col in [3, 5, 7] {
                let mut col_gen = logup_gen.new_col();
                for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                    // Each butterfly operation uses 8 columns, so we access the remainder columns
                    let result_packed = trace[operation_element_index * 8 + col].data[vec_row];

                    // Create the denominator using the lookup elements for range checking
                    let denom: PackedQM31 = rc_lookup_elements.combine(&[result_packed]);
                    col_gen.write_frac(vec_row, PackedQM31::one(), denom);
                }
                col_gen.finalize_col();
            }
        }

        // Phase 2: Interaction trace for the merging phase
        // Check remainder values from every other column in the merging phase
        // These columns contain the remainder values from modular arithmetic operations in the recursive merging
        let offset = first_ntt_size * 8;
        for col in (offset..trace.len() - POLY_SIZE).skip(1).step_by(2) {
            let mut col_gen = logup_gen.new_col();
            for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                // Access remainder columns from the merging phase
                let result_packed = trace[col].data[vec_row];

                // Create the denominator using the lookup elements for range checking
                let denom: PackedQM31 = rc_lookup_elements.combine(&[result_packed]);

                // The numerator is 1 (we want to check that remainder is in the range)
                let numerator = PackedQM31::one();

                col_gen.write_frac(vec_row, numerator, denom);
            }
            col_gen.finalize_col();
        }

        // Phase 3: Link NTT output to INTT input with negative multiplicity
        // This ensures that the NTT output can be used as input for the inverse transform
        for col in trace[trace.len() - POLY_SIZE..].iter() {
            let mut col_gen = logup_gen.new_col();
            for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                let v = col.data[vec_row]; // must have all lanes populated
                let denom: PackedQM31 = ntt_lookup_elements.combine(&[v]);
                col_gen.write_frac(vec_row, -PackedQM31::from(is_first.data[vec_row]), denom);
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
