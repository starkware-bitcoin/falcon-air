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
use stwo_constraint_framework::{FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation};

use crate::{
    POLY_LOG_SIZE, POLY_SIZE,
    ntts::{
        ROOTS, SQ1,
        ntt::merge::{Merge, MergeNTT},
    },
    zq::{Q, add::AddMod, mul::MulMod, range_check, sub::SubMod},
};

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
    /// including both the initial butterfly phase and the merging phase. Each
    /// arithmetic operation is decomposed into quotient and remainder parts for
    /// modular arithmetic verification.
    ///
    /// # Returns
    ///
    /// Returns a tuple containing:
    /// - `ColumnVec<CircleEvaluation<...>>`: The main computation trace columns
    /// - `Vec<Vec<M31>>`: Remainder values organized by operation type (MUL, ADD, SUB)
    #[allow(clippy::type_complexity)]
    pub fn gen_trace(
        &self,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Vec<Vec<M31>>,
    ) {
        // Initialize the input polynomial with values [1, 2, ..., POLY_SIZE]
        let mut poly = (1..POLY_SIZE + 1).collect::<Vec<_>>();

        // Apply bit-reversal permutation to prepare for in-place NTT computation
        // This ensures the polynomial is in the correct order for the butterfly operations
        bit_reverse(&mut poly);
        let bit_reversed_0 = bit_reverse_index(0, self.log_size);

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
                let f1_times_sq1_quotient = (f1 * SQ1) / Q;
                let f1_times_sq1_remainder = (f1 * SQ1) % Q;

                let f0_plus_f1_times_sq1_quotient = (f0 + f1_times_sq1_remainder) / Q;
                let f0_plus_f1_times_sq1_remainder = (f0 + f1_times_sq1_remainder) % Q;

                let f0_minus_f1_times_sq1_quotient = (f0 < f1_times_sq1_remainder) as u32;
                let f0_minus_f1_times_sq1_remainder =
                    (f0 + f0_minus_f1_times_sq1_quotient * Q - f1_times_sq1_remainder) % Q;

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

        // Phase 2: Merging Operations
        //
        // This phase implements the remaining NTT levels using merging operations:
        //   f_ntt[2 * i + 0] = (f0_ntt[i] + w[2 * i] * f1_ntt[i]) % q
        //   f_ntt[2 * i + 1] = (f0_ntt[i] - w[2 * i] * f1_ntt[i]) % q
        //
        // Each merging operation requires 6 new trace columns:
        // - f1_ntt[i] * w[2 * i] / Q, f1_ntt[i] * w[2 * i] % Q: Multiplication with root
        // - f0_ntt[i] + f1_ntt[i] * w[2 * i] / Q, f0_ntt[i] + f1_ntt[i] * w[2 * i] % Q: Addition
        // - f0_ntt[i] - f1_ntt[i] * w[2 * i] / Q, f0_ntt[i] - f1_ntt[i] * w[2 * i] % Q: Subtraction
        //
        // The roots of unity (w[2 * i]) are precomputed and stored in ROOTS[i][2 * j]
        for i in 1..POLY_LOG_SIZE as usize {
            for coeffs in polys[i - 1].clone().chunks_exact(2) {
                let left = &coeffs[0]; // f0_ntt polynomial
                let right = &coeffs[1]; // f1_ntt polynomial

                // Process each coefficient pair from the two polynomials
                let mut merged_poly = vec![];
                for (j, (coeff_left, coeff_right)) in left.iter().zip(right.iter()).enumerate() {
                    // Get the appropriate root of unity for this position
                    let root = ROOTS[i][2 * j];

                    // Step 1: Multiply f1_ntt coefficient by root of unity
                    let root_times_f1_quotient = (*coeff_right * root) / Q;
                    let root_times_f1_remainder = (*coeff_right * root) % Q;

                    trace.push(root_times_f1_quotient);
                    trace.push(root_times_f1_remainder);

                    // Step 2: Add f0_ntt coefficient to the multiplied result
                    let f0_plus_root_times_f1_quotient =
                        (*coeff_left + root_times_f1_remainder) / Q;
                    let f0_plus_root_times_f1_remainder =
                        (*coeff_left + root_times_f1_remainder) % Q;

                    trace.push(f0_plus_root_times_f1_quotient);
                    trace.push(f0_plus_root_times_f1_remainder);

                    // Step 3: Subtract the multiplied result from f0_ntt coefficient
                    // Handle potential underflow with borrow bit
                    let f0_minus_root_times_f1_borrow =
                        (*coeff_left < root_times_f1_remainder) as u32;
                    let f0_minus_root_times_f1_remainder =
                        (*coeff_left + f0_minus_root_times_f1_borrow * Q - root_times_f1_remainder)
                            % Q;
                    trace.push(f0_minus_root_times_f1_borrow);
                    trace.push(f0_minus_root_times_f1_remainder);

                    // Store the results for the next iteration
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

        (
            final_trace
                .into_iter()
                .chain(trace)
                .map(|val| {
                    CircleEvaluation::<SimdBackend, _, BitReversedOrder>::new(
                        domain,
                        BaseColumn::from_iter(val),
                    )
                })
                .collect::<Vec<_>>(),
            remainders.collect(),
        )
    }
}

/// Evaluation component for the NTT circuit.
///
/// This struct contains the necessary data to evaluate the NTT constraints
/// during proof generation, including the claim parameters and lookup elements
/// for range checking of modular arithmetic operations.
#[derive(Debug, Clone)]
pub struct Eval {
    /// The claim parameters defining the NTT computation
    pub claim: Claim,
    /// Lookup elements for range checking modular arithmetic operations
    pub lookup_elements: range_check::LookupElements,
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
    fn evaluate<E: stwo_constraint_framework::EvalAtRow>(&self, mut eval: E) -> E {
        let sq1 = E::F::from(M31::from_u32_unchecked(SQ1));
        let mut base_f_ntt = Vec::with_capacity(POLY_SIZE as usize);

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
            .evaluate(&self.lookup_elements, &mut eval);

            AddMod::new(
                f0.clone(),
                f1_times_sq1_remainder.clone(),
                f0_plus_f1_times_sq1_quotient,
                f0_plus_f1_times_sq1_remainder.clone(),
            )
            .evaluate(&self.lookup_elements, &mut eval);

            SubMod::new(
                f0,
                f1_times_sq1_remainder,
                f0_minus_f1_times_sq1_quotient,
                f0_minus_f1_times_sq1_remainder.clone(),
            )
            .evaluate(&self.lookup_elements, &mut eval);

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
                let merged_poly = MergeNTT::evaluate(merges, &self.lookup_elements, &mut eval);
                poly[i].push(merged_poly);
            }
        }

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
        lookup_elements: &range_check::LookupElements,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        InteractionClaim,
    ) {
        let log_size = trace[0].domain.log_size();
        let mut logup_gen = LogupTraceGenerator::new(log_size);

        // Phase 1: Interaction trace for the initial butterfly phase
        // Check remainder values from columns 3, 5, 7 of each 8-column group
        let first_ntt_size = 1 << (POLY_LOG_SIZE - 1);
        for operation_elemnt_index in 0..first_ntt_size {
            for col in [3, 5, 7] {
                let mut col_gen = logup_gen.new_col();
                for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                    // Each butterfly operation uses 8 columns, so we access the remainder columns
                    let result_packed = trace[operation_elemnt_index * 8 + col].data[vec_row];

                    // Create the denominator using the lookup elements for range checking
                    let denom: PackedQM31 = lookup_elements.combine(&[result_packed]);
                    col_gen.write_frac(vec_row, PackedQM31::one(), denom);
                }
                col_gen.finalize_col();
            }
        }

        // Phase 2: Interaction trace for the merging phase
        // Check remainder values from every other column in the merging phase
        let offset = first_ntt_size * 8 + 1;
        for col in (offset..trace.len()).step_by(2) {
            let mut col_gen = logup_gen.new_col();
            for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                // Access remainder columns from the merging phase
                let result_packed = trace[col].data[vec_row];

                // Create the denominator using the lookup elements for range checking
                let denom: PackedQM31 = lookup_elements.combine(&[result_packed]);

                // The numerator is 1 (we want to check that remainder is in the range)
                let numerator = PackedQM31::one();

                col_gen.write_frac(vec_row, numerator, denom);
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
pub type Component = FrameworkComponent<Eval>;
