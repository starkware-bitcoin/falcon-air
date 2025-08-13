//! Inverse Number Theoretic Transform (INTT) implementation for polynomial interpolation.
//!
//! This module implements a complete INTT circuit that performs polynomial interpolation
//! over a finite field using modular arithmetic operations. The INTT is the inverse of
//! the NTT and converts from evaluation form back to coefficient form.
//!
//! The INTT algorithm works by:
//! 1. **Splitting Phase**: Decomposes the polynomial into smaller subproblems
//! 2. **Recursive Computation**: Applies INTT to each subproblem
//! 3. **Combining Phase**: Merges results using inverse roots of unity
//!
//! Key differences from NTT:
//! - Uses inverse roots of unity (INVERSES_MOD_Q)
//! - Includes scaling factor I2 (1/2) at each level
//! - Input is in evaluation form, output is in coefficient form
//!
//! Each phase uses modular arithmetic operations (multiplication, addition, subtraction)
//! with range checking to ensure correctness within the field bounds.

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
    ntts::{
        I2, ROOTS, SQ1,
        intt::split::{Split, SplitNTT},
        ntt,
    },
    zq::{
        Q,
        add::{ADD_COL, AddMod},
        inverses::INVERSES_MOD_Q,
        mul::{MUL_COL, MulMod},
        range_check,
        sub::{SUB_COL, SubMod},
    },
};

pub mod split;

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
    /// - `trace`: Main INTT computation trace
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

    /// Generates the complete INTT computation trace.
    ///
    /// This function creates a trace that represents the entire INTT computation,
    /// including the splitting phase and recursive combination phase. Each
    /// arithmetic operation is decomposed into quotient and remainder parts for
    /// modular arithmetic verification.
    ///
    /// The INTT algorithm:
    /// 1. Takes NTT output as input (polynomial in evaluation form)
    /// 2. Splits the polynomial into even and odd coefficients  
    /// 3. Recursively applies INTT to each half
    /// 4. Combines results using inverse roots of unity and scaling factor I2
    /// 5. Applies final butterfly with SQ1 inverse to complete the transform
    ///
    /// # Returns
    ///
    /// Returns a tuple containing:
    /// - `ColumnVec<CircleEvaluation<...>>`: The main computation trace columns
    /// - `Vec<Vec<M31>>`: Remainder values organized by operation type (MUL, ADD, SUB)
    #[allow(clippy::type_complexity)]
    pub fn gen_trace(
        &self,
        poly: Vec<u32>,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Vec<Vec<M31>>,
    ) {
        // Initialize with the NTT output polynomial (already in evaluation form)
        // This represents the polynomial that we want to convert back to coefficient form
        let poly = vec![poly];

        // Initialize remainder arrays for each operation type (MUL, ADD, SUB)
        // These will be used for range checking during proof verification
        let mut remainders = vec![vec![]; 3];
        let mut flat_remainders = vec![];
        let mut trace = poly[0].to_vec();

        // Prepare data structures for the recursive INTT computation
        // Each level will contain polynomials of decreasing size
        let mut polys = vec![vec![]; POLY_LOG_SIZE as usize];
        polys[0] = poly;

        // Phase 1: Recursive INTT Computation
        //
        // This phase implements the INTT algorithm by recursively splitting and combining polynomials:
        // 1. Split each polynomial into even and odd coefficients
        // 2. Apply INTT to each half recursively
        // 3. Combine results using inverse roots of unity and scaling factor I2
        //
        // The INTT butterfly operations:
        //   f0_ntt[i] = I2 * (f_even[i] + f_odd[i]) % q
        //   f1_ntt[i] = I2 * (f_even[i] - f_odd[i]) * inv_root[i] % q
        //
        // Each operation requires multiple trace columns for modular arithmetic decomposition
        for i in 1..POLY_LOG_SIZE as usize {
            for poly in polys[i - 1].clone() {
                let mut f0_ntt = vec![];
                let mut f1_ntt = vec![];

                // Process pairs of coefficients (even, odd) from the polynomial
                for (j, (f_even, f_odd)) in poly
                    .iter()
                    .step_by(2)
                    .zip(poly.iter().skip(1).step_by(2))
                    .enumerate()
                {
                    // Get the appropriate inverse root of unity for this position
                    // Note: We use regular roots here but will inverse later
                    let root = ROOTS[poly.len().ilog2() as usize - 1][2 * j];

                    // Step 1: Add even and odd coefficients
                    // f_even[i] + f_odd[i]
                    let f_even_plus_f_odd_quotient = (*f_even + *f_odd) / Q;
                    let f_even_plus_f_odd_remainder = (*f_even + *f_odd) % Q;

                    trace.push(f_even_plus_f_odd_quotient);
                    trace.push(f_even_plus_f_odd_remainder);
                    remainders[ADD_COL].push(f_even_plus_f_odd_remainder);
                    flat_remainders.push(f_even_plus_f_odd_remainder);

                    // Step 2: Apply scaling factor I2 to the sum
                    // I2 * (f_even[i] + f_odd[i]) where I2 = inv(2) mod q
                    let i2_times_f_even_plus_f_odd_quotient =
                        (I2 * f_even_plus_f_odd_remainder) / Q;
                    let i2_times_f_even_plus_f_odd_remainder =
                        (I2 * f_even_plus_f_odd_remainder) % Q;

                    trace.push(i2_times_f_even_plus_f_odd_quotient);
                    trace.push(i2_times_f_even_plus_f_odd_remainder);
                    remainders[MUL_COL].push(i2_times_f_even_plus_f_odd_remainder);
                    flat_remainders.push(i2_times_f_even_plus_f_odd_remainder);

                    // Step 3: Subtract odd from even coefficients
                    // f_even[i] - f_odd[i] (with borrow handling for modular subtraction)
                    let f_even_minus_f_odd_borrow = (*f_even < *f_odd) as u32;
                    let f_even_minus_f_odd_remainder =
                        (*f_even + f_even_minus_f_odd_borrow * Q - *f_odd) % Q;

                    trace.push(f_even_minus_f_odd_borrow);
                    trace.push(f_even_minus_f_odd_remainder);
                    remainders[SUB_COL].push(f_even_minus_f_odd_remainder);
                    flat_remainders.push(f_even_minus_f_odd_remainder);

                    // Step 4: Apply scaling factor I2 to the difference
                    // I2 * (f_even[i] - f_odd[i])
                    let i2_times_f_even_minus_f_odd_quotient =
                        (I2 * f_even_minus_f_odd_remainder) / Q;
                    let i2_times_f_even_minus_f_odd_remainder =
                        (I2 * f_even_minus_f_odd_remainder) % Q;

                    trace.push(i2_times_f_even_minus_f_odd_quotient);
                    trace.push(i2_times_f_even_minus_f_odd_remainder);
                    remainders[MUL_COL].push(i2_times_f_even_minus_f_odd_remainder);
                    flat_remainders.push(i2_times_f_even_minus_f_odd_remainder);

                    // Step 5: Multiply by inverse root of unity
                    // I2 * (f_even[i] - f_odd[i]) * inv_root[i] where inv_root[i] = 1/root[i]
                    let i2_times_f_even_minus_f_odd_times_root_inv_quotient =
                        (i2_times_f_even_minus_f_odd_remainder * INVERSES_MOD_Q[root as usize]) / Q;
                    let i2_times_f_even_minus_f_odd_times_root_inv_remainder =
                        (i2_times_f_even_minus_f_odd_remainder * INVERSES_MOD_Q[root as usize]) % Q;

                    trace.push(i2_times_f_even_minus_f_odd_times_root_inv_quotient);
                    trace.push(i2_times_f_even_minus_f_odd_times_root_inv_remainder);
                    remainders[MUL_COL].push(i2_times_f_even_minus_f_odd_times_root_inv_remainder);
                    flat_remainders.push(i2_times_f_even_minus_f_odd_times_root_inv_remainder);

                    // Store the results for the next recursive level
                    f0_ntt.push(i2_times_f_even_plus_f_odd_remainder);
                    f1_ntt.push(i2_times_f_even_minus_f_odd_times_root_inv_remainder);
                }
                polys[i].push(f0_ntt);
                polys[i].push(f1_ntt);
            }
        }

        // Phase 2: Final INTT Combination
        //
        // This phase performs the final INTT butterfly operation on the last two coefficients:
        // 1. Add the two remaining coefficients
        // 2. Apply scaling factor I2
        // 3. Subtract the coefficients
        // 4. Apply scaling factor I2 and inverse of SQ1
        //
        // This completes the INTT and produces the final coefficient form result
        let mut debug_result = vec![];

        for poly in polys.iter().last().unwrap() {
            debug_assert!(poly.len() == 2);

            // Step 1: Add the final two coefficients
            // f_ntt[0] + f_ntt[1]
            let f_ntt_0_plus_f_ntt_1_quotient = (poly[0] + poly[1]) / Q;
            let f_ntt_0_plus_f_ntt_1_remainder = (poly[0] + poly[1]) % Q;

            trace.push(f_ntt_0_plus_f_ntt_1_quotient);
            trace.push(f_ntt_0_plus_f_ntt_1_remainder);
            remainders[ADD_COL].push(f_ntt_0_plus_f_ntt_1_remainder);
            flat_remainders.push(f_ntt_0_plus_f_ntt_1_remainder);

            // Step 2: Apply scaling factor I2 to the sum
            // I2 * (f_ntt[0] + f_ntt[1]) where I2 = 1/2
            let i2_times_f_ntt_0_plus_f_ntt_1_quotient = (I2 * f_ntt_0_plus_f_ntt_1_remainder) / Q;
            let i2_times_f_ntt_0_plus_f_ntt_1_remainder = (I2 * f_ntt_0_plus_f_ntt_1_remainder) % Q;
            debug_result.push(i2_times_f_ntt_0_plus_f_ntt_1_remainder);

            trace.push(i2_times_f_ntt_0_plus_f_ntt_1_quotient);
            trace.push(i2_times_f_ntt_0_plus_f_ntt_1_remainder);
            remainders[MUL_COL].push(i2_times_f_ntt_0_plus_f_ntt_1_remainder);
            flat_remainders.push(i2_times_f_ntt_0_plus_f_ntt_1_remainder);

            // Step 3: Subtract the final two coefficients
            // f_ntt[0] - f_ntt[1] (with borrow handling)
            let f_ntt_0_minus_f_ntt_1_quotient = (poly[0] < poly[1]) as u32;
            let f_ntt_0_minus_f_ntt_1_remainder =
                (poly[0] + f_ntt_0_minus_f_ntt_1_quotient * Q - poly[1]) % Q;

            trace.push(f_ntt_0_minus_f_ntt_1_quotient);
            trace.push(f_ntt_0_minus_f_ntt_1_remainder);
            remainders[SUB_COL].push(f_ntt_0_minus_f_ntt_1_remainder);
            flat_remainders.push(f_ntt_0_minus_f_ntt_1_remainder);

            // Step 4: Apply scaling factor I2 and inverse of SQ1 to the difference
            // I2 * inv_sq1 * (f_ntt[0] - f_ntt[1]) where inv_sq1 = 1/sq1
            let i2_times_inv_sq1 = (I2 * INVERSES_MOD_Q[SQ1 as usize]) % Q;

            // I2 * inv_sq1 * (f_ntt[0] - f_ntt[1])
            let i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_quotient =
                (i2_times_inv_sq1 * f_ntt_0_minus_f_ntt_1_remainder) / Q;
            let i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder =
                (i2_times_inv_sq1 * f_ntt_0_minus_f_ntt_1_remainder) % Q;

            trace.push(i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_quotient);
            trace.push(i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder);
            remainders[MUL_COL].push(i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder);
            flat_remainders.push(i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder);
            debug_result.push(i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder);
        }

        bit_reverse(&mut debug_result);
        let trace = trace
            .into_iter()
            .chain(debug_result)
            .map(M31)
            .collect::<Vec<_>>();

        // Convert the trace values to circle evaluations for the proof system
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        let bit_reversed_0 = bit_reverse_index(0, self.log_size);

        (
            trace
                .into_iter()
                .map(|val| {
                    // Create a column with the trace value at the bit-reversed index
                    let mut col = vec![M31::zero(); 1 << self.log_size];
                    col[bit_reversed_0] = val;
                    CircleEvaluation::<SimdBackend, _, BitReversedOrder>::new(
                        domain,
                        BaseColumn::from_iter(col),
                    )
                })
                .collect::<Vec<_>>(),
            // Convert remainder values to M31 field elements for range checking
            remainders
                .into_iter()
                .map(|col| {
                    col.into_iter()
                        .map(M31::from_u32_unchecked)
                        .collect::<Vec<_>>()
                })
                .collect(),
        )
    }
}

/// Evaluation component for the INTT circuit.
///
/// This struct contains the necessary data to evaluate the INTT constraints
/// during proof generation, including the claim parameters and lookup elements
/// for range checking of modular arithmetic operations.
#[derive(Debug, Clone)]
pub struct Eval {
    /// The claim parameters defining the INTT computation
    pub claim: Claim,
    /// Lookup elements for range checking modular arithmetic operations
    pub rc_lookup_elements: range_check::LookupElements,
    /// Lookup elements for NTT operations
    pub ntt_lookup_elements: ntt::LookupElements,
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

    /// Evaluates the INTT constraints during proof generation.
    ///
    /// This function generates the constraint evaluation trace that matches
    /// the computation trace generated by `gen_trace`. It ensures that all
    /// modular arithmetic operations are correctly verified through range checking.
    fn evaluate<E: stwo_constraint_framework::EvalAtRow>(&self, mut eval: E) -> E {
        let mut poly = Vec::with_capacity(POLY_SIZE);
        for _ in 0..(1 << (POLY_LOG_SIZE - 1)) {
            let f_even = eval.next_trace_mask();
            let f_odd = eval.next_trace_mask();
            poly.push(f_even.clone());
            poly.push(f_odd.clone());
            eval.add_to_relation(RelationEntry::new(
                &self.ntt_lookup_elements,
                E::EF::one(),
                &[f_even],
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.ntt_lookup_elements,
                E::EF::one(),
                &[f_odd],
            ));
        }

        let mut polys = vec![vec![]; POLY_LOG_SIZE as usize];
        polys[0] = vec![poly];

        for i in 1..POLY_LOG_SIZE as usize {
            for poly in polys[i - 1].clone() {
                let mut split = SplitNTT::default();

                for (j, (f_even, f_odd)) in poly
                    .iter()
                    .step_by(2)
                    .zip(poly.iter().skip(1).step_by(2))
                    .enumerate()
                {
                    let f_even_plus_f_odd = AddMod::<E>::new(
                        f_even.clone(),
                        f_odd.clone(),
                        eval.next_trace_mask().clone(),
                        eval.next_trace_mask().clone(),
                    );
                    let i2_times_f_even_plus_f_odd = MulMod::<E>::new(
                        E::F::from(M31(I2)),
                        f_even_plus_f_odd.r.clone(),
                        eval.next_trace_mask(),
                        eval.next_trace_mask(),
                    );

                    let f_even_minus_f_odd = SubMod::<E>::new(
                        f_even.clone(),
                        f_odd.clone(),
                        eval.next_trace_mask(),
                        eval.next_trace_mask(),
                    );
                    let i2_times_f_even_minus_f_odd = MulMod::<E>::new(
                        E::F::from(M31(I2)),
                        f_even_minus_f_odd.r.clone(),
                        eval.next_trace_mask(),
                        eval.next_trace_mask(),
                    );
                    let root = ROOTS[poly.len().ilog2() as usize - 1][2 * j];
                    let inv = INVERSES_MOD_Q[root as usize];
                    let i2_times_f_even_minus_f_odd_times_root_inv = MulMod::<E>::new(
                        i2_times_f_even_minus_f_odd.r.clone(),
                        E::F::from(M31(inv)),
                        eval.next_trace_mask(),
                        eval.next_trace_mask(),
                    );
                    split.push(Split::new(
                        f_even_plus_f_odd,
                        i2_times_f_even_plus_f_odd,
                        f_even_minus_f_odd,
                        i2_times_f_even_minus_f_odd,
                        i2_times_f_even_minus_f_odd_times_root_inv,
                    ));
                }
                let (f0, f1) = split.evaluate(&self.rc_lookup_elements, &mut eval);

                polys[i].push(f0);
                polys[i].push(f1);
            }
        }
        let mut res = vec![];

        for poly in polys.iter().last().unwrap() {
            debug_assert!(poly.len() == 2);
            // (f_ntt[0] + f_ntt[1])

            let f_ntt_0_plus_f_ntt_quotient = eval.next_trace_mask();
            let f_ntt_0_plus_f_ntt_remainder = eval.next_trace_mask();
            AddMod::<E>::new(
                poly[0].clone(),
                poly[1].clone(),
                f_ntt_0_plus_f_ntt_quotient,
                f_ntt_0_plus_f_ntt_remainder.clone(),
            )
            .evaluate(&self.rc_lookup_elements, &mut eval);

            // (i2 * (f_ntt[0] + f_ntt[1])) % q
            let i2_times_f_ntt_0_plus_f_ntt_quotient = eval.next_trace_mask();
            let i2_times_f_ntt_0_plus_f_ntt_remainder = eval.next_trace_mask();
            MulMod::<E>::new(
                E::F::from(M31(I2)),
                f_ntt_0_plus_f_ntt_remainder.clone(),
                i2_times_f_ntt_0_plus_f_ntt_quotient,
                i2_times_f_ntt_0_plus_f_ntt_remainder.clone(),
            )
            .evaluate(&self.rc_lookup_elements, &mut eval);
            res.push(i2_times_f_ntt_0_plus_f_ntt_remainder);

            // f_ntt[0] - f_ntt[1]
            let f_ntt_0_minus_f_ntt_quotient = eval.next_trace_mask();
            let f_ntt_0_minus_f_ntt_remainder = eval.next_trace_mask();
            SubMod::<E>::new(
                poly[0].clone(),
                poly[1].clone(),
                f_ntt_0_minus_f_ntt_quotient,
                f_ntt_0_minus_f_ntt_remainder.clone(),
            )
            .evaluate(&self.rc_lookup_elements, &mut eval);

            let i2_times_inv_sq1 = (I2 * INVERSES_MOD_Q[SQ1 as usize]) % Q;

            // (i2 * inv_mod_q[sqr1] * (f_ntt[0] - f_ntt[1])) % q
            let i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_quotient =
                eval.next_trace_mask();
            let i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder =
                eval.next_trace_mask();
            MulMod::<E>::new(
                f_ntt_0_minus_f_ntt_remainder.clone(),
                E::F::from(M31(i2_times_inv_sq1)),
                i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_quotient,
                i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder.clone(),
            )
            .evaluate(&self.rc_lookup_elements, &mut eval);
            res.push(i2_times_inv_mod_q_sqr1_times_f_ntt_0_minus_f_ntt_1_remainder);
        }

        bit_reverse(&mut res);
        res.into_iter().for_each(|x| {
            let output_col = eval.next_trace_mask();

            eval.add_constraint(x - output_col);
        });

        eval.finalize_logup();
        eval
    }
}

/// Claim for the interaction trace that connects INTT computation with range checking.
///
/// This struct contains the claimed sum that links the INTT computation trace
/// with the range checking component through the lookup protocol. The interaction
/// ensures that all modular arithmetic operations produce results within the
/// expected range.
#[derive(Debug, Clone)]
pub struct InteractionClaim {
    /// The claimed sum for the interaction between INTT and range checking
    pub claimed_sum: SecureField,
}

impl InteractionClaim {
    /// Mixes the interaction claim into the Fiat-Shamir channel.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }

    /// Generates the interaction trace that connects INTT computation with range checking.
    ///
    /// This method creates an interaction trace that ensures all modular arithmetic
    /// operations in the INTT computation produce results within the expected range.
    /// It uses the lookup protocol to verify that remainders from modular operations
    /// are properly bounded.
    ///
    /// The interaction trace covers remainder values from the INTT computation phases.
    ///
    /// # Parameters
    ///
    /// - `trace`: The main INTT computation trace columns
    /// - `lookup_elements`: The lookup elements for range checking
    ///
    /// # Returns
    ///
    /// Returns the interaction trace and the interaction claim.
    pub fn gen_interaction_trace(
        trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        rc_lookup_elements: &range_check::LookupElements,
        ntt_lookup_elements: &ntt::LookupElements,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        InteractionClaim,
    ) {
        let log_size = trace[0].domain.log_size();
        let mut logup_gen = LogupTraceGenerator::new(log_size);

        for col in trace.iter().take(POLY_SIZE) {
            let mut col_gen = logup_gen.new_col();
            for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                let v = col.data[vec_row]; // must have all lanes populated
                let denom: PackedQM31 = ntt_lookup_elements.combine(&[v]);
                col_gen.write_frac(vec_row, PackedQM31::one(), denom);
            }
            col_gen.finalize_col();
        }

        for col in (POLY_SIZE + 1..trace.len() - POLY_SIZE).step_by(2) {
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

        let (interaction_trace, claimed_sum) = logup_gen.finalize_last();
        (interaction_trace, InteractionClaim { claimed_sum })
    }
}

/// Type alias for the INTT circuit component.
///
/// This represents the complete INTT circuit that can be used within
/// the constraint framework for proof generation and verification.
pub type Component = FrameworkComponent<Eval>;
