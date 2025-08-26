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

use itertools::Itertools;

use num_traits::One;
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
    FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEFTraitBound,
    RelationEntry,
};

use crate::{
    POLY_LOG_SIZE,
    big_air::relation::{ButterflyLookupElements, NTTLookupElements, RCLookupElements},
    ntts::{
        ROOTS,
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
        input_polys: &[Vec<u32>],
        stage: usize,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Vec<Vec<M31>>,
        Vec<Vec<u32>>,
    ) {
        // Initialize the input polynomial with values [1, 2, ..., POLY_SIZE]

        // Prepare data structures for the merging phase

        let mut output_polys = Vec::with_capacity(input_polys.len() / 2);
        let mut trace = vec![vec![0; 1 << self.log_size]; 8 * (1 << stage)];
        let mut remainders = vec![];
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
        for (i, coeffs) in input_polys.chunks_exact(2).enumerate() {
            let left = &coeffs[0]; // f0_ntt polynomial
            let right = &coeffs[1]; // f1_ntt polynomial

            // Process each coefficient pair from the two polynomials
            let mut merged_poly = vec![];
            for (j, (coeff_left, coeff_right)) in left.iter().zip(right.iter()).enumerate() {
                // Get the appropriate root of unity for this position
                // Each level uses different roots from the precomputed ROOTS array
                let root = ROOTS[stage][2 * j];

                trace[8 * j][i] = *coeff_left;
                trace[8 * j + 1][i] = *coeff_right;

                // Step 1: Multiply f1_ntt coefficient by root of unity
                // f1_ntt[i] * w[2 * i] = quotient * Q + remainder
                let root_times_f1_quotient = (*coeff_right * root) / Q;
                let root_times_f1_remainder = (*coeff_right * root) % Q;

                trace[8 * j + 2][i] = root_times_f1_quotient;
                trace[8 * j + 3][i] = root_times_f1_remainder;

                // Step 2: Add f0_ntt coefficient to the multiplied result
                // f0_ntt[i] + f1_ntt[i] * w[2 * i] = quotient * Q + remainder
                let f0_plus_root_times_f1_quotient = (*coeff_left + root_times_f1_remainder) / Q;
                let f0_plus_root_times_f1_remainder = (*coeff_left + root_times_f1_remainder) % Q;

                trace[8 * j + 4][i] = f0_plus_root_times_f1_quotient;
                trace[8 * j + 5][i] = f0_plus_root_times_f1_remainder;

                // Step 3: Subtract the multiplied result from f0_ntt coefficient
                // f0_ntt[i] - f1_ntt[i] * w[2 * i] = quotient * Q + remainder (with borrow handling)
                let f0_minus_root_times_f1_borrow = (*coeff_left < root_times_f1_remainder) as u32;
                let f0_minus_root_times_f1_remainder =
                    (*coeff_left + f0_minus_root_times_f1_borrow * Q - root_times_f1_remainder) % Q;

                trace[8 * j + 6][i] = f0_minus_root_times_f1_borrow;
                trace[8 * j + 7][i] = f0_minus_root_times_f1_remainder;

                // Store the results for the next recursive level
                merged_poly.push(f0_plus_root_times_f1_remainder);
                merged_poly.push(f0_minus_root_times_f1_remainder);
            }
            output_polys.push(merged_poly);
        }

        for i in 0..1 << stage {
            remainders.extend(trace[8 * i + 3].iter().map(|x| M31(*x)));
            remainders.extend(trace[8 * i + 5].iter().map(|x| M31(*x)));
            remainders.extend(trace[8 * i + 7].iter().map(|x| M31(*x)));
        }

        // end of loop
        let trace = trace
            .into_iter()
            .map(|col| col.into_iter().map(M31).collect_vec())
            .collect_vec();

        // Convert the trace values to circle evaluations for the proof system
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        let mut is_filled = vec![M31(0); 1 << self.log_size];
        (0..1 << (POLY_LOG_SIZE as usize - stage - 1)).for_each(|i| {
            is_filled[i] = M31(1);
        });

        (
            std::iter::once(is_filled)
                .chain(trace)
                .map(|val| {
                    CircleEvaluation::<SimdBackend, _, BitReversedOrder>::new(
                        domain,
                        BaseColumn::from_iter(val),
                    )
                })
                .collect::<Vec<_>>(),
            vec![remainders],
            output_polys,
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
    pub poly_size: usize,
    /// Lookup elements for range checking modular arithmetic operations
    pub rc_lookup_elements: RCLookupElements,
    /// Lookup elements for NTT operations
    pub ntt_lookup_elements: NTTLookupElements,
    /// Lookup elements for butterfly output
    pub input_lookup_elements: InputLookupElements,
}

#[derive(Debug, Clone)]
pub enum InputLookupElements {
    NTT(NTTLookupElements),
    Butterfly(ButterflyLookupElements),
}

impl<F, EF> Relation<F, EF> for InputLookupElements
where
    F: Clone,
    EF: RelationEFTraitBound<F>,
{
    fn combine(&self, values: &[F]) -> EF {
        match self {
            InputLookupElements::NTT(lookup_elements) => lookup_elements.combine(values),
            InputLookupElements::Butterfly(lookup_elements) => lookup_elements.combine(values),
        }
    }

    fn get_name(&self) -> &str {
        match self {
            InputLookupElements::NTT(lookup_elements) => {
                <NTTLookupElements as Relation<F, EF>>::get_name(lookup_elements)
            }
            InputLookupElements::Butterfly(lookup_elements) => {
                <ButterflyLookupElements as Relation<F, EF>>::get_name(lookup_elements)
            }
        }
    }

    fn get_size(&self) -> usize {
        match self {
            InputLookupElements::NTT(lookup_elements) => {
                <NTTLookupElements as Relation<F, EF>>::get_size(lookup_elements)
            }
            InputLookupElements::Butterfly(lookup_elements) => {
                <ButterflyLookupElements as Relation<F, EF>>::get_size(lookup_elements)
            }
        }
    }
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
        let is_filled = eval.next_trace_mask();
        let mut merges = MergeNTT::default();

        // Process each coefficient pair using the appropriate root of unity
        for j in 0..self.poly_size {
            let root = ROOTS[self.poly_size.ilog2() as usize][2 * j];
            let coeff_left = eval.next_trace_mask();
            let coeff_right = eval.next_trace_mask();

            eval.add_to_relation(RelationEntry::new(
                &self.input_lookup_elements,
                E::EF::from(is_filled.clone()),
                &[coeff_left.clone()],
            ));

            eval.add_to_relation(RelationEntry::new(
                &self.input_lookup_elements,
                E::EF::from(is_filled.clone()),
                &[coeff_right.clone()],
            ));

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
            let merge = Merge::new(root_times_f1, f0_plus_root_times_f1, f0_minus_root_times_f1);
            merges.push(merge);
        }

        // Evaluate the merge operations and store the result
        let merged_poly = MergeNTT::evaluate(merges, &self.rc_lookup_elements, &mut eval);

        merged_poly.into_iter().for_each(|x| {
            eval.add_to_relation(RelationEntry::new(
                &self.ntt_lookup_elements,
                -E::EF::from(is_filled.clone()),
                &[x],
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
        input_lookup_elements: &InputLookupElements,
        stage: usize,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        InteractionClaim,
    ) {
        let log_size = trace[0].domain.log_size();
        let mut logup_gen = LogupTraceGenerator::new(log_size);
        let is_first = trace[0].clone();
        let trace = trace.iter().skip(1).collect::<Vec<_>>();

        for coeff_nb in 0..1 << stage {
            for col_offset in [0, 1] {
                let mut col_gen = logup_gen.new_col();
                for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                    let v = trace[coeff_nb * 8 + col_offset].data[vec_row]; // must have all lanes populated
                    let denom: PackedQM31 = input_lookup_elements.combine(&[v]);
                    col_gen.write_frac(vec_row, PackedQM31::from(is_first.data[vec_row]), denom);
                }
                col_gen.finalize_col();
            }
        }

        for coeff_nb in 0..1 << stage {
            for col_offset in [3, 5, 7] {
                let mut col_gen = logup_gen.new_col();
                for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                    let v = trace[coeff_nb * 8 + col_offset].data[vec_row]; // must have all lanes populated
                    let denom: PackedQM31 = rc_lookup_elements.combine(&[v]);
                    col_gen.write_frac(vec_row, PackedQM31::one(), denom);
                }
                col_gen.finalize_col();
            }
        }

        for coeff_nb in 0..1 << stage {
            for col_offset in [5, 7] {
                let mut col_gen = logup_gen.new_col();
                for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                    let v = trace[coeff_nb * 8 + col_offset].data[vec_row]; // must have all lanes populated
                    let denom: PackedQM31 = ntt_lookup_elements.combine(&[v]);
                    col_gen.write_frac(vec_row, -PackedQM31::from(is_first.data[vec_row]), denom);
                }
                col_gen.finalize_col();
            }
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
