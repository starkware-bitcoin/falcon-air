//! INTT Split Phase implementation for polynomial interpolation.
//!
//! This module implements the splitting phase of the INTT circuit that performs
//! polynomial interpolation over a finite field using modular arithmetic operations.
//! The split phase decomposes polynomials into smaller subproblems for recursive computation.
//!
//! The split phase works by:
//! 1. **Polynomial Splitting**: Decomposes the polynomial into even and odd coefficients
//! 2. **Scaling Operations**: Applies scaling factor I2 (1/2) to normalize results
//! 3. **Inverse Root Multiplication**: Uses inverse roots of unity for decomposition
//!
//! Key characteristics:
//! - Uses inverse roots of unity (INVERSES_MOD_Q)
//! - Includes scaling factor I2 (1/2) at each level
//! - Input is in evaluation form, output is ready for recursive INTT computation
//! - Each operation uses modular arithmetic with range checking
//!
//! This is the splitting phase of the INTT that decomposes larger polynomials
//! into smaller subproblems for recursive computation.

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
    FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
};

use crate::{
    big_air::relation::{
        INTTInputLookupElements, INTTLookupElements, InvRootsLookupElements, RCLookupElements,
    },
    ntts::{I2, ROOTS, intt::split::Split},
    zq::{Q, add::AddMod, inverses::INVERSES_MOD_Q, mul::MulMod, sub::SubMod},
};

pub mod ibutterfly;
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

    /// Generates the INTT split phase computation trace.
    ///
    /// This function creates a trace that represents the splitting phase
    /// of the INTT computation. Each arithmetic operation is decomposed into
    /// quotient and remainder parts for modular arithmetic verification.
    ///
    /// The split phase algorithm:
    /// 1. Takes polynomial in evaluation form as input
    /// 2. Splits into even and odd coefficients
    /// 3. Applies scaling factor I2 and inverse roots of unity
    /// 4. Produces smaller polynomials for recursive INTT computation
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
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Vec<Vec<M31>>,
        Vec<Vec<u32>>,
        Vec<u32>,
    ) {
        let mut output_polys = vec![];

        let mut trace = vec![vec![]; 16];
        let mut remainders = vec![];
        let mut js = vec![];
        let mut row = 0;
        trace[0] = vec![0; 1 << self.log_size];
        trace[1] = vec![0; 1 << self.log_size];

        for poly in input_polys.iter() {
            let mut f0_ntt = vec![];
            let mut f1_ntt = vec![];

            // Process pairs of coefficients (even, odd) from the polynomial
            for (j, (f_even, f_odd)) in poly
                .iter()
                .step_by(2)
                .zip(poly.iter().skip(1).step_by(2))
                .enumerate()
            {
                let j = 2 * j;
                // Get the appropriate inverse root of unity for this position
                // Note: We use regular roots here but will inverse later
                let root = INVERSES_MOD_Q[ROOTS[poly.len().ilog2() as usize - 1][j] as usize];
                js.push(j as u32);
                if j == 0 {
                    trace[0][row] = 1;
                }
                trace[1][row] = 1;
                row += 1;
                trace[2].push(j as u32);
                trace[3].push(root);

                trace[4].push(*f_even);
                trace[5].push(*f_odd);

                // Step 1: Add even and odd coefficients
                // f_even[i] + f_odd[i]
                let f_even_plus_f_odd_quotient = (*f_even + *f_odd) / Q;
                let f_even_plus_f_odd_remainder = (*f_even + *f_odd) % Q;

                trace[6].push(f_even_plus_f_odd_quotient);
                trace[7].push(f_even_plus_f_odd_remainder);

                // Step 2: Apply scaling factor I2 to the sum
                // I2 * (f_even[i] + f_odd[i]) where I2 = inv(2) mod q
                let i2_times_f_even_plus_f_odd_quotient = (I2 * f_even_plus_f_odd_remainder) / Q;
                let i2_times_f_even_plus_f_odd_remainder = (I2 * f_even_plus_f_odd_remainder) % Q;

                trace[8].push(i2_times_f_even_plus_f_odd_quotient);
                trace[9].push(i2_times_f_even_plus_f_odd_remainder);

                // Step 3: Subtract odd from even coefficients
                // f_even[i] - f_odd[i] (with borrow handling for modular subtraction)
                let f_even_minus_f_odd_borrow = (*f_even < *f_odd) as u32;
                let f_even_minus_f_odd_remainder =
                    (*f_even + f_even_minus_f_odd_borrow * Q - *f_odd) % Q;

                trace[10].push(f_even_minus_f_odd_borrow);
                trace[11].push(f_even_minus_f_odd_remainder);

                // Step 4: Apply scaling factor I2 to the difference
                // I2 * (f_even[i] - f_odd[i])
                let i2_times_f_even_minus_f_odd_quotient = (I2 * f_even_minus_f_odd_remainder) / Q;
                let i2_times_f_even_minus_f_odd_remainder = (I2 * f_even_minus_f_odd_remainder) % Q;

                trace[12].push(i2_times_f_even_minus_f_odd_quotient);
                trace[13].push(i2_times_f_even_minus_f_odd_remainder);

                // Step 5: Multiply by inverse root of unity
                // I2 * (f_even[i] - f_odd[i]) * inv_root[i] where inv_root[i] = 1/root[i]
                let i2_times_f_even_minus_f_odd_times_root_inv_quotient =
                    (i2_times_f_even_minus_f_odd_remainder * root) / Q;
                let i2_times_f_even_minus_f_odd_times_root_inv_remainder =
                    (i2_times_f_even_minus_f_odd_remainder * root) % Q;

                trace[14].push(i2_times_f_even_minus_f_odd_times_root_inv_quotient);
                trace[15].push(i2_times_f_even_minus_f_odd_times_root_inv_remainder);

                // Store the results for the next recursive level
                f0_ntt.push(i2_times_f_even_plus_f_odd_remainder);
                f1_ntt.push(i2_times_f_even_minus_f_odd_times_root_inv_remainder);
                // f0_ntt.push(0);
                // f1_ntt.push(0);
            }
            output_polys.push(f0_ntt);
            output_polys.push(f1_ntt);
        }

        let trace = trace
            .into_iter()
            .map(|col| col.into_iter().map(M31).collect_vec())
            .collect_vec();

        remainders.extend(trace[7].clone());
        remainders.extend(trace[9].clone());
        remainders.extend(trace[11].clone());
        remainders.extend(trace[13].clone());
        remainders.extend(trace[15].clone());

        // Convert the trace values to circle evaluations for the proof system
        let domain = CanonicCoset::new(self.log_size).circle_domain();

        (
            trace
                .into_iter()
                .map(|val| {
                    CircleEvaluation::<SimdBackend, _, BitReversedOrder>::new(
                        domain,
                        BaseColumn::from_iter(val),
                    )
                })
                .collect::<Vec<_>>(),
            // Convert remainder values to M31 field elements for range checking
            vec![remainders],
            output_polys,
            js,
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
    pub rc_lookup_elements: RCLookupElements,
    /// Lookup elements for NTT operations
    pub input_lookup_elements: INTTInputLookupElements,
    /// Lookup elements for INTT output
    pub intt_lookup_elements: INTTLookupElements,
    /// Stage of the INTT computation
    pub poly_size: usize,
    /// Lookup elements for inverse roots of unity
    pub inv_roots_lookup_elements: InvRootsLookupElements,
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
        // Extract the filled mask that indicates which positions contain valid data
        let is_first_coeff = eval.next_trace_mask();
        let is_filled = eval.next_trace_mask();
        // Initialize collection of split operations for this INTT level

        // Process each pair of coefficients (even, odd) for the split operation

        let j = eval.next_trace_mask();
        let inv = eval.next_trace_mask();
        // Extract even and odd coefficients from the trace
        let f_even = eval.next_trace_mask();
        let f_odd = eval.next_trace_mask();

        eval.add_to_relation(RelationEntry::new(
            &self.inv_roots_lookup_elements,
            E::EF::from(is_filled.clone()),
            &[j.clone(), inv.clone()],
        ));
        eval.add_constraint(is_first_coeff.clone() * (is_first_coeff.clone() - E::F::one()));
        eval.add_constraint(is_first_coeff * j);
        eval.add_constraint(is_filled.clone() * (is_filled.clone() - E::F::one()));

        // Add input coefficients to lookup relation for verification
        // This ensures the input values are properly connected to the INTT computation
        eval.add_to_relation(RelationEntry::new(
            &self.input_lookup_elements,
            E::EF::from(is_filled.clone()),
            &[f_even.clone()],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.input_lookup_elements,
            E::EF::from(is_filled.clone()),
            &[f_odd.clone()],
        ));

        // Step 1: Add even and odd coefficients with modular arithmetic
        // This computes f_even[i] + f_odd[i] = quotient * Q + remainder
        let f_even_plus_f_odd = AddMod::<E>::new(
            f_even.clone(),
            f_odd.clone(),
            eval.next_trace_mask().clone(),
            eval.next_trace_mask().clone(),
        );

        // Step 2: Apply scaling factor I2 to the sum with modular arithmetic
        // This computes I2 * (f_even[i] + f_odd[i]) = quotient * Q + remainder
        let i2_times_f_even_plus_f_odd = MulMod::<E>::new(
            E::F::from(M31(I2)),
            f_even_plus_f_odd.r.clone(),
            eval.next_trace_mask(),
            eval.next_trace_mask(),
        );

        // Step 3: Subtract odd from even coefficients with modular arithmetic
        // This computes f_even[i] - f_odd[i] = quotient * Q + remainder (with borrow)
        let f_even_minus_f_odd = SubMod::<E>::new(
            f_even.clone(),
            f_odd.clone(),
            eval.next_trace_mask(),
            eval.next_trace_mask(),
        );

        // Step 4: Apply scaling factor I2 to the difference with modular arithmetic
        // This computes I2 * (f_even[i] - f_odd[i]) = quotient * Q + remainder
        let i2_times_f_even_minus_f_odd = MulMod::<E>::new(
            E::F::from(M31(I2)),
            f_even_minus_f_odd.r.clone(),
            eval.next_trace_mask(),
            eval.next_trace_mask(),
        );

        // Step 5: Multiply by inverse root of unity with modular arithmetic
        // Get the appropriate root and its inverse for this position
        // This computes I2 * (f_even[i] - f_odd[i]) * inv_root[i] = quotient * Q + remainder
        let i2_times_f_even_minus_f_odd_times_root_inv = MulMod::<E>::new(
            i2_times_f_even_minus_f_odd.r.clone(),
            inv,
            eval.next_trace_mask(),
            eval.next_trace_mask(),
        );

        // Evaluate all split operations and collect the two smaller polynomials
        // This performs the actual split operations and produces f0 and f1 polynomials
        let [f0, f1] = Split::new(
            f_even_plus_f_odd,
            i2_times_f_even_plus_f_odd,
            f_even_minus_f_odd,
            i2_times_f_even_minus_f_odd,
            i2_times_f_even_minus_f_odd_times_root_inv,
        )
        .evaluate(&self.rc_lookup_elements, &mut eval);

        // Add split polynomial coefficients to INTT lookup relation for verification
        // This ensures the output values are properly connected to the INTT computation

        eval.add_to_relation(RelationEntry::new(
            &self.intt_lookup_elements,
            -E::EF::from(is_filled.clone()),
            &[f0],
        ));

        eval.add_to_relation(RelationEntry::new(
            &self.intt_lookup_elements,
            -E::EF::from(is_filled.clone()),
            &[f1],
        ));

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
        rc_lookup_elements: &RCLookupElements,
        intt_input_lookup_elements: &INTTInputLookupElements,
        intt_lookup_elements: &INTTLookupElements,
        inv_roots_lookup_elements: &InvRootsLookupElements,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        InteractionClaim,
    ) {
        let log_size = trace[0].domain.log_size();
        let is_filled = trace[1].clone();
        let mut logup_gen = LogupTraceGenerator::new(log_size);

        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let j = trace[2].data[vec_row]; // must have all lanes populated
            let inv_root = trace[3].data[vec_row]; // must have all lanes populated
            let denom: PackedQM31 = inv_roots_lookup_elements.combine(&[j, inv_root]);
            col_gen.write_frac(vec_row, PackedQM31::from(is_filled.data[vec_row]), denom);
        }
        col_gen.finalize_col();

        // input linking
        for col_offset in [4, 5] {
            let mut col_gen = logup_gen.new_col();
            for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                let v = trace[col_offset].data[vec_row]; // must have all lanes populated
                let denom: PackedQM31 = intt_input_lookup_elements.combine(&[v]);
                col_gen.write_frac(vec_row, PackedQM31::from(is_filled.data[vec_row]), denom);
            }
            col_gen.finalize_col();
        }
        // range check
        for col_offset in [7, 9, 11, 13, 15] {
            let mut col_gen = logup_gen.new_col();
            for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                let v = trace[col_offset].data[vec_row]; // must have all lanes populated
                let denom: PackedQM31 = rc_lookup_elements.combine(&[v]);
                col_gen.write_frac(vec_row, PackedQM31::one(), denom);
            }
            col_gen.finalize_col();
        }

        // output linking

        for col_offset in [9, 15] {
            let mut col_gen = logup_gen.new_col();
            for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                let v = trace[col_offset].data[vec_row]; // must have all lanes populated
                let denom: PackedQM31 = intt_lookup_elements.combine(&[v]);
                col_gen.write_frac(vec_row, -PackedQM31::from(is_filled.data[vec_row]), denom);
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
