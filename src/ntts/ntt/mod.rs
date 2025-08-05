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
    zq::{
        Q,
        add::{ADD_COL, AddMod},
        mul::{MUL_COL, MulMod},
        range_check,
        sub::{SUB_COL, SubMod},
    },
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
    /// [preprocessed_trace, trace, interaction_trace]
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let trace_log_sizes = vec![self.log_size];
        let interaction_log_sizes = vec![self.log_size; SECURE_EXTENSION_DEGREE];
        TreeVec::new(vec![vec![], trace_log_sizes, interaction_log_sizes])
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    pub fn gen_trace(
        &self,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Vec<Vec<M31>>,
    ) {
        let mut poly = (1..POLY_SIZE + 1).collect::<Vec<_>>();
        // bit reverse the polynomial so it's directly in the correct order for butterfly
        bit_reverse(&mut poly);
        let mut remainders = vec![vec![]; 3];
        let mut flat_remainders = vec![];
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

                remainders[MUL_COL].push(f1_times_sq1_remainder);
                remainders[ADD_COL].push(f0_plus_f1_times_sq1_remainder);
                remainders[SUB_COL].push(f0_minus_f1_times_sq1_remainder);
                flat_remainders.extend([
                    f1_times_sq1_remainder,
                    f0_plus_f1_times_sq1_remainder,
                    f0_minus_f1_times_sq1_remainder,
                ]);
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

        let mut polys = vec![vec![]; POLY_LOG_SIZE as usize];
        for [_, _, _, _, _, left, _, right] in trace.iter() {
            polys[0].push(vec![*left, *right]);
        }
        let mut trace = trace.into_flattened();

        for i in 1..POLY_LOG_SIZE as usize {
            for coeffs in polys[i - 1].clone().chunks_exact(2) {
                let left = &coeffs[0];
                let right = &coeffs[1];
                let mut merged_poly = vec![];
                for (j, (coeff_left, coeff_right)) in left.iter().zip(right.iter()).enumerate() {
                    let root = ROOTS[i][2 * j];
                    let root_times_f1_quotient = (*coeff_right * root) / Q;
                    let root_times_f1_remainder = (*coeff_right * root) % Q;

                    trace.push(root_times_f1_quotient);
                    trace.push(root_times_f1_remainder);
                    remainders[MUL_COL].push(root_times_f1_remainder);

                    let f0_plus_root_times_f1_quotient =
                        (*coeff_left + root_times_f1_remainder) / Q;
                    let f0_plus_root_times_f1_remainder =
                        (*coeff_left + root_times_f1_remainder) % Q;

                    trace.push(f0_plus_root_times_f1_quotient);
                    trace.push(f0_plus_root_times_f1_remainder);
                    remainders[ADD_COL].push(f0_plus_root_times_f1_remainder);

                    let f0_minus_root_times_f1_borrow =
                        (*coeff_left < root_times_f1_remainder) as u32;
                    let f0_minus_root_times_f1_remainder =
                        (*coeff_left + f0_minus_root_times_f1_borrow * Q - root_times_f1_remainder)
                            % Q;
                    trace.push(f0_minus_root_times_f1_borrow);
                    trace.push(f0_minus_root_times_f1_remainder);
                    remainders[SUB_COL].push(f0_minus_root_times_f1_remainder);
                    flat_remainders.extend([
                        root_times_f1_remainder,
                        f0_plus_root_times_f1_remainder,
                        f0_minus_root_times_f1_remainder,
                    ]);

                    merged_poly.push(f0_plus_root_times_f1_remainder);
                    merged_poly.push(f0_minus_root_times_f1_remainder);
                }
                polys[i].push(merged_poly);
            }
        }
        let trace = trace.into_iter().map(M31).collect::<Vec<_>>();

        let domain = CanonicCoset::new(self.log_size).circle_domain();
        let bit_reversed_0 = bit_reverse_index(0, self.log_size);
        (
            trace
                .into_iter()
                .map(|val| {
                    let mut col = vec![M31::zero(); 1 << self.log_size];
                    col[bit_reversed_0] = val;
                    CircleEvaluation::<SimdBackend, _, BitReversedOrder>::new(
                        domain,
                        BaseColumn::from_iter(col),
                    )
                })
                .collect::<Vec<_>>(),
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

#[derive(Debug, Clone)]
pub struct Eval {
    /// The claim parameters
    pub claim: Claim,
    /// Lookup elements for range checking
    pub lookup_elements: range_check::LookupElements,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.claim.log_size + 1
    }

    fn evaluate<E: stwo_constraint_framework::EvalAtRow>(&self, mut eval: E) -> E {
        let sq1 = E::F::from(M31::from_u32_unchecked(SQ1));
        let mut base_f_ntt = Vec::with_capacity(POLY_SIZE as usize);
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

        let mut poly: Vec<Vec<Vec<E::F>>> = vec![vec![]; POLY_LOG_SIZE as usize];
        poly[0] = base_f_ntt;

        for i in 1..POLY_LOG_SIZE as usize {
            for coeffs in poly[i - 1].clone().chunks_exact(2) {
                let mut merges = MergeNTT::default();
                let left = &coeffs[0];
                let right = &coeffs[1];
                for (j, (coeff_left, coeff_right)) in left.iter().zip(right.iter()).enumerate() {
                    let root = ROOTS[i][2 * j];
                    let root_times_f1 = MulMod::<E>::new(
                        coeff_right.clone(),
                        E::F::from(M31(root)),
                        eval.next_trace_mask(),
                        eval.next_trace_mask(),
                    );
                    let f0_plus_root_times_f1 = AddMod::<E>::new(
                        coeff_left.clone(),
                        root_times_f1.r.clone(),
                        eval.next_trace_mask(),
                        eval.next_trace_mask(),
                    );
                    let f0_minus_root_times_f1 = SubMod::<E>::new(
                        coeff_left.clone(),
                        root_times_f1.r.clone(),
                        eval.next_trace_mask(),
                        eval.next_trace_mask(),
                    );
                    let merge =
                        Merge::new(root_times_f1, f0_plus_root_times_f1, f0_minus_root_times_f1);
                    merges.push(merge);
                }
                let merged_poly = MergeNTT::evaluate(merges, &self.lookup_elements, &mut eval);
                poly[i].push(merged_poly);
            }
        }

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

        // Interaction trace for the remainder
        let first_ntt_size = 1 << (POLY_LOG_SIZE - 1);
        for operation_elemnt_index in 0..first_ntt_size {
            for col in [3, 5, 7] {
                let mut col_gen = logup_gen.new_col();
                for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                    // in the first part of the trace each element is 8 columns wide
                    let result_packed = trace[operation_elemnt_index * 8 + col].data[vec_row];

                    // Create the denominator using the lookup elements
                    let denom: PackedQM31 = lookup_elements.combine(&[result_packed]);

                    // The numerator is 1 (we want to check that remainder is in the range)
                    let numerator = PackedQM31::one();

                    col_gen.write_frac(vec_row, numerator, denom);
                }
                col_gen.finalize_col();
            }
        }

        let offset = first_ntt_size * 8 + 1;
        for col in (offset..trace.len()).step_by(2) {
            let mut col_gen = logup_gen.new_col();
            for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                // in the first part of the trace each element is 8 columns wide
                let result_packed = trace[col].data[vec_row];

                // Create the denominator using the lookup elements
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

/// Type alias for the modular addition component.
pub type Component = FrameworkComponent<Eval>;
