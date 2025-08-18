use num_traits::{One, Zero};
use stwo::{
    core::{
        ColumnVec,
        channel::Channel,
        fields::{m31::M31, qm31::SecureField},
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
    POLY_LOG_SIZE,
    ntts::SQ1,
    zq::{Q, add::AddMod, mul::MulMod, range_check, sub::SubMod},
};

#[derive(Debug, Clone)]
pub struct Claim {
    /// The log base 2 of the trace size
    pub log_size: u32,
}

impl Claim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    pub fn gen_trace(
        &self,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Vec<M31>,
    ) {
        let mut poly = (1..17).collect::<Vec<_>>();
        bit_reverse(&mut poly);
        let trace = poly
            .chunks(2)
            .flat_map(|chunk| {
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
                .into_iter()
                .map(M31::from_u32_unchecked)
                .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        let domain = CanonicCoset::new(self.log_size).circle_domain();
        let bit_reversed_0 = bit_reverse_index(0, self.log_size);
        let trace = trace
            .into_iter()
            .map(|val| {
                let mut col = vec![M31::zero(); 1 << self.log_size];
                col[bit_reversed_0] = val;
                col
            })
            .collect::<Vec<_>>();
        let mut remainders = vec![];
        for coeff in 0..(1 << (POLY_LOG_SIZE - 1)) {
            for col in [3, 5, 7] {
                remainders.push(trace[coeff * 8 + col].clone());
            }
        }
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
            remainders.into_iter().flatten().collect(),
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
                f0_plus_f1_times_sq1_remainder,
            )
            .evaluate(&self.lookup_elements, &mut eval);

            SubMod::new(
                f0,
                f1_times_sq1_remainder,
                f0_minus_f1_times_sq1_quotient,
                f0_minus_f1_times_sq1_remainder,
            )
            .evaluate(&self.lookup_elements, &mut eval);
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

        for poly_coeff in 0..(1 << (POLY_LOG_SIZE - 1)) {
            for col in [3, 5, 7] {
                let mut col_gen = logup_gen.new_col();
                for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                    // only the packed row that contains the hot lane contributes
                    let result_packed = trace[poly_coeff * 8 + col].data[vec_row];
                    // denom per-lane from the actual packed remainder
                    let denom: PackedQM31 = lookup_elements.combine(&[result_packed]);
                    col_gen.write_frac(vec_row, PackedQM31::one(), denom);
                }
                col_gen.finalize_col();
            }
        }

        let (interaction_trace, claimed_sum) = logup_gen.finalize_last();
        (interaction_trace, InteractionClaim { claimed_sum })
    }
}

/// Type alias for the modular addition component.
pub type Component = FrameworkComponent<Eval>;
