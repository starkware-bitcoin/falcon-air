use num_traits::One;
use rand::Rng;
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

use crate::zq::Q;

// This is a helper function for the prover to generate the trace for the add component
pub struct Claim {
    pub log_size: u32,
}

impl Claim {
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let trace_log_sizes = vec![self.log_size];
        TreeVec::new(vec![vec![], trace_log_sizes, vec![]])
    }
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }
    /// Generates the trace for the add component
    /// Generates 2 random numbers and creates a trace for the add component
    /// returns the columns in this order: a, b, quotient, remainder
    pub fn gen_trace(
        &self,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Vec<M31>,
    ) {
        let mut rng = rand::thread_rng();
        let a = (0..(1 << self.log_size))
            .map(|_| rng.gen_range(0..Q))
            .collect::<Vec<_>>();
        let b = (0..(1 << self.log_size))
            .map(|_| rng.gen_range(0..Q))
            .collect::<Vec<_>>();
        let quotient = a
            .iter()
            .zip(b.iter())
            .map(|(a, b)| M31::from_u32_unchecked((a + b) / Q))
            .collect::<Vec<_>>();
        let remainder = a
            .iter()
            .zip(b.iter())
            .map(|(a, b)| M31::from_u32_unchecked((a + b) % Q))
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
pub struct Eval {
    pub claim: Claim,
    pub lookup_elements: super::range_check::LookupElements,
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
        let quotient = eval.next_trace_mask();
        let remainder = eval.next_trace_mask();

        // this is the constraint for add_mod_12289
        // a + b = quotient * Q + remainder
        eval.add_constraint(
            a + b - quotient * E::F::from(M31::from_u32_unchecked(Q)) - remainder.clone(),
        );
        // Now we need to check that the remainder is in the range [0, Q)
        // We do this by using the range check we defined. Here we increment the multiplicity of
        // this value (remainder) by 1 because we want to range check it and the logup sum has to be exactly 0
        // So here we increment and in the range_check we decrements
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            E::EF::one(),
            &[remainder],
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

pub struct InteractionClaim {
    pub claimed_sum: SecureField,
}
impl InteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }

    pub fn gen_interaction_trace(
        trace: &ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        lookup_elements: &super::range_check::LookupElements,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        InteractionClaim,
    ) {
        let log_size = trace[0].domain.log_size();
        let mut logup_gen = LogupTraceGenerator::new(log_size);
        let mut col_gen = logup_gen.new_col();

        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            // Get the result value from the trace (column 2)
            let result_packed = trace[3].data[vec_row];

            // Create the denominator using the lookup elements
            let denom: PackedQM31 = lookup_elements.combine(&[result_packed]);

            // The numerator is 1 (we want to check that result is in the range)
            let numerator = PackedQM31::one();

            col_gen.write_frac(vec_row, numerator, denom);
        }
        col_gen.finalize_col();

        let (interaction_trace, claimed_sum) = logup_gen.finalize_last();
        (interaction_trace, InteractionClaim { claimed_sum })
    }
}
pub type Component = FrameworkComponent<Eval>;
