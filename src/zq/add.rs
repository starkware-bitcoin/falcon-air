use num_traits::One;
use rand::Rng;
use stwo::{
    core::{
        ColumnVec,
        fields::{m31::M31, qm31::QM31},
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

pub struct Eval {
    pub log_size: u32,
    pub lookup_elements: super::range_check::LookupElements,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: stwo_constraint_framework::EvalAtRow>(&self, mut eval: E) -> E {
        let a = eval.next_trace_mask();
        let b = eval.next_trace_mask();
        let quotient = eval.next_trace_mask();
        let remainder = eval.next_trace_mask();

        eval.add_constraint(
            a + b - quotient * E::F::from(M31::from_u32_unchecked(Q)) - remainder.clone(),
        );
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            E::EF::one(),
            &[remainder],
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

pub fn gen_interaction_trace(
    trace: &ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    lookup_elements: &super::range_check::LookupElements,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    QM31,
) {
    let log_size = trace[0].domain.log_size();
    let mut logup_gen = LogupTraceGenerator::new(log_size);
    let mut col_gen = logup_gen.new_col();

    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        // Get the result value from the trace (column 2)
        let result_packed = trace[2].data[vec_row];

        // Create the denominator using the lookup elements
        let denom: PackedQM31 = lookup_elements.combine(&[result_packed]);

        // The numerator is 1 (we want to check that result is in the range)
        let numerator = PackedQM31::one();

        col_gen.write_frac(vec_row, numerator, denom);
    }
    col_gen.finalize_col();

    logup_gen.finalize_last()
}

pub fn gen_trace(log_size: u32) -> ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>> {
    let mut rng = rand::thread_rng();
    let a = (0..(1 << log_size))
        .map(|_| rng.gen_range(0..Q))
        .collect::<Vec<_>>();
    let b = (0..(1 << log_size))
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
    let domain = CanonicCoset::new(log_size).circle_domain();
    [a, b, quotient, remainder]
        .into_iter()
        .map(|col| {
            CircleEvaluation::<SimdBackend, _, BitReversedOrder>::new(
                domain,
                BaseColumn::from_iter(col),
            )
        })
        .collect::<Vec<_>>()
}
pub type Component = FrameworkComponent<Eval>;
