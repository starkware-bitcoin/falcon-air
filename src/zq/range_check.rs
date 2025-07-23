use num_traits::{One, Zero};
use stwo::{
    core::{
        ColumnVec,
        fields::{
            m31::{BaseField, M31},
            qm31::QM31,
        },
        poly::circle::CanonicCoset,
    },
    prover::{
        backend::simd::{SimdBackend, column::BaseColumn, m31::LOG_N_LANES, qm31::PackedQM31},
        poly::{BitReversedOrder, circle::CircleEvaluation},
    },
};
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    preprocessed_columns::PreProcessedColumnId, relation,
};

use crate::zq::Q;

pub struct RangeCheck12289;

impl RangeCheck12289 {
    pub fn log_size() -> u32 {
        Q.ilog2() + 1
    }

    pub fn gen_column_simd() -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
        CircleEvaluation::new(
            CanonicCoset::new(Self::log_size()).circle_domain(),
            BaseColumn::from_iter(
                (0..Q)
                    .map(M31)
                    .chain((Q..Q.next_power_of_two()).map(|_| M31::zero())),
            ),
        )
    }

    pub fn id() -> PreProcessedColumnId {
        PreProcessedColumnId {
            id: format!("range_check_{}", Q),
        }
    }
}
relation!(LookupElements, 1);

pub struct Eval {
    pub log_size: u32,
    pub lookup_elements: LookupElements,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let lookup_col_1 = eval.next_trace_mask();

        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            -E::EF::one(),
            &[lookup_col_1],
        ));

        eval.finalize_logup_in_pairs();

        eval
    }
}

pub fn gen_interaction_trace(
    trace: &CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
    lookup_elements: &LookupElements,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    QM31,
) {
    let log_size = trace.domain.log_size();
    let mut logup_gen = LogupTraceGenerator::new(log_size);
    let mut col_gen = logup_gen.new_col();

    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        // Get the result value from the trace (column 2)
        let result_packed = trace.data[vec_row];

        // Create the denominator using the lookup elements
        let denom: PackedQM31 = lookup_elements.combine(&[result_packed]);

        // The numerator is 1 (we want to check that result is in the range)
        let numerator = -PackedQM31::one();

        col_gen.write_frac(vec_row, numerator, denom);
    }
    col_gen.finalize_col();

    logup_gen.finalize_last()
}

pub type Component = FrameworkComponent<Eval>;
