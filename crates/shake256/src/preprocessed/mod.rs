pub mod chi_8_8_8;
pub mod rc_7_7_7;
pub mod xor_8_8;
pub mod xor_8_8_8;

use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_prover::core::{
    backend::simd::SimdBackend,
    fields::m31::M31,
    poly::{circle::CircleEvaluation, BitReversedOrder},
};

pub fn generate_preprocessed_trace() -> (
    Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    Vec<PreProcessedColumnId>,
    Vec<u32>,
) {
    let (xor_8_8_trace, xor_8_8_ids, xor_8_8_log_sizes) = xor_8_8::generate_preprocessed_trace();
    let (xor_8_8_8_trace, xor_8_8_8_ids, xor_8_8_8_log_sizes) =
        xor_8_8_8::generate_preprocessed_trace();
    let (chi_8_8_8_trace, chi_8_8_8_ids, chi_8_8_8_log_sizes) =
        chi_8_8_8::generate_preprocessed_trace();
    let (rc_7_7_7_trace, rc_7_7_7_ids, rc_7_7_7_log_sizes) =
        rc_7_7_7::generate_preprocessed_trace();

    let trace = xor_8_8_trace
        .to_evals()
        .into_iter()
        .chain(xor_8_8_8_trace.to_evals())
        .chain(chi_8_8_8_trace.to_evals())
        .chain(rc_7_7_7_trace.to_evals())
        .collect();
    let ids = xor_8_8_ids
        .into_iter()
        .chain(xor_8_8_8_ids)
        .chain(chi_8_8_8_ids)
        .chain(rc_7_7_7_ids)
        .collect();
    let log_sizes = xor_8_8_log_sizes
        .into_iter()
        .chain(xor_8_8_8_log_sizes)
        .chain(chi_8_8_8_log_sizes)
        .chain(rc_7_7_7_log_sizes)
        .collect();

    (trace, ids, log_sizes)
}
