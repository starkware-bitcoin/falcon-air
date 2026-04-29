use rayon::iter::{IntoParallelIterator, ParallelIterator};
use stwo_air_utils::trace::component_trace::ComponentTrace;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::{
    backend::{simd::SimdBackend, BackendForChannel},
    vcs::blake2_merkle::Blake2sMerkleChannel,
};

use crate::utils::pack_column;

pub const N_INPUT_COLUMNS: usize = 2;
const N_OUTPUT_COLUMNS: usize = 1;
pub const N_TRACE_COLUMNS: usize = N_INPUT_COLUMNS + N_OUTPUT_COLUMNS;
pub const N_BITS_IN_LIMB: usize = 8;
const COLUMN_IDS: [&str; N_TRACE_COLUMNS] = ["chi_8_8_b", "chi_8_8_c", "chi_8_8_res"];

/// Preprocessed table for the chi sub-step: maps (b, c) -> (!b) & c on 8-bit limbs.
/// Used to chain chi_8_8_8(a, b, c) = a ^ ((!b) & c) as
///     chi_8_8(b, c) -> t   then   xor_8_8(a, t) -> out
/// log_size = 16 (vs 24 for the previous chi_8_8_8 table, a 256x reduction).
pub fn generate_preprocessed_trace() -> (
    ComponentTrace<N_TRACE_COLUMNS>,
    Vec<PreProcessedColumnId>,
    Vec<u32>,
)
where
    SimdBackend: BackendForChannel<Blake2sMerkleChannel>,
{
    let log_size = (N_BITS_IN_LIMB * N_INPUT_COLUMNS) as u32;
    let mut trace = unsafe { ComponentTrace::<N_TRACE_COLUMNS>::uninitialized(log_size) };
    let column_ids = COLUMN_IDS
        .iter()
        .map(|id| PreProcessedColumnId { id: id.to_string() })
        .collect();

    let n_rows = 1usize << (log_size as usize);
    let b_packed = pack_column(n_rows, |idx| M31::from((idx as u32) & 0xFF));
    let c_packed = pack_column(n_rows, |idx| M31::from((idx as u32 >> 8) & 0xFF));
    let res_packed = pack_column(n_rows, |idx| {
        let b = (idx as u32) & 0xFF;
        let c = ((idx as u32) >> 8) & 0xFF;
        let nb = (!b) & 0xFF;
        M31::from(nb & c)
    });

    (
        trace.par_iter_mut(),
        b_packed.into_par_iter(),
        c_packed.into_par_iter(),
        res_packed.into_par_iter(),
    )
        .into_par_iter()
        .for_each(|(mut row, b, c, res)| {
            *row[0] = b.into();
            *row[1] = c.into();
            *row[2] = res.into();
        });

    (trace, column_ids, vec![log_size; N_TRACE_COLUMNS])
}
