use rayon::iter::{IntoParallelIterator, ParallelIterator};
use stwo_air_utils::trace::component_trace::ComponentTrace;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_prover::core::{
    backend::{simd::SimdBackend, BackendForChannel},
    fields::m31::M31,
    vcs::blake2_merkle::Blake2sMerkleChannel,
};

use crate::utils::pack_column;

pub const N_INPUT_COLUMNS: usize = 3;
const N_OUTPUT_COLUMNS: usize = 0;
pub const N_TRACE_COLUMNS: usize = N_INPUT_COLUMNS + N_OUTPUT_COLUMNS;
pub const N_BITS_IN_LIMB: usize = 7;
const COLUMN_IDS: [&str; N_TRACE_COLUMNS] = ["rc_7_7_7_a", "rc_7_7_7_b", "rc_7_7_7_c"];

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
    let a_packed = pack_column(n_rows, |idx| M31::from((idx as u32) & 0x7f));
    let b_packed = pack_column(n_rows, |idx| M31::from(((idx as u32) >> 7) & 0x7f));
    let c_packed = pack_column(n_rows, |idx| M31::from(((idx as u32) >> 14) & 0x7f));

    (
        trace.par_iter_mut(),
        a_packed.into_par_iter(),
        b_packed.into_par_iter(),
        c_packed.into_par_iter(),
    )
        .into_par_iter()
        .for_each(|(mut row, a, b, c)| {
            *row[0] = a.into();
            *row[1] = b.into();
            *row[2] = c.into();
        });

    (trace, column_ids, vec![log_size; N_TRACE_COLUMNS])
}
