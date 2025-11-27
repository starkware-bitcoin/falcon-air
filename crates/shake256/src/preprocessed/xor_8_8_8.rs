use rayon::iter::{IntoParallelIterator, ParallelIterator};
use stwo_air_utils::trace::component_trace::ComponentTrace;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::{
    backend::{simd::SimdBackend, BackendForChannel},
    vcs::blake2_merkle::Blake2sMerkleChannel,
};

use crate::utils::pack_column;

pub const N_INPUT_COLUMNS: usize = 3;
const N_OUTPUT_COLUMNS: usize = 1;
pub const N_TRACE_COLUMNS: usize = N_INPUT_COLUMNS + N_OUTPUT_COLUMNS;
pub const N_BITS_IN_LIMB: usize = 8;
const COLUMN_IDS: [&str; N_TRACE_COLUMNS] =
    ["xor_8_8_8_a", "xor_8_8_8_b", "xor_8_8_8_c", "xor_8_8_8_res"];

pub fn generate_preprocessed_trace() -> (
    ComponentTrace<N_TRACE_COLUMNS>,
    Vec<PreProcessedColumnId>,
    Vec<u32>,
)
where
    SimdBackend: BackendForChannel<Blake2sMerkleChannel>,
{
    // Initialize trace and ids
    let log_size = (N_BITS_IN_LIMB * N_INPUT_COLUMNS) as u32;
    let mut trace = unsafe { ComponentTrace::<N_TRACE_COLUMNS>::uninitialized(log_size) };
    let column_ids = COLUMN_IDS
        .iter()
        .map(|id| PreProcessedColumnId { id: id.to_string() })
        .collect();

    // Generate packed columns
    let n_rows = 1usize << (log_size as usize);
    let a_packed = pack_column(n_rows, |idx| M31::from((idx as u32) & 0xFF));
    let b_packed = pack_column(n_rows, |idx| M31::from((idx as u32 >> 8) & 0xFF));
    let c_packed = pack_column(n_rows, |idx| M31::from((idx as u32 >> 16) & 0xFF));
    let x_packed = pack_column(n_rows, |idx| {
        let a = (idx & 0xFF) as u32;
        let b = ((idx >> 8) as u32) & 0xFF;
        let c = ((idx >> 16) as u32) & 0xFF;
        M31::from(a ^ b ^ c)
    });

    // Fill trace
    (
        trace.par_iter_mut(),
        a_packed.into_par_iter(),
        b_packed.into_par_iter(),
        c_packed.into_par_iter(),
        x_packed.into_par_iter(),
    )
        .into_par_iter()
        .for_each(|(mut row, a, b, c, x)| {
            *row[0] = a.into();
            *row[1] = b.into();
            *row[2] = c.into();
            *row[3] = x.into();
        });

    (trace, column_ids, vec![log_size; N_TRACE_COLUMNS])
}
