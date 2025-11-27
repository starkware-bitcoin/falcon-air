use std::sync::atomic::{AtomicU32, Ordering};

use rayon::iter::ParallelIterator;
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator};
use rayon::slice::ParallelSlice;
use serde::{Deserialize, Serialize};
use stwo_air_utils_derive::{IterMut, ParIterMut, Uninitialized};
use stwo_prover::core::{
    backend::{
        simd::{
            column::BaseColumn,
            m31::{PackedM31, N_LANES},
            SimdBackend,
        },
        BackendForChannel,
    },
    channel::Channel,
    fields::{m31::M31, qm31::SECURE_EXTENSION_DEGREE},
    pcs::TreeVec,
    poly::{
        circle::{CanonicCoset, CircleEvaluation},
        BitReversedOrder,
    },
    vcs::blake2_merkle::Blake2sMerkleChannel,
};

use crate::preprocessed::chi_8_8_8::{N_BITS_IN_LIMB, N_INPUT_COLUMNS};
use crate::utils::pack_column;

const N_COLUMNS: usize = 1;
const N_INTERACTION_COLUMNS: usize = 1;

pub struct InteractionClaimData {
    pub lookup_data: LookupData,
}

#[derive(Uninitialized, IterMut, ParIterMut)]
pub struct LookupData {
    pub chi_8_8_8: Vec<[PackedM31; 5]>,
}

#[derive(Copy, Clone, Default, Serialize, Deserialize, Debug)]
pub struct Claim {
    pub log_size: u32,
}

impl Claim {
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let trace = vec![self.log_size; N_COLUMNS];
        let interaction_trace =
            vec![self.log_size; SECURE_EXTENSION_DEGREE * N_INTERACTION_COLUMNS];
        TreeVec::new(vec![vec![], trace, interaction_trace])
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    pub fn generate_trace<'a>(
        requested_chi_8_8_8: impl ParallelIterator<Item = &'a [[PackedM31; 4]]>,
    ) -> (
        Self,
        [CircleEvaluation<SimdBackend, M31, BitReversedOrder>; 1],
        InteractionClaimData,
    )
    where
        SimdBackend: BackendForChannel<Blake2sMerkleChannel>,
    {
        let log_size = (N_BITS_IN_LIMB * N_INPUT_COLUMNS) as u32;

        let mults_atomic: Vec<AtomicU32> = (0..1 << log_size).map(|_| AtomicU32::new(0)).collect();

        requested_chi_8_8_8.for_each(|entries| {
            for entry in entries.iter() {
                for lane in 0..N_LANES {
                    let a_val = entry[0].to_array()[lane].0;
                    let b_val = entry[1].to_array()[lane].0;
                    let c_val = entry[2].to_array()[lane].0;
                    let idx = (a_val | (b_val << 8) | (c_val << 16)) as usize;
                    mults_atomic[idx].fetch_add(1, Ordering::Relaxed);
                }
            }
        });

        let mults: Vec<M31> = mults_atomic
            .into_par_iter()
            .map(|atomic| M31(atomic.into_inner()))
            .collect();

        // Build first 4 columns to match preprocessed chi_8_8_8
        let n_rows = 1usize << log_size;
        let a_packed = pack_column(n_rows, |idx| M31::from((idx as u32) & 0xFF));
        let b_packed = pack_column(n_rows, |idx| M31::from(((idx as u32) >> 8) & 0xFF));
        let c_packed = pack_column(n_rows, |idx| M31::from(((idx as u32) >> 16) & 0xFF));
        let x_packed = pack_column(n_rows, |idx| {
            let a = ((idx as u32) & 0xFF) as u32;
            let b = (((idx as u32) >> 8) & 0xFF) as u32;
            let c = (((idx as u32) >> 16) & 0xFF) as u32;
            let nb = (!b) & 0xFF;
            M31::from(a ^ (nb & c))
        });

        // Pack mults into lanes as the last column
        let mults_packed: Vec<PackedM31> = mults
            .par_chunks(N_LANES)
            .map(|chunk| PackedM31::from_array(chunk.try_into().unwrap()))
            .collect();

        let chi_8_8_8: Vec<[PackedM31; 5]> = a_packed
            .into_par_iter()
            .zip(b_packed.into_par_iter())
            .zip(c_packed.into_par_iter())
            .zip(x_packed.into_par_iter())
            .zip(mults_packed.into_par_iter())
            .map(|((((a, b), c), x), mult)| [a, b, c, x, mult])
            .collect();

        let domain = CanonicCoset::new(log_size).circle_domain();
        (
            Self { log_size },
            [CircleEvaluation::<SimdBackend, M31, BitReversedOrder>::new(
                domain,
                BaseColumn::from_iter(mults),
            )],
            InteractionClaimData {
                lookup_data: LookupData { chi_8_8_8 },
            },
        )
    }
}
