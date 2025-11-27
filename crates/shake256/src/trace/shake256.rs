#![allow(non_snake_case)]

use crate::{
    constants::{
        DELIMITED_SUFFIX, FINAL_BIT, N_BYTES_IN_MESSAGE, N_BYTES_IN_OUTPUT, N_BYTES_IN_RATE,
        N_BYTES_IN_STATE, N_ROUNDS, N_SQUEEZING,
    },
    interaction::relations::RELATION_SIZE_SHAKE256,
    utils::{keccak_f1600, keccak_f1600_round, Enabler},
};
use num_traits::Zero;
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};
use serde::{Deserialize, Serialize};
use stwo_air_utils::trace::component_trace::ComponentTrace;
use stwo_air_utils_derive::{IterMut, ParIterMut, Uninitialized};
use stwo_prover::core::{
    backend::{
        simd::{
            m31::{PackedM31, LOG_N_LANES, N_LANES},
            SimdBackend,
        },
        BackendForChannel,
    },
    channel::Channel,
    fields::{m31::M31, qm31::SECURE_EXTENSION_DEGREE},
    pcs::TreeVec,
    vcs::blake2_merkle::Blake2sMerkleChannel,
};

const N_SHAKE256_LOOKUPS: usize = 2;
// We record Keccak states as (pre, post) pairs: one pair for absorption, and
// one pair per squeezing permutation (for bookkeeping). This yields
// 2 + 2*N_SQUEEZING lookups.
pub const N_KECCAK_LOOKUPS: usize = 2 * N_SQUEEZING;
const N_COLUMNS: usize = 1 + N_BYTES_IN_MESSAGE + N_BYTES_IN_STATE * N_KECCAK_LOOKUPS / 2;
const N_INTERACTION_COLUMNS: usize =
    SECURE_EXTENSION_DEGREE * (N_SHAKE256_LOOKUPS + N_KECCAK_LOOKUPS).div_ceil(2);

#[derive(Default, Debug)]
pub struct Indexes {
    pub col_index: usize,
    pub keccak_index: usize,
}

pub struct InteractionClaimData {
    pub lookup_data: LookupData,
    pub non_padded_length: usize,
}

#[derive(Uninitialized, IterMut, ParIterMut)]
pub struct LookupData {
    pub shake256: [Vec<[PackedM31; RELATION_SIZE_SHAKE256]>; N_SHAKE256_LOOKUPS],
    pub keccak: [Vec<[PackedM31; N_BYTES_IN_STATE]>; N_KECCAK_LOOKUPS],
}

#[derive(Copy, Clone, Default, Serialize, Deserialize, Debug)]
pub struct Claim {
    pub log_size: u32,
}

impl Claim {
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let trace = vec![self.log_size; N_COLUMNS];
        let interaction_trace = vec![self.log_size; N_INTERACTION_COLUMNS];
        TreeVec::new(vec![vec![], trace, interaction_trace])
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    pub fn generate_trace(
        messages: Vec<[u8; N_BYTES_IN_MESSAGE]>,
    ) -> (Self, ComponentTrace<N_COLUMNS>, InteractionClaimData, usize)
    where
        SimdBackend: BackendForChannel<Blake2sMerkleChannel>,
    {
        let messages_len = messages.len();
        let log_size = std::cmp::max(messages_len.next_power_of_two().ilog2() as u32, LOG_N_LANES);
        let keccak_invocations = messages_len * N_KECCAK_LOOKUPS / 2;
        let enabler_col = Enabler::new(messages_len);

        // Generate lookup data and fill the trace
        let (mut trace, mut lookup_data) = unsafe {
            (
                ComponentTrace::<N_COLUMNS>::uninitialized(log_size),
                LookupData::uninitialized(log_size - LOG_N_LANES),
            )
        };

        let packed_inputs: Vec<[PackedM31; N_BYTES_IN_MESSAGE]> = messages
            .iter()
            .chain(std::iter::repeat(&[0u8; N_BYTES_IN_MESSAGE]))
            .take(1 << log_size)
            .array_chunks::<N_LANES>()
            .map(|chunk| {
                std::array::from_fn(|x| {
                    PackedM31::from_array(std::array::from_fn(|y| M31::from(chunk[y][x] as u32)))
                })
            })
            .collect();

        (
            trace.par_iter_mut(),
            packed_inputs.into_par_iter(),
            lookup_data.par_iter_mut(),
        )
            .into_par_iter()
            .enumerate()
            .for_each(|(row_index, (mut row, message, lookup_data))| {
                let mut indexes = Indexes::default();
                let enabler = enabler_col.packed_at(row_index);

                *row[indexes.col_index] = enabler;
                indexes.col_index += 1;

                // ╔════════════════════════════════════╗
                // ║     Padding and Initialization     ║
                // ╚════════════════════════════════════╝
                let mut S: [PackedM31; N_BYTES_IN_STATE] = std::array::from_fn(|i| {
                    if i < N_BYTES_IN_MESSAGE {
                        let x = message[i];
                        *row[indexes.col_index] = x;
                        indexes.col_index += 1;
                        x
                    } else {
                        PackedM31::zero()
                    }
                });

                // Use the SHAKE256 message (same lookup for input and output requires padding)
                *lookup_data.shake256[0] = std::array::from_fn(|i| {
                    if i < N_BYTES_IN_MESSAGE {
                        S[i]
                    } else {
                        PackedM31::zero()
                    }
                });

                // Add the delimited suffix and final bit
                S[N_BYTES_IN_MESSAGE] = PackedM31::from(M31::from(DELIMITED_SUFFIX));
                S[N_BYTES_IN_RATE - 1] = PackedM31::from(M31::from(FINAL_BIT));

                // ╔════════════════════════════════════╗
                // ║              Absorbing             ║
                // ╚════════════════════════════════════╝
                *lookup_data.keccak[indexes.keccak_index] = S;
                indexes.keccak_index += 1;

                keccak_f1600(&mut S);
                S.iter().for_each(|x| {
                    *row[indexes.col_index] = *x;
                    indexes.col_index += 1;
                });

                // Record post-absorption state (used for first output block).
                *lookup_data.keccak[indexes.keccak_index] = S;
                indexes.keccak_index += 1;

                // ╔════════════════════════════════════╗
                // ║              Squeezing             ║
                // ╚════════════════════════════════════╝
                let mut Z = [PackedM31::zero(); N_BYTES_IN_OUTPUT];

                // First block: copy directly from the current state S.
                for j in 0..N_BYTES_IN_RATE {
                    Z[j] = S[j];
                }

                // Remaining blocks: each produced after another permutation.
                for i in 1..N_SQUEEZING {
                    // Pre-permutation state
                    *lookup_data.keccak[indexes.keccak_index] = S;
                    indexes.keccak_index += 1;

                    keccak_f1600(&mut S);
                    S.iter().enumerate().for_each(|(j, x)| {
                        if j < N_BYTES_IN_RATE {
                            Z[i * N_BYTES_IN_RATE + j] = *x;
                        }
                        *row[indexes.col_index] = *x;
                        indexes.col_index += 1;
                    });

                    *lookup_data.keccak[indexes.keccak_index] = S;
                    indexes.keccak_index += 1;
                }
                *lookup_data.shake256[1] = Z;
            });

        let claim = Self { log_size };
        (
            claim,
            trace,
            InteractionClaimData {
                lookup_data,
                non_padded_length: messages_len,
            },
            keccak_invocations,
        )
    }
}

/// Applies a single Keccak-f[1600] round in place.
pub(crate) fn apply_keccakf(S: &mut [PackedM31; N_BYTES_IN_STATE], round: usize) {
    debug_assert!(round < N_ROUNDS);
    keccak_f1600_round(S, round);
}
