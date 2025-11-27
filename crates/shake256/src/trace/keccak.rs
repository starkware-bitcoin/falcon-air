#![allow(non_snake_case)]

use crate::constants::N_ROUNDS;
use crate::constants::{N_BYTES_IN_STATE, N_BYTES_IN_U64};
use crate::trace::shake256::apply_keccakf;
use crate::utils::Enabler;
use num_traits::Zero;
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};
use serde::{Deserialize, Serialize};
use stwo_air_utils::trace::component_trace::ComponentTrace;
use stwo_air_utils_derive::{IterMut, ParIterMut, Uninitialized};
use stwo_prover::core::backend::simd::m31::LOG_N_LANES;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::{
    backend::{
        simd::{m31::PackedM31, SimdBackend},
        BackendForChannel,
    },
    channel::Channel,
    fields::qm31::SECURE_EXTENSION_DEGREE,
    pcs::TreeVec,
    vcs::blake2_merkle::Blake2sMerkleChannel,
};

pub const IOTA_RC: [u64; N_ROUNDS + 1] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808A,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808B,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008A,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000A,
    0x0000_0000_8000_808B,
    0x8000_0000_0000_008B,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800A,
    0x8000_0000_8000_000A,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
    0x0000_0000_0000_0000, // Dummy value for lookups
];

const N_KECCAK_LOOKUPS: usize = 2;
const N_KECCAK_ROUND_LOOKUPS: usize = 2 * N_ROUNDS;

const N_COLUMNS: usize = 1 + (N_ROUNDS + 1) * N_BYTES_IN_STATE;
const N_INTERACTION_COLUMNS: usize =
    SECURE_EXTENSION_DEGREE * (N_KECCAK_LOOKUPS + N_KECCAK_ROUND_LOOKUPS).div_ceil(2);

#[derive(Default, Debug)]
pub struct Indexes {
    pub col_index: usize,
}

pub struct InteractionClaimData {
    pub lookup_data: LookupData,
    pub non_padded_length: usize,
}

#[derive(Uninitialized, IterMut, ParIterMut)]
pub struct LookupData {
    pub keccak: [Vec<[PackedM31; N_BYTES_IN_STATE]>; N_KECCAK_LOOKUPS],
    pub keccak_round: [Vec<[PackedM31; N_BYTES_IN_STATE + N_BYTES_IN_U64]>; N_KECCAK_ROUND_LOOKUPS],
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
        mut keccak_packed_input: Vec<[PackedM31; N_BYTES_IN_STATE]>,
        keccak_invocations: usize,
    ) -> (Self, ComponentTrace<N_COLUMNS>, InteractionClaimData)
    where
        SimdBackend: BackendForChannel<Blake2sMerkleChannel>,
    {
        let log_size = std::cmp::max(
            keccak_invocations.next_power_of_two().ilog2() as u32,
            LOG_N_LANES,
        );
        keccak_packed_input.resize(
            1 << (log_size - LOG_N_LANES),
            [PackedM31::zero(); N_BYTES_IN_STATE],
        );
        let enabler_col = Enabler::new(keccak_invocations);

        // Generate lookup data and fill the trace
        let (mut trace, mut lookup_data) = unsafe {
            (
                ComponentTrace::<N_COLUMNS>::uninitialized(log_size),
                LookupData::uninitialized(log_size - LOG_N_LANES),
            )
        };

        (
            trace.par_iter_mut(),
            keccak_packed_input.into_par_iter(),
            lookup_data.par_iter_mut(),
        )
            .into_par_iter()
            .enumerate()
            .for_each(|(row_index, (mut row, mut S, lookup_data))| {
                let mut indexes = Indexes::default();
                let enabler = enabler_col.packed_at(row_index);
                *row[indexes.col_index] = enabler;
                indexes.col_index += 1;

                // ╔════════════════════════════════════╗
                // ║           Initialization           ║
                // ╚════════════════════════════════════╝
                // Initialize the state
                S.iter().for_each(|x| {
                    *row[indexes.col_index] = *x;
                    indexes.col_index += 1;
                });

                // Use the Keccak input state
                *lookup_data.keccak[0] = S;

                // ╔════════════════════════════════════╗
                // ║               Rounds               ║
                // ╚════════════════════════════════════╝
                for round in 0..N_ROUNDS {
                    // Emit the current round state
                    *lookup_data.keccak_round[2 * round] = IOTA_RC[round]
                        .to_le_bytes()
                        .into_iter()
                        .map(|x| PackedM31::from(M31::from(x as u32)))
                        .chain(S.iter().cloned())
                        .collect::<Vec<_>>()
                        .try_into()
                        .unwrap();

                    apply_keccakf(&mut S, round);
                    S.iter().for_each(|x| {
                        *row[indexes.col_index] = *x;
                        indexes.col_index += 1;
                    });

                    // Emit the next round state
                    *lookup_data.keccak_round[2 * round + 1] = IOTA_RC[round + 1]
                        .to_le_bytes()
                        .into_iter()
                        .map(|x| PackedM31::from(M31::from(x as u32)))
                        .chain(S.iter().cloned())
                        .collect::<Vec<_>>()
                        .try_into()
                        .unwrap();

                    if round == N_ROUNDS - 1 {
                        // Emit the Keccak output state
                        *lookup_data.keccak[1] = S;
                    }
                }
            });

        let claim = Self { log_size };
        (
            claim,
            trace,
            InteractionClaimData {
                lookup_data,
                non_padded_length: keccak_invocations,
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::Claim;
    use crate::constants::N_BYTES_IN_STATE;
    use crate::utils::keccak_f1600;
    use stwo_prover::core::{
        backend::simd::m31::{PackedM31, N_LANES},
        fields::m31::M31,
    };

    #[test]
    fn keccak_compare_to_reference() {
        // Build one packed Keccak input state (200 bytes), with 16 SIMD lanes.
        let input_state: [PackedM31; N_BYTES_IN_STATE] = std::array::from_fn(|i| {
            PackedM31::from_array(std::array::from_fn(|lane| {
                let v: u32 = ((i as u32).wrapping_mul(37)).wrapping_add((lane as u32) * 13) & 0xFF;
                M31::from(v)
            }))
        });

        // Compute the expected final state with the reference Keccak-f[1600].
        let mut expected = input_state.clone();
        keccak_f1600(&mut expected);

        // Feed the same input to the Keccak trace generator.
        let keccak_invocations = N_LANES;
        let (_claim, _trace, interaction) =
            Claim::generate_trace(vec![input_state], keccak_invocations);

        // The final state is stored in lookup_data.keccak[1]
        let got = &interaction.lookup_data.keccak[1][0];

        for i in 0..N_BYTES_IN_STATE {
            assert_eq!(
                got[i].to_array(),
                expected[i].to_array(),
                "Mismatch at byte {}",
                i
            );
        }
    }
}
