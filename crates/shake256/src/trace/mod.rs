pub mod chi_8_8_8;
pub mod keccak;
pub mod keccak_round;
pub mod rc_7_7_7;
pub mod shake256;
pub mod xor_8_8;
pub mod xor_8_8_8;

use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use serde::{Deserialize, Serialize};
use stwo_prover::core::{
    backend::{
        simd::m31::{PackedM31, N_LANES},
        simd::SimdBackend,
        BackendForChannel,
    },
    channel::Channel,
    fields::m31::M31,
    pcs::TreeVec,
    poly::{circle::CircleEvaluation, BitReversedOrder},
    vcs::blake2_merkle::Blake2sMerkleChannel,
};

use crate::{
    constants::{N_BYTES_IN_MESSAGE, N_BYTES_IN_STATE, N_BYTES_IN_U64, N_ROUNDS},
    interaction::InteractionClaimData,
};

#[derive(Serialize, Deserialize, Debug)]
pub struct Claim {
    pub shake256: shake256::Claim,
    pub keccak: keccak::Claim,
    pub keccak_round: keccak_round::Claim,
    pub xor_8_8_8: xor_8_8_8::Claim,
    pub chi_8_8_8: chi_8_8_8::Claim,
    pub xor_8_8: xor_8_8::Claim,
    pub rc_7_7_7: rc_7_7_7::Claim,
}

impl Claim {
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let trees = vec![
            self.shake256.log_sizes(),
            self.keccak.log_sizes(),
            self.keccak_round.log_sizes(),
            self.xor_8_8_8.log_sizes(),
            self.chi_8_8_8.log_sizes(),
            self.xor_8_8.log_sizes(),
            self.rc_7_7_7.log_sizes(),
        ];
        TreeVec::concat_cols(trees.into_iter())
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.shake256.mix_into(channel);
        self.keccak.mix_into(channel);
        self.keccak_round.mix_into(channel);
        self.xor_8_8_8.mix_into(channel);
        self.chi_8_8_8.mix_into(channel);
        self.xor_8_8.mix_into(channel);
        self.rc_7_7_7.mix_into(channel);
    }

    pub fn generate_trace(
        messages: Vec<[u8; N_BYTES_IN_MESSAGE]>,
    ) -> (
        Self,
        impl IntoIterator<Item = CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        InteractionClaimData,
    )
    where
        SimdBackend: BackendForChannel<Blake2sMerkleChannel>,
    {
        // Generate shake256 trace
        let (shake256_claim, shake256_trace, shake256_interaction_claim_data, keccak_invocations) =
            shake256::Claim::generate_trace(messages);

        // Generate keccak trace: keep even keccak columns (inputs before permutation)
        let filtered_arrays_keccak: Vec<&Vec<[PackedM31; N_BYTES_IN_STATE]>> =
            shake256_interaction_claim_data
                .lookup_data
                .keccak
                .iter()
                .enumerate()
                .filter(|(i, _)| *i % 2 == 0)
                .map(|(_, v)| v)
                .collect();
        let keccak_input = repack_packed_inputs(&filtered_arrays_keccak);
        let (keccak_claim, keccak_trace, keccak_interaction_claim_data) =
            keccak::Claim::generate_trace(keccak_input, keccak_invocations);

        // Generate keccak_round trace: keep even keccak_round columns (inputs before permutation)
        let filtered_arrays_keccak_round: Vec<(
            usize,
            &Vec<[PackedM31; N_BYTES_IN_STATE + N_BYTES_IN_U64]>,
        )> = keccak_interaction_claim_data
            .lookup_data
            .keccak_round
            .iter()
            .enumerate()
            .filter(|(i, _)| *i % 2 == 0)
            .map(|(i, v)| (i / 2, v))
            .collect();
        // We add the round index as a column
        let keccak_round_columns: Vec<Vec<[PackedM31; N_BYTES_IN_STATE + 1]>> =
            filtered_arrays_keccak_round
                .iter()
                .map(|(round_idx, column)| convert_keccak_round_column(*round_idx, column))
                .collect();
        let keccak_round_column_refs: Vec<&Vec<[PackedM31; N_BYTES_IN_STATE + 1]>> =
            keccak_round_columns.iter().collect();
        // Repack as for keccak inputs
        let keccak_round_input = repack_packed_inputs(&keccak_round_column_refs);
        let (keccak_round_claim, keccak_round_trace, keccak_round_interaction_claim_data) =
            keccak_round::Claim::generate_trace(keccak_round_input, N_ROUNDS * keccak_invocations);

        // Generate traces for providers
        let requested_xor_8_8_8 = keccak_round_interaction_claim_data
            .lookup_data
            .xor_8_8_8
            .par_iter()
            .map(|v| v.as_slice());
        let requested_chi_8_8_8 = keccak_round_interaction_claim_data
            .lookup_data
            .chi_8_8_8
            .par_iter()
            .map(|v| v.as_slice());
        let requested_xor_8_8 = keccak_round_interaction_claim_data
            .lookup_data
            .xor_8_8
            .par_iter()
            .map(|v| v.as_slice());
        let requested_rc_7_7_7 = keccak_round_interaction_claim_data
            .lookup_data
            .rc_7_7_7
            .par_iter()
            .map(|v| v.as_slice());
        let (xor_8_8_8_claim, xor_8_8_8_trace, xor_8_8_8_interaction_claim_data) =
            xor_8_8_8::Claim::generate_trace(requested_xor_8_8_8);
        let (chi_8_8_8_claim, chi_8_8_8_trace, chi_8_8_8_interaction_claim_data) =
            chi_8_8_8::Claim::generate_trace(requested_chi_8_8_8);
        let (xor_8_8_claim, xor_8_8_trace, xor_8_8_interaction_claim_data) =
            xor_8_8::Claim::generate_trace(requested_xor_8_8);
        let (rc_7_7_7_claim, rc_7_7_7_trace, rc_7_7_7_interaction_claim_data) =
            rc_7_7_7::Claim::generate_trace(requested_rc_7_7_7);

        // Gather all lookup data
        let interaction_claim_data = InteractionClaimData {
            shake256: shake256_interaction_claim_data,
            keccak: keccak_interaction_claim_data,
            keccak_round: keccak_round_interaction_claim_data,
            xor_8_8_8: xor_8_8_8_interaction_claim_data,
            chi_8_8_8: chi_8_8_8_interaction_claim_data,
            xor_8_8: xor_8_8_interaction_claim_data,
            rc_7_7_7: rc_7_7_7_interaction_claim_data,
        };

        // Combine all traces
        let trace = shake256_trace
            .to_evals()
            .into_iter()
            .chain(keccak_trace.to_evals())
            .chain(keccak_round_trace.to_evals())
            .chain(xor_8_8_8_trace)
            .chain(chi_8_8_8_trace)
            .chain(xor_8_8_trace)
            .chain(rc_7_7_7_trace);

        (
            Self {
                shake256: shake256_claim,
                keccak: keccak_claim,
                keccak_round: keccak_round_claim,
                xor_8_8_8: xor_8_8_8_claim,
                chi_8_8_8: chi_8_8_8_claim,
                xor_8_8: xor_8_8_claim,
                rc_7_7_7: rc_7_7_7_claim,
            },
            trace,
            interaction_claim_data,
        )
    }
}

// Repack: 11 Vec<PackedStates> (even) -> 11 Vec<States> (unpack) -> 1 Vec<interleaved States> -> repack to PackedStates
fn repack_packed_inputs<const N: usize>(cols: &[&Vec<[PackedM31; N]>]) -> Vec<[PackedM31; N]> {
    if cols.is_empty() {
        return Vec::new();
    }
    let n_cols = cols.len();
    let rows = cols.iter().map(|v| v.len()).max().unwrap_or(0);

    let mut result: Vec<[PackedM31; N]> = Vec::with_capacity(rows * n_cols);
    let mut buf: Vec<[M31; N]> = Vec::with_capacity(N_LANES);

    for s in 0..(rows * N_LANES) {
        let row_idx = s / N_LANES;
        let lane_idx = s % N_LANES;
        for col in cols {
            if row_idx >= col.len() {
                continue;
            }
            let packed_state = &col[row_idx];
            let state: [M31; N] = std::array::from_fn(|b| packed_state[b].to_array()[lane_idx]);
            buf.push(state);
            if buf.len() == N_LANES {
                let packed: [PackedM31; N] = std::array::from_fn(|b| {
                    let lanes: [M31; N_LANES] = std::array::from_fn(|lane| buf[lane][b]);
                    PackedM31::from_array(lanes)
                });
                result.push(packed);
                buf.clear();
            }
        }
    }
    debug_assert!(buf.is_empty());
    result
}

fn convert_keccak_round_column(
    round_idx: usize,
    column: &Vec<[PackedM31; N_BYTES_IN_STATE + N_BYTES_IN_U64]>,
) -> Vec<[PackedM31; N_BYTES_IN_STATE + 1]> {
    debug_assert!(round_idx < N_ROUNDS);
    column
        .iter()
        .map(|row| {
            let index_packed = PackedM31::from_array([M31::from(round_idx as u32); N_LANES]);
            std::array::from_fn(|i| {
                if i < N_BYTES_IN_STATE {
                    row[N_BYTES_IN_U64 + i]
                } else {
                    index_packed
                }
            })
        })
        .collect()
}
