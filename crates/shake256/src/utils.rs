use crate::constants::{N_BYTES_IN_STATE, N_BYTES_IN_U64, N_LANES_SHAKE256, N_ROUNDS};
use itertools::Itertools;
use num_traits::{One, Zero};
use stwo_prover::core::backend::simd::m31::{PackedM31, N_LANES};
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::FieldExpOps;

use std::fmt::Debug;
use std::ops::{Add, AddAssign, Mul, Sub};

//  ┌──────────────────────────────┐
//  │     Prep. Traces Helper      │
//  └──────────────────────────────┘

pub fn pack_column<F>(n_rows: usize, mut f: F) -> Vec<PackedM31>
where
    F: FnMut(usize) -> M31 + 'static,
{
    (0..n_rows)
        .map(move |idx| f(idx))
        .chunks(N_LANES)
        .into_iter()
        .map(|chunk| {
            let arr: [M31; N_LANES] = chunk.collect_vec().try_into().unwrap();
            PackedM31::from_array(arr)
        })
        .collect_vec()
}

//  ┌──────────────────────────────┐
//  │           Enabler            │
//  └──────────────────────────────┘

#[derive(Debug, Clone)]
pub struct Enabler {
    /// Number of active (non-padded) rows in the trace
    pub padding_offset: usize,
}
impl Enabler {
    pub const fn new(padding_offset: usize) -> Self {
        Self { padding_offset }
    }

    pub fn packed_at(&self, vec_row: usize) -> PackedM31 {
        let row_offset = vec_row * N_LANES;

        if row_offset >= self.padding_offset {
            return PackedM31::zero();
        }

        if row_offset + N_LANES <= self.padding_offset {
            return PackedM31::one();
        }

        let mut res = [M31::zero(); N_LANES];
        let enabled_lanes = self.padding_offset - row_offset;
        res[..enabled_lanes].fill(M31::one());
        PackedM31::from_array(res)
    }
}

//  ┌──────────────────────────────┐
//  │        Keccak-f (1600)       │
//  └──────────────────────────────┘

const KECCAK_RHO: [u32; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
];
const KECCAK_PI: [usize; 24] = [
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
];
const KECCAK_RC: [u64; 24] = [
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
];

/// Implementation of Keccak-f[1600] for easy trace filling in keccak
pub fn keccak_f1600(state: &mut [PackedM31; N_BYTES_IN_STATE]) {
    for lane in 0..N_LANES {
        let mut words = load_lane_words(state, lane);
        for round in 0..N_ROUNDS {
            keccak_f1600_round_words(&mut words, round);
        }
        store_lane_words(state, lane, &words);
    }
}

/// Implementation of a single Keccak-f[1600] round for easy trace filling in keccak_round
pub fn keccak_f1600_round(state: &mut [PackedM31; N_BYTES_IN_STATE], round: usize) {
    debug_assert!(round < N_ROUNDS);
    for lane in 0..N_LANES {
        let mut words = load_lane_words(state, lane);
        keccak_f1600_round_words(&mut words, round);
        store_lane_words(state, lane, &words);
    }
}

fn keccak_f1600_round_words(state: &mut [u64; N_LANES_SHAKE256], round: usize) {
    let mut c = [0u64; 5];
    for x in 0..5 {
        c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
    }

    let mut d = [0u64; 5];
    for x in 0..5 {
        d[x] = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
    }

    for y in 0..5 {
        for x in 0..5 {
            state[x + 5 * y] ^= d[x];
        }
    }

    let mut current = state[1];
    for i in 0..24 {
        let idx = KECCAK_PI[i];
        let tmp = state[idx];
        state[idx] = current.rotate_left(KECCAK_RHO[i]);
        current = tmp;
    }

    for y in 0..5 {
        let base = 5 * y;
        let row = [
            state[base],
            state[base + 1],
            state[base + 2],
            state[base + 3],
            state[base + 4],
        ];
        state[base] = row[0] ^ ((!row[1]) & row[2]);
        state[base + 1] = row[1] ^ ((!row[2]) & row[3]);
        state[base + 2] = row[2] ^ ((!row[3]) & row[4]);
        state[base + 3] = row[3] ^ ((!row[4]) & row[0]);
        state[base + 4] = row[4] ^ ((!row[0]) & row[1]);
    }

    state[0] ^= KECCAK_RC[round];
}

fn load_lane_words(state: &[PackedM31; N_BYTES_IN_STATE], lane: usize) -> [u64; N_LANES_SHAKE256] {
    let mut words = [0u64; N_LANES_SHAKE256];
    for w in 0..N_LANES_SHAKE256 {
        let mut value = 0u64;
        for byte_idx in 0..N_BYTES_IN_U64 {
            let idx = w * N_BYTES_IN_U64 + byte_idx;
            let byte = state[idx].to_array()[lane].0 as u64;
            value |= byte << (8 * byte_idx);
        }
        words[w] = value;
    }
    words
}

fn store_lane_words(
    state: &mut [PackedM31; N_BYTES_IN_STATE],
    lane: usize,
    words: &[u64; N_LANES_SHAKE256],
) {
    for w in 0..N_LANES_SHAKE256 {
        let value = words[w];
        for byte_idx in 0..N_BYTES_IN_U64 {
            let idx = w * N_BYTES_IN_U64 + byte_idx;
            let mut lanes = state[idx].to_array();
            lanes[lane] = M31::from(((value >> (8 * byte_idx)) & 0xFF) as u32);
            state[idx] = PackedM31::from_array(lanes);
        }
    }
}

//  ┌──────────────────────────────┐
//  │            Fu64              │
//  └──────────────────────────────┘

// Concrete 64-bit split into 8 limbs of 8 bits each
#[derive(Clone, Debug)]
pub struct Fu64_8<F>
where
    F: FieldExpOps
        + Clone
        + Zero
        + Debug
        + AddAssign<F>
        + Add<F, Output = F>
        + Sub<F, Output = F>
        + Mul<M31, Output = F>,
{
    pub limbs: [F; 8],
}

impl<F> Fu64_8<F>
where
    F: FieldExpOps
        + Zero
        + Clone
        + Debug
        + AddAssign<F>
        + Add<F, Output = F>
        + Sub<F, Output = F>
        + Mul<M31, Output = F>,
{
    pub fn from_felts(x: &[F; 8]) -> Self {
        Self { limbs: x.clone() }
    }
    #[allow(unused)]
    pub fn into_felts(self) -> [F; 8] {
        self.limbs
    }
}

impl<F> Zero for Fu64_8<F>
where
    F: FieldExpOps
        + Zero
        + Clone
        + Debug
        + AddAssign<F>
        + Add<F, Output = F>
        + Sub<F, Output = F>
        + Mul<M31, Output = F>,
{
    fn zero() -> Self {
        Self {
            limbs: core::array::from_fn(|_| F::zero()),
        }
    }

    fn is_zero(&self) -> bool {
        self.limbs.iter().all(|x| x.is_zero())
    }
}

impl<F> Add for Fu64_8<F>
where
    F: FieldExpOps
        + Zero
        + Clone
        + Debug
        + AddAssign<F>
        + Add<F, Output = F>
        + Sub<F, Output = F>
        + Mul<M31, Output = F>,
{
    type Output = Self;

    // Necessary for Zero implementation
    fn add(self, _other: Self) -> Self {
        unimplemented!();
    }
}

#[cfg(test)]
mod tests {
    use super::keccak_f1600;
    use crate::constants::{N_BYTES_IN_STATE, N_BYTES_IN_U64, N_LANES_SHAKE256};
    use num_traits::Zero;
    use stwo_prover::core::backend::simd::m31::{PackedM31, N_LANES};
    use stwo_prover::core::fields::m31::M31;
    use tiny_keccak::keccakf;

    /// Test that the Keccak-f[1600] implementation matches the reference implementation
    #[test]
    fn keccak_f1600_matches_reference() {
        let cases = [
            [0u64; 25],
            std::array::from_fn(|i| i as u64),
            std::array::from_fn(|i| (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)),
        ];

        for mut reference in cases {
            let mut state = words_to_packed(reference);

            keccak_f1600(&mut state);
            keccakf(&mut reference);
            assert_eq!(packed_to_words(&state), reference);

            keccak_f1600(&mut state);
            keccakf(&mut reference);
            assert_eq!(packed_to_words(&state), reference);
        }
    }

    fn words_to_packed(words: [u64; N_LANES_SHAKE256]) -> [PackedM31; N_BYTES_IN_STATE] {
        let mut out = [PackedM31::from_array([M31::zero(); N_LANES]); N_BYTES_IN_STATE];
        for w in 0..N_LANES_SHAKE256 {
            let word = words[w];
            for byte_idx in 0..N_BYTES_IN_U64 {
                let idx = w * N_BYTES_IN_U64 + byte_idx;
                let mut lanes = out[idx].to_array();
                lanes[0] = M31::from(((word >> (8 * byte_idx)) & 0xFF) as u32);
                out[idx] = PackedM31::from_array(lanes);
            }
        }
        out
    }

    fn packed_to_words(state: &[PackedM31; N_BYTES_IN_STATE]) -> [u64; N_LANES_SHAKE256] {
        let mut words = [0u64; N_LANES_SHAKE256];
        for w in 0..N_LANES_SHAKE256 {
            let mut word = 0u64;
            for byte_idx in 0..N_BYTES_IN_U64 {
                let idx = w * N_BYTES_IN_U64 + byte_idx;
                let byte = state[idx].to_array()[0].0 as u64;
                word |= byte << (8 * byte_idx);
            }
            words[w] = word;
        }
        words
    }
}
