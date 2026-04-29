#![allow(non_snake_case)]

use itertools::Itertools;
use num_traits::{One, Zero};
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};
use stwo_prover::core::fields::m31::M31;

use crate::constants::{N_BYTES_IN_STATE, N_BYTES_IN_U64, N_LANES_SHAKE256, SQRT_N_LANES_SHAKE256};
use crate::trace::keccak_round::Claim;
use crate::utils::Fu64_8;

// Rotation offsets for Keccak-f[1600] RHO step
const RHO_OFFSETS: [[usize; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

#[derive(Clone)]
pub struct Eval {
    pub claim: Claim,
    pub interaction_elements: crate::interaction::InteractionElements,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let enabler = E::EF::from(eval.next_trace_mask());
        eval.add_constraint(enabler.clone() * (E::EF::one() - enabler.clone()));

        // ╔════════════════════════════════════╗
        // ║           Initialization           ║
        // ╚════════════════════════════════════╝
        let current_rc_bytes: [E::F; N_BYTES_IN_U64] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let next_rc_bytes: [E::F; N_BYTES_IN_U64] = std::array::from_fn(|_| eval.next_trace_mask());

        let S: [E::F; N_BYTES_IN_STATE] = std::array::from_fn(|_| eval.next_trace_mask());

        let round_data: Vec<E::F> = current_rc_bytes.iter().chain(S.iter()).cloned().collect();
        eval.add_to_relation(RelationEntry::new(
            &self.interaction_elements.keccak_round,
            -enabler.clone(),
            &round_data,
        ));

        let mut S: [Fu64_8<E::F>; N_LANES_SHAKE256] = S
            .chunks(8)
            .map(|chunk| Fu64_8::from_felts(chunk.try_into().unwrap()))
            .collect_vec()
            .try_into()
            .unwrap();

        // ╔════════════════════════════════════╗
        // ║               Theta                ║
        // ╚════════════════════════════════════╝
        // C[x] = S[x,0] ^ S[x,1] ^ S[x,2] ^ S[x,3] ^ S[x,4] computed via 4 chained xor_8_8 lookups.
        // For each x we witness the chain (t1, C_inter, t2, C) and emit one xor_8_8 lookup per link.
        let mut C: [Fu64_8<E::F>; SQRT_N_LANES_SHAKE256] = std::array::from_fn(|_| Fu64_8::zero());
        let mut C_inter_arr: [Fu64_8<E::F>; SQRT_N_LANES_SHAKE256] =
            std::array::from_fn(|_| Fu64_8::zero());

        for x in 0..SQRT_N_LANES_SHAKE256 {
            // Witness intermediate t1 = S[x,0] ^ S[x,1]
            let t1: Fu64_8<E::F> =
                Fu64_8::from_felts(&std::array::from_fn(|_| eval.next_trace_mask()));
            // Witness C_inter = t1 ^ S[x,2]
            let C_inter: Fu64_8<E::F> =
                Fu64_8::from_felts(&std::array::from_fn(|_| eval.next_trace_mask()));
            C_inter_arr[x] = C_inter.clone();
            // Witness intermediate t2 = C_inter ^ S[x,3]
            let t2: Fu64_8<E::F> =
                Fu64_8::from_felts(&std::array::from_fn(|_| eval.next_trace_mask()));
            // Witness C = t2 ^ S[x,4]
            C[x] = Fu64_8::from_felts(&std::array::from_fn(|_| eval.next_trace_mask()));

            for i in 0..N_BYTES_IN_U64 {
                // xor_8_8(S[x,0], S[x,1], t1)
                eval.add_to_relation(RelationEntry::new(
                    &self.interaction_elements.xor_8_8,
                    E::EF::one(),
                    &[
                        S[x].limbs[i].clone(),
                        S[x + 5].limbs[i].clone(),
                        t1.limbs[i].clone(),
                    ],
                ));
                // xor_8_8(t1, S[x,2], C_inter)
                eval.add_to_relation(RelationEntry::new(
                    &self.interaction_elements.xor_8_8,
                    E::EF::one(),
                    &[
                        t1.limbs[i].clone(),
                        S[x + 10].limbs[i].clone(),
                        C_inter.limbs[i].clone(),
                    ],
                ));
                // xor_8_8(C_inter, S[x,3], t2)
                eval.add_to_relation(RelationEntry::new(
                    &self.interaction_elements.xor_8_8,
                    E::EF::one(),
                    &[
                        C_inter.limbs[i].clone(),
                        S[x + 15].limbs[i].clone(),
                        t2.limbs[i].clone(),
                    ],
                ));
                // xor_8_8(t2, S[x,4], C)
                eval.add_to_relation(RelationEntry::new(
                    &self.interaction_elements.xor_8_8,
                    E::EF::one(),
                    &[
                        t2.limbs[i].clone(),
                        S[x + 20].limbs[i].clone(),
                        C[x].limbs[i].clone(),
                    ],
                ));
            }
        }

        // Rotate neighbor column: rotl(C[x+1], 1) == rotr(C[x+1], 63)
        let C_rot_1: [Fu64_8<E::F>; SQRT_N_LANES_SHAKE256] = std::array::from_fn(|x| {
            let xp1 = (x + 1) % SQRT_N_LANES_SHAKE256;
            rotr_fu64_8(&C[xp1], 63, &mut eval, &self.interaction_elements)
        });

        // Witness D
        let D: [Fu64_8<E::F>; SQRT_N_LANES_SHAKE256] = std::array::from_fn(|_| {
            Fu64_8::from_felts(&std::array::from_fn(|_| eval.next_trace_mask()))
        });

        // Check D = C[x-1] ^ rotl(C[x+1], 1)
        for x in 0..SQRT_N_LANES_SHAKE256 {
            for i in 0..N_BYTES_IN_U64 {
                let xm1 = (x + SQRT_N_LANES_SHAKE256 - 1) % SQRT_N_LANES_SHAKE256;
                eval.add_to_relation(RelationEntry::new(
                    &self.interaction_elements.xor_8_8,
                    E::EF::one(),
                    &[
                        C[xm1].limbs[i].clone(),
                        C_rot_1[x].limbs[i].clone(),
                        D[x].limbs[i].clone(),
                    ],
                ));
            }
        }

        // Witness theta-on-S result and verify
        let res_S: [Fu64_8<E::F>; N_LANES_SHAKE256] = std::array::from_fn(|_| {
            Fu64_8::from_felts(&std::array::from_fn(|_| eval.next_trace_mask()))
        });

        for x in 0..SQRT_N_LANES_SHAKE256 {
            for y in 0..SQRT_N_LANES_SHAKE256 {
                for i in 0..N_BYTES_IN_U64 {
                    eval.add_to_relation(RelationEntry::new(
                        &self.interaction_elements.xor_8_8,
                        E::EF::one(),
                        &[
                            S[x + 5 * y].limbs[i].clone(),
                            D[x].limbs[i].clone(),
                            res_S[x + 5 * y].limbs[i].clone(),
                        ],
                    ));
                }
            }
        }

        S = res_S;

        // ╔════════════════════════════════════╗
        // ║            RHO and PI              ║
        // ╚════════════════════════════════════╝
        let mut B: [Fu64_8<E::F>; N_LANES_SHAKE256] = std::array::from_fn(|_| Fu64_8::zero());
        for x in 0..SQRT_N_LANES_SHAKE256 {
            for y in 0..SQRT_N_LANES_SHAKE256 {
                let off = RHO_OFFSETS[x][y];
                let rotr = if off == 0 { 0 } else { 64 - off };
                B[5 * y + ((2 * x + 3 * y) % SQRT_N_LANES_SHAKE256)] =
                    rotr_fu64_8(&S[x + 5 * y], rotr, &mut eval, &self.interaction_elements);
            }
        }

        // ╔════════════════════════════════════╗
        // ║                 CHI                ║
        // ╚════════════════════════════════════╝
        // chi(a, b, c) = a ^ ((!b) & c).
        // Stage 1: witness chi_partial = (!b) & c via chi_8_8 lookups.
        let chi_partials: [Fu64_8<E::F>; N_LANES_SHAKE256] = std::array::from_fn(|_| {
            Fu64_8::from_felts(&std::array::from_fn(|_| eval.next_trace_mask()))
        });
        for y in 0..SQRT_N_LANES_SHAKE256 {
            for x in 0..SQRT_N_LANES_SHAKE256 {
                let b_idx = 5 * ((x + 1) % SQRT_N_LANES_SHAKE256) + y;
                let c_idx = 5 * ((x + 2) % SQRT_N_LANES_SHAKE256) + y;
                for i in 0..N_BYTES_IN_U64 {
                    eval.add_to_relation(RelationEntry::new(
                        &self.interaction_elements.chi_8_8,
                        E::EF::one(),
                        &[
                            B[b_idx].limbs[i].clone(),
                            B[c_idx].limbs[i].clone(),
                            chi_partials[x + 5 * y].limbs[i].clone(),
                        ],
                    ));
                }
            }
        }

        // Stage 2: witness S after CHI and verify S = a ^ chi_partial.
        S = std::array::from_fn(|_| {
            Fu64_8::from_felts(&std::array::from_fn(|_| eval.next_trace_mask()))
        });
        for y in 0..SQRT_N_LANES_SHAKE256 {
            for x in 0..SQRT_N_LANES_SHAKE256 {
                for i in 0..N_BYTES_IN_U64 {
                    eval.add_to_relation(RelationEntry::new(
                        &self.interaction_elements.xor_8_8,
                        E::EF::one(),
                        &[
                            B[5 * x + y].limbs[i].clone(),
                            chi_partials[x + 5 * y].limbs[i].clone(),
                            S[x + 5 * y].limbs[i].clone(),
                        ],
                    ));
                }
            }
        }

        // ╔════════════════════════════════════╗
        // ║                IOTA                ║
        // ╚════════════════════════════════════╝
        let res_S_xor_RC: Fu64_8<E::F> =
            Fu64_8::from_felts(&std::array::from_fn(|_| eval.next_trace_mask()));
        for i in 0..N_BYTES_IN_U64 {
            eval.add_to_relation(RelationEntry::new(
                &self.interaction_elements.xor_8_8,
                E::EF::one(),
                &[
                    S[0].limbs[i].clone(),
                    current_rc_bytes[i].clone(),
                    res_S_xor_RC.limbs[i].clone(),
                ],
            ));
        }
        S[0] = res_S_xor_RC;

        // Emit the next round state
        let next_round_data: Vec<E::F> = next_rc_bytes
            .iter()
            .cloned()
            .chain(S.iter().flat_map(|x| x.clone().into_felts()))
            .collect();
        eval.add_to_relation(RelationEntry::new(
            &self.interaction_elements.keccak_round,
            enabler.clone(),
            &next_round_data,
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}

fn rotr_fu64_8<E: EvalAtRow>(
    A: &Fu64_8<E::F>,
    n: usize,
    eval: &mut E,
    interaction_elements: &crate::interaction::InteractionElements,
) -> Fu64_8<E::F> {
    let q = n / 8;
    let r = n % 8;
    let two_pow_r: E::F = E::F::from(M31::from(1 << r));
    let max_ur: E::F = E::F::from(M31::from((1 << r) - 1));
    let two_pow_8_minus_r: E::F = E::F::from(M31::from(1 << (8 - r)));

    let A: Fu64_8<E::F> = Fu64_8::from_felts(&std::array::from_fn(|i| {
        let idx = (i + (q % N_BYTES_IN_U64)) % N_BYTES_IN_U64;
        A.limbs[idx].clone()
    }));

    if r == 0 {
        return A;
    }

    let A_hi_limbs: [E::F; 8] = std::array::from_fn(|_| eval.next_trace_mask());
    let A_lo_limbs: [E::F; 8] =
        std::array::from_fn(|i| A.limbs[i].clone() - A_hi_limbs[i].clone() * two_pow_r.clone());

    eval.add_to_relation(RelationEntry::new(
        &interaction_elements.rc_7_7_7,
        E::EF::one(),
        &[
            max_ur.clone() - A_lo_limbs[0].clone(),
            max_ur.clone() - A_lo_limbs[1].clone(),
            max_ur.clone() - A_lo_limbs[2].clone(),
        ],
    ));
    eval.add_to_relation(RelationEntry::new(
        &interaction_elements.rc_7_7_7,
        E::EF::one(),
        &[
            max_ur.clone() - A_lo_limbs[3].clone(),
            max_ur.clone() - A_lo_limbs[4].clone(),
            max_ur.clone() - A_lo_limbs[5].clone(),
        ],
    ));
    eval.add_to_relation(RelationEntry::new(
        &interaction_elements.rc_7_7_7,
        E::EF::one(),
        &[
            max_ur.clone() - A_lo_limbs[6].clone(),
            max_ur.clone() - A_lo_limbs[7].clone(),
            E::F::zero(),
        ],
    ));

    Fu64_8::from_felts(&std::array::from_fn(|i| {
        let j = (i + 1) % N_BYTES_IN_U64;
        A_hi_limbs[i].clone() + A_lo_limbs[j].clone() * two_pow_8_minus_r.clone()
    }))
}

pub type Component = FrameworkComponent<Eval>;
