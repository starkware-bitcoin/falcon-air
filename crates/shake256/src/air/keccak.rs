#![allow(non_snake_case)]

use num_traits::One;
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};
use stwo_prover::core::fields::m31::M31;

use crate::constants::{N_BYTES_IN_STATE, N_ROUNDS};
use crate::trace::keccak::{Claim, IOTA_RC};

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
        // Initialize the state
        let mut S: [E::F; N_BYTES_IN_STATE] = std::array::from_fn(|_| eval.next_trace_mask());

        // Use the Keccak input state
        eval.add_to_relation(RelationEntry::new(
            &self.interaction_elements.keccak,
            -enabler.clone(),
            &S,
        ));

        // ╔════════════════════════════════════╗
        // ║               Rounds               ║
        // ╚════════════════════════════════════╝
        for round in 0..N_ROUNDS {
            // Emit the current round state ensuring that the associated keccak_round subroutine
            // uses the right round constant
            let round_data: Vec<E::F> = IOTA_RC[round]
                .to_le_bytes()
                .into_iter()
                .map(|x| E::F::from(M31::from(x as u32)))
                .chain(S.iter().cloned())
                .collect();
            eval.add_to_relation(RelationEntry::new(
                &self.interaction_elements.keccak_round,
                enabler.clone(),
                &round_data,
            ));

            // Guess the next round state
            let S_next_round: [E::F; N_BYTES_IN_STATE] =
                std::array::from_fn(|_| eval.next_trace_mask());

            // Emit the next round state
            let next_round_data: Vec<E::F> = IOTA_RC[round + 1]
                .to_le_bytes()
                .into_iter()
                .map(|x| E::F::from(M31::from(x as u32)))
                .chain(S_next_round.iter().cloned())
                .collect();
            eval.add_to_relation(RelationEntry::new(
                &self.interaction_elements.keccak_round,
                -enabler.clone(),
                &next_round_data,
            ));

            S = S_next_round;

            if round == N_ROUNDS - 1 {
                // Emit the Keccak output state
                eval.add_to_relation(RelationEntry::new(
                    &self.interaction_elements.keccak,
                    enabler.clone(),
                    &S,
                ));
            }
        }

        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type Component = FrameworkComponent<Eval>;
