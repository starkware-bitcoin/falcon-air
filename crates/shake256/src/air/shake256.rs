#![allow(non_snake_case)]

use num_traits::{One, Zero};
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};
use stwo_prover::core::fields::m31::M31;

use crate::constants::{
    DELIMITED_SUFFIX, FINAL_BIT, N_BYTES_IN_MESSAGE, N_BYTES_IN_OUTPUT, N_BYTES_IN_RATE,
    N_BYTES_IN_STATE, N_SQUEEZING,
};
use crate::trace::shake256::Claim;

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
        // ║     Padding and Initialization     ║
        // ╚════════════════════════════════════╝
        // Initialize the state with 0-padded message
        let mut S: [E::F; N_BYTES_IN_STATE] = std::array::from_fn(|i| {
            if i < N_BYTES_IN_MESSAGE {
                eval.next_trace_mask()
            } else {
                E::F::zero()
            }
        });

        // Use the SHAKE256 message
        eval.add_to_relation(RelationEntry::new(
            &self.interaction_elements.shake256,
            -enabler.clone(),
            &S[..N_BYTES_IN_MESSAGE],
        ));

        // Add the delimited suffix
        S[N_BYTES_IN_MESSAGE] = E::F::from(M31::from(DELIMITED_SUFFIX));

        // Set the final bit
        S[N_BYTES_IN_RATE - 1] = E::F::from(M31::from(FINAL_BIT));

        // ╔════════════════════════════════════╗
        // ║              Absorbing             ║
        // ╚════════════════════════════════════╝
        // Guess the Keccak permutation result (post-absorption state)
        let res_S: [E::F; N_BYTES_IN_STATE] = std::array::from_fn(|_| eval.next_trace_mask());

        // Apply the permutation
        eval.add_to_relation(RelationEntry::new(
            &self.interaction_elements.keccak,
            enabler.clone(),
            &S,
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.interaction_elements.keccak,
            -enabler.clone(),
            &res_S,
        ));

        // First output block comes directly from the post-absorption state.
        let mut Z: [E::F; N_BYTES_IN_OUTPUT] = std::array::from_fn(|_| E::F::zero());
        for j in 0..N_BYTES_IN_RATE {
            Z[j] = res_S[j].clone();
        }

        S = res_S;

        // ╔════════════════════════════════════╗
        // ║              Squeezing             ║
        // ╚════════════════════════════════════╝
        for i in 1..N_SQUEEZING {
            // Guess the result separating rate and capacity and fill the output
            let res_S: [E::F; N_BYTES_IN_STATE] = std::array::from_fn(|j| {
                if j < N_BYTES_IN_RATE {
                    Z[i * N_BYTES_IN_RATE + j] = eval.next_trace_mask();
                    Z[i * N_BYTES_IN_RATE + j].clone()
                } else {
                    eval.next_trace_mask()
                }
            });

            // Apply the permutation
            eval.add_to_relation(RelationEntry::new(
                &self.interaction_elements.keccak,
                enabler.clone(),
                &S,
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.interaction_elements.keccak,
                -enabler.clone(),
                &res_S,
            ));

            S = res_S;
        }

        // Emit the SHAKE256 output
        eval.add_to_relation(RelationEntry::new(
            &self.interaction_elements.shake256,
            enabler.clone(),
            &Z,
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type Component = FrameworkComponent<Eval>;
