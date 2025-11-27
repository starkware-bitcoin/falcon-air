use num_traits::Zero;
use serde::{Deserialize, Serialize};
use stwo_constraint_framework::Relation;
use stwo_prover::core::fields::{
    m31::M31,
    qm31::{SecureField, QM31},
    FieldExpOps,
};

use tiny_keccak::{Hasher, Shake};

use crate::{
    constants::{N_BYTES_IN_MESSAGE, N_BYTES_IN_OUTPUT},
    interaction::{relations, InteractionElements},
};

#[derive(Serialize, Deserialize, Debug)]
pub struct PublicData {
    pub inputs: Vec<Vec<u8>>,  // each length N_BYTES_IN_MESSAGE
    pub outputs: Vec<Vec<u8>>, // each length N_BYTES_IN_OUTPUT
}

impl PublicData {
    pub fn new(inputs: &Vec<[u8; N_BYTES_IN_MESSAGE]>) -> Self {
        let outputs: Vec<Vec<u8>> = inputs
            .iter()
            .map(|input| {
                let mut out = vec![0u8; N_BYTES_IN_OUTPUT];
                let mut shake = Shake::v256();
                shake.update(input);
                shake.finalize(&mut out);
                out
            })
            .collect();
        Self {
            inputs: inputs.iter().map(|x| x.to_vec()).collect(),
            outputs,
        }
    }

    // Emits SHAKE256 inputs and consumes SHAKE256 outputs (controls hash correctness)
    pub fn initial_logup_sum(&self, interaction_elements: &InteractionElements) -> SecureField {
        use crate::interaction::relations::RELATION_SIZE_SHAKE256;

        let mut values_to_inverse = vec![];

        for input in &self.inputs {
            let mut rel = [M31::zero(); RELATION_SIZE_SHAKE256];
            for i in 0..N_BYTES_IN_MESSAGE {
                rel[i] = M31::from(input[i] as u32);
            }
            values_to_inverse.push(
                <relations::Shake256 as Relation<M31, SecureField>>::combine(
                    &interaction_elements.shake256,
                    &rel,
                ),
            );
        }

        for output in &self.outputs {
            let mut rel = [M31::zero(); RELATION_SIZE_SHAKE256];
            for i in 0..N_BYTES_IN_OUTPUT {
                rel[i] = M31::from(output[i] as u32);
            }
            values_to_inverse.push(
                -<relations::Shake256 as Relation<M31, SecureField>>::combine(
                    &interaction_elements.shake256,
                    &rel,
                ),
            );
        }

        let inverted_values = QM31::batch_inverse(&values_to_inverse);
        inverted_values.iter().sum::<QM31>()
    }
}
