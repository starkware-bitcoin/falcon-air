#![allow(unused)]

use itertools::chain;
use num_traits::{One, Zero};
use stwo_constraint_framework::relation_tracker::{
    add_to_relation_entries, RelationSummary, RelationTrackerEntry,
};
use stwo_prover::core::backend::simd::SimdBackend;
use stwo_prover::core::backend::{BackendForChannel, Column};
use stwo_prover::core::channel::MerkleChannel;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::pcs::{CommitmentSchemeProver, TreeVec};
use stwo_prover::core::poly::circle::CanonicCoset;

use crate::air::Components;
use crate::constants::{N_BYTES_IN_MESSAGE, N_BYTES_IN_OUTPUT};
use crate::interaction::relations::RELATION_SIZE_SHAKE256;
use crate::public_data::PublicData;

/// Show emitted but unconsumed OR consumed but non emitted relation entries.
pub fn track_and_summarize_relations<MC: MerkleChannel>(
    commitment_scheme: &CommitmentSchemeProver<'_, SimdBackend, MC>,
    components: &Components,
    public_data: &PublicData,
) -> RelationSummary
where
    SimdBackend: BackendForChannel<MC>,
{
    let entries = track_relations(commitment_scheme, components, public_data);
    RelationSummary::summarize_relations(&entries).cleaned()
}

/// Tracks lookup emissions/consumptions
///
/// Goes through each add_to_relation in each component and for each entry it counts how much time it is emitted/used:
/// - adds `numerator` times for emissions
/// - subtracts `numerator` times for uses
///
/// Most of the logic in the track_relations function reproduces the PublicData::initial_logup_sum logic.
/// Must be updated when components or public data are modified.
fn track_relations<MC: MerkleChannel>(
    commitment_scheme: &CommitmentSchemeProver<'_, SimdBackend, MC>,
    components: &Components,
    public_data: &PublicData,
) -> Vec<RelationTrackerEntry>
where
    SimdBackend: BackendForChannel<MC>,
{
    let evals = commitment_scheme.trace().polys.map(|tree| {
        tree.iter()
            .map(|poly| {
                poly.evaluate(CanonicCoset::new(poly.log_size()).circle_domain())
                    .values
                    .to_cpu()
            })
            .collect()
    });
    let evals = &evals.as_ref();
    let trace = &evals.into();

    relation_entries(components, trace, public_data)
}

/// Goes through add_to_relation all and keeps count of each entry used/emitted.
/// Should be updated when components are modified.
fn relation_entries(
    components: &Components,
    trace: &TreeVec<Vec<&Vec<M31>>>,
    public_data: &PublicData,
) -> Vec<RelationTrackerEntry> {
    let Components {
        shake256,
        keccak,
        keccak_round,
        xor_8_8_8,
        rc_7_7_7,
        chi_8_8_8,
        xor_8_8,
    } = components;

    let mut entries: Vec<RelationTrackerEntry> = chain!(
        add_to_relation_entries(&shake256, trace),
        add_to_relation_entries(&keccak, trace),
        add_to_relation_entries(&keccak_round, trace),
        add_to_relation_entries(&xor_8_8_8, trace),
        add_to_relation_entries(&rc_7_7_7, trace),
        add_to_relation_entries(&chi_8_8_8, trace),
        add_to_relation_entries(&xor_8_8, trace),
    )
    .collect();

    // PublicData contributions: emit inputs (+1) and consume outputs (-1) for Shake256.
    for input in &public_data.inputs {
        let mut values = vec![M31::zero(); RELATION_SIZE_SHAKE256];
        for i in 0..N_BYTES_IN_MESSAGE {
            values[i] = M31::from(input[i] as u32);
        }
        entries.push(RelationTrackerEntry {
            relation: "Shake256".to_string(),
            mult: M31::one(),
            values,
        });
    }
    for output in &public_data.outputs {
        let mut values = vec![M31::zero(); RELATION_SIZE_SHAKE256];
        for i in 0..N_BYTES_IN_OUTPUT {
            values[i] = M31::from(output[i] as u32);
        }
        entries.push(RelationTrackerEntry {
            relation: "Shake256".to_string(),
            mult: -M31::one(),
            values,
        });
    }

    entries
}
