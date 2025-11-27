#![feature(raw_slice_split)]
#![feature(iter_array_chunks)]

mod air;
pub mod constants;
pub mod debug_tools;
mod interaction;
mod preprocessed;
mod public_data;
mod trace;
mod utils;

use std::time::Instant;

use num_traits::Zero;
use serde::{Deserialize, Serialize};
use stwo_constraint_framework::TraceLocationAllocator;
use stwo_prover::core::backend::simd::m31::N_LANES;
use stwo_prover::core::backend::simd::SimdBackend;
use stwo_prover::core::backend::BackendForChannel;
use stwo_prover::core::channel::{Blake2sChannel, Channel};
use stwo_prover::core::fields::qm31::SecureField;
use stwo_prover::core::pcs::{CommitmentSchemeProver, CommitmentSchemeVerifier, PcsConfig};
use stwo_prover::core::poly::circle::{CanonicCoset, PolyOps};
use stwo_prover::core::proof_of_work::GrindOps;
use stwo_prover::core::prover::{
    prove, verify, ProvingError, StarkProof, VerificationError as StwoVerificationError,
};
use stwo_prover::core::vcs::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use thiserror::Error;
use tracing::{info, span, Level};

use crate::air::Components;
use crate::constants::{N_BYTES_IN_MESSAGE, N_SQUEEZING};
use crate::interaction::{InteractionClaim, InteractionElements};
use crate::preprocessed::generate_preprocessed_trace;
use crate::public_data::PublicData;
use crate::trace::Claim;

const MAX_LOG_SIZE: u32 = 24;

// ============================ Proof Structure ================================

#[derive(Serialize, Deserialize, Debug)]
pub struct Shake256Proof {
    /// Claim about the execution trace (log sizes for each component)
    pub claim: Claim,
    /// Claim about interaction trace (claimed sums for each component)
    pub interaction_claim: InteractionClaim,
    /// Public data
    pub public_data: PublicData,
    /// The underlying STARK proof containing polynomial commitments and evaluations
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
    /// Proof-of-work nonce
    pub interaction_pow: u64,
}

// =============================== Prove ==================================

pub fn prove_shake256(
    messages: Vec<[u8; N_BYTES_IN_MESSAGE]>,
    pcs_config: PcsConfig,
) -> Result<Shake256Proof, ProvingError>
where
    SimdBackend: BackendForChannel<Blake2sMerkleChannel>,
{
    let _span = span!(Level::INFO, "Prove SHAKE-256").entered();
    let n_messages = messages.len();

    //  ┌──────────────────────────────┐
    //  │        Setup Protocol        │
    //  └──────────────────────────────┘
    info!("Setup channel");
    let channel = &mut Blake2sChannel::default();
    pcs_config.mix_into(channel);

    info!("Precompute twiddles");
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(MAX_LOG_SIZE + pcs_config.fri_config.log_blowup_factor + 1)
            .circle_domain()
            .half_coset,
    );

    info!("Generate public data");
    let public_data = PublicData::new(&messages);

    info!("Setup commitment scheme");
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(pcs_config, &twiddles);

    //  ┌──────────────────────────────┐
    //  │      Preprocessed Trace      │
    //  └──────────────────────────────┘
    info!("Generate preprocessed trace");
    let (preprocessed_trace, preprocessed_trace_ids, _) = generate_preprocessed_trace();

    info!("Commit preprocessed trace");
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed_trace);
    tree_builder.commit(channel);

    //  ┌──────────────────────────────┐
    //  │          Base Trace          │
    //  └──────────────────────────────┘
    info!("Generate base trace");
    let (claim, trace, lookup_data) = Claim::generate_trace(messages);
    claim.mix_into(channel);

    info!("Commit base trace");
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace);
    tree_builder.commit(channel);

    //  ┌──────────────────────────────┐
    //  │      Interaction Trace       │
    //  └──────────────────────────────┘
    info!("Grind {} bits", pcs_config.pow_bits);
    let interaction_pow = SimdBackend::grind(channel, pcs_config.pow_bits);
    channel.mix_u64(interaction_pow);

    info!("Draw interaction elements");
    let interaction_elements = InteractionElements::draw(channel);

    info!("Generate interaction trace");
    let (interaction_claim, interaction_trace) =
        InteractionClaim::generate_interaction_trace(&interaction_elements, &lookup_data);
    interaction_claim.mix_into(channel);

    info!("Commit interaction trace");
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction_trace);
    tree_builder.commit(channel);

    //  ┌──────────────────────────────┐
    //  │          Prove STARK         │
    //  └──────────────────────────────┘
    let mut tree_span_provider =
        TraceLocationAllocator::new_with_preproccessed_columns(&preprocessed_trace_ids);
    let components = Components::new(
        &mut tree_span_provider,
        &claim,
        &interaction_claim,
        &interaction_elements,
    );

    #[cfg(feature = "relation-tracker")]
    {
        use crate::debug_tools::relation_tracker::track_and_summarize_relations;
        let summary = track_and_summarize_relations(&commitment_scheme, &components, &public_data);
        println!("Relations summary: {:?}", summary);
    }
    info!(
        "Number of columns per trace: {:?}",
        commitment_scheme
            .trees
            .as_ref()
            .map(|tree| tree.evaluations.len())
    );

    info!("Prove STARK");
    let proving_start = Instant::now();
    let stark_proof = prove::<SimdBackend, _>(&components.provers(), channel, commitment_scheme)
        .map_err(ProvingError::from)?;
    let proving_duration = proving_start.elapsed();

    //  ┌──────────────────────────────┐
    //  │      Performance Metrics     │
    //  └──────────────────────────────┘
    let computed_shake256_instances = std::cmp::max(n_messages.next_power_of_two(), N_LANES);
    let computed_keccak_permutations = std::cmp::max((n_messages * N_SQUEEZING).next_power_of_two(), N_LANES);
    let proving_frequency_shake256 = (computed_shake256_instances as f64) / proving_duration.as_secs_f64();
    let proving_frequency_keccak = (computed_keccak_permutations as f64) / proving_duration.as_secs_f64();
    info!("SHAKE-256 instances: {:?}", computed_shake256_instances);
    info!("Keccak permutations: {:?}", computed_keccak_permutations);
    info!(
        "Proving frequency for SHAKE-256: {:.2} Hz",
        proving_frequency_shake256
    );
    info!(
        "Proving frequency for Keccak: {:.2} Hz",
        proving_frequency_keccak
    );

    Ok(Shake256Proof {
        claim,
        interaction_claim,
        public_data,
        stark_proof,
        interaction_pow,
    })
}

// =============================== Verify ==================================

pub fn verify_shake256(proof: Shake256Proof, pcs_config: PcsConfig) -> Result<(), VerificationError>
where
    SimdBackend: BackendForChannel<Blake2sMerkleChannel>,
{
    let _span = span!(Level::INFO, "Verify SHAKE-256").entered();

    //  ┌──────────────────────────────┐
    //  │        Setup Protocol        │
    //  └──────────────────────────────┘
    info!("Setup channel");
    let channel = &mut Blake2sChannel::default();
    pcs_config.mix_into(channel);

    info!("Setup commitment scheme");
    let commitment_scheme_verifier =
        &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(pcs_config);

    //  ┌──────────────────────────────┐
    //  │      Preprocessed Trace      │
    //  └──────────────────────────────┘
    info!("Commit preprocessed trace");
    let (_, preprocessed_trace_ids, preprocessed_trace_log_sizes) = generate_preprocessed_trace();
    commitment_scheme_verifier.commit(
        proof.stark_proof.commitments[0],
        &preprocessed_trace_log_sizes,
        channel,
    );

    //  ┌──────────────────────────────┐
    //  │          Base Trace          │
    //  └──────────────────────────────┘
    info!("Commit base trace");
    proof.claim.mix_into(channel);
    commitment_scheme_verifier.commit(
        proof.stark_proof.commitments[1],
        &proof.claim.log_sizes()[1],
        channel,
    );

    //  ┌──────────────────────────────┐
    //  │      Interaction Trace       │
    //  └──────────────────────────────┘
    info!("Verify proof-of-work");
    channel.mix_u64(proof.interaction_pow);
    if channel.trailing_zeros() < pcs_config.pow_bits {
        return Err(VerificationError::Stwo(StwoVerificationError::ProofOfWork));
    }

    info!("Draw interaction elements");
    let relations = InteractionElements::draw(channel);

    // Verify lookup argument.
    info!("Verify Logup Sum");
    if proof
        .interaction_claim
        .claimed_sum(&relations, proof.public_data)
        != SecureField::zero()
    {
        return Err(VerificationError::InvalidLogupSum);
    }

    info!("Commit interaction trace");
    proof.interaction_claim.mix_into(channel);
    commitment_scheme_verifier.commit(
        proof.stark_proof.commitments[2],
        &proof.claim.log_sizes()[2],
        channel,
    );

    //  ┌──────────────────────────────┐
    //  │          Verify STARK        │
    //  └──────────────────────────────┘
    let mut tree_span_provider =
        TraceLocationAllocator::new_with_preproccessed_columns(&preprocessed_trace_ids);
    let components = Components::new(
        &mut tree_span_provider,
        &proof.claim,
        &proof.interaction_claim,
        &relations,
    );
    info!("Verify STARK");
    verify(
        &components.verifiers(),
        channel,
        commitment_scheme_verifier,
        proof.stark_proof,
    )
    .map_err(VerificationError::from)
}

#[derive(Clone, Debug, Error)]
pub enum VerificationError {
    #[error("Invalid logup sum.")]
    InvalidLogupSum,
    #[error(transparent)]
    Stwo(#[from] StwoVerificationError),
}
