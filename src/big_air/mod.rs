//! # Big AIR - Combined STARK Proof System
//!
//! This module implements a combined STARK proof system that integrates all arithmetic
//! operations (addition, multiplication, subtraction) with range checking.
//!
//! The system generates a single STARK proof that proves the correctness of:
//! - Modular addition: (a + b) mod q
//! - Modular multiplication: (a * b) mod q  
//! - Modular subtraction: (a - b) mod q
//! - Range checking: ensuring all results are in [0, q)
//!
//! All operations are performed in the field Z_q where q = 12289, which is compatible
//! with the Falcon signature scheme requirements.
//!
pub mod claim;
pub mod interaction_claim;
pub mod relation;

use crate::{
    POLY_LOG_SIZE,
    big_air::{claim::BigClaim, interaction_claim::BigInteractionClaim, relation::LookupElements},
    ntts::{intt, mul, ntt},
    zq::{Q, range_check},
};

use stwo::{
    core::{
        channel::{Blake2sChannel, Channel},
        pcs::PcsConfig,
        poly::circle::CanonicCoset,
        proof::StarkProof,
        proof_of_work::GrindOps,
        vcs::blake2_merkle::Blake2sMerkleChannel,
        vcs::blake2_merkle::Blake2sMerkleHasher,
    },
    prover::{
        CommitmentSchemeProver, ProvingError, backend::simd::SimdBackend, poly::circle::PolyOps,
        prove,
    },
};
use stwo_constraint_framework::TraceLocationAllocator;

/// Generates a complete STARK proof for all arithmetic operations.
///
/// This function orchestrates the entire proof generation process:
/// 1. Sets up the commitment scheme and Fiat-Shamir channel
/// 2. Commits to preprocessed columns (range check table)
/// 3. Generates traces for all arithmetic operations
/// 4. Commits to the main trace
/// 5. Generates interaction traces for lookup relations
/// 6. Commits to interaction traces
/// 7. Generates the final STARK proof
///
/// # Returns
///
/// Returns a `StarkProof` that proves the correctness of all arithmetic
/// operations and their range checking constraints.
///
/// # Errors
///
/// Returns `ProvingError` if any step in the proof generation fails,
/// such as constraint violations or commitment failures.
pub fn prove_falcon() -> Result<StarkProof<Blake2sMerkleHasher>, ProvingError> {
    // Use consistent trace size across all components
    let range_check_log_size = Q.ilog2() + 1;

    // Initialize Fiat-Shamir channel and commitment scheme
    let channel = &mut Blake2sChannel::default();
    let pcs_config = PcsConfig::default();
    pcs_config.mix_into(channel);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(range_check_log_size + pcs_config.fri_config.log_blowup_factor + 1)
            .circle_domain()
            .half_coset,
    );

    // Commit to preprocessed columns (range check table)
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(pcs_config, &twiddles);
    let mut tree_builder = commitment_scheme.tree_builder();
    let range_check_preprocessed = range_check::RangeCheck12289::gen_column_simd();
    tree_builder.extend_evals([range_check_preprocessed]);
    tree_builder.commit(channel);

    // Generate and commit to main traces
    let claim = BigClaim {
        f_ntt: ntt::Claim { log_size: 4 },
        g_ntt: ntt::Claim { log_size: 4 },
        mul: mul::Claim {
            log_size: POLY_LOG_SIZE,
        },
        intt: intt::Claim { log_size: 4 },
        range_check: range_check::Claim {
            log_size: range_check_log_size,
        },
    };
    let (trace, traces) = claim.gen_trace();
    claim.mix_into(channel);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace.clone());
    tree_builder.commit(channel);

    // Generate proof of work and draw lookup relations
    let interaction_pow = SimdBackend::grind(channel, 2);
    channel.mix_u64(interaction_pow);

    let lookup_elements = LookupElements::draw(channel);

    // Generate and commit to interaction traces
    let (interaction_trace, interaction_claim) = BigInteractionClaim::gen_interaction_trace(
        &lookup_elements,
        &traces.f_ntt,
        &traces.g_ntt,
        &traces.mul,
        &traces.intt,
        &traces.range_check,
    );
    interaction_claim.mix_into(channel);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction_trace);
    tree_builder.commit(channel);

    // Set up trace location allocator with preprocessed columns
    let mut tree_span_provider = TraceLocationAllocator::new_with_preproccessed_columns(&[
        range_check::RangeCheck12289::id(),
    ]);

    let f_ntt_component = ntt::Component::new(
        &mut tree_span_provider,
        ntt::Eval {
            claim: ntt::Claim { log_size: 4 },
            rc_lookup_elements: lookup_elements.rc.clone(),
            ntt_lookup_elements: lookup_elements.f_ntt.clone(),
        },
        interaction_claim.f_ntt.claimed_sum,
    );
    let g_ntt_component = ntt::Component::new(
        &mut tree_span_provider,
        ntt::Eval {
            claim: ntt::Claim { log_size: 4 },
            rc_lookup_elements: lookup_elements.rc.clone(),
            ntt_lookup_elements: lookup_elements.g_ntt.clone(),
        },
        interaction_claim.g_ntt.claimed_sum,
    );
    let mul_component = mul::Component::new(
        &mut tree_span_provider,
        mul::Eval {
            claim: mul::Claim {
                log_size: POLY_LOG_SIZE,
            },
            rc_lookup_elements: lookup_elements.rc.clone(),
            f_ntt_lookup_elements: lookup_elements.f_ntt.clone(),
            g_ntt_lookup_elements: lookup_elements.g_ntt.clone(),
            mul_lookup_elements: lookup_elements.mul.clone(),
        },
        interaction_claim.mul.claimed_sum,
    );
    let intt_component = intt::Component::new(
        &mut tree_span_provider,
        intt::Eval {
            claim: intt::Claim { log_size: 4 },
            rc_lookup_elements: lookup_elements.rc.clone(),
            mul_lookup_elements: lookup_elements.mul.clone(),
        },
        interaction_claim.intt.claimed_sum,
    );
    let range_check_component = range_check::Component::new(
        &mut tree_span_provider,
        range_check::Eval {
            claim: range_check::Claim {
                log_size: range_check_log_size,
            },
            lookup_elements: lookup_elements.rc.clone(),
        },
        interaction_claim.range_check.claimed_sum,
    );

    #[cfg(test)]
    {
        use crate::relation_tracker::{BigAirComponents, track_and_summarize_big_air_relations};
        let components = &BigAirComponents {
            f_ntt: &f_ntt_component,
            g_ntt: &g_ntt_component,
            mul: &mul_component,
            intt: &intt_component,
            range_check: &range_check_component,
        };
        println!(
            "summary: {:?}",
            track_and_summarize_big_air_relations(&commitment_scheme, components)
        );
    }

    // Generate the final STARK proof
    prove::<SimdBackend, _>(
        &[
            &f_ntt_component,
            &g_ntt_component,
            &mul_component,
            &intt_component,
            &range_check_component,
        ],
        channel,
        commitment_scheme,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::debug;

    /// Tests the complete STARK proof generation for all arithmetic operations.
    ///
    /// This test verifies that:
    /// - All traces can be generated correctly
    /// - All constraints are satisfied
    /// - The proof can be generated without errors
    #[test]
    fn test_prove_falcon() {
        match prove_falcon() {
            Ok(_) => println!("Proof generation successful!"),
            Err(e) => {
                eprintln!("Proof generation failed: {:?}", e);
                panic!("Proof generation failed: {:?}", e);
            }
        }
    }

    #[test]
    fn test_debug_constraints() {
        debug::assert_constraints();
    }
}
