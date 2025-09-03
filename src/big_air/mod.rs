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
pub mod relation_macro;

use crate::{
    POLY_SIZE,
    big_air::{claim::BigClaim, interaction_claim::BigInteractionClaim, relation::LookupElements},
    zq::Q,
};

use num_traits::Zero;
use stwo::{core::fields::qm31::QM31, prover::ComponentProver};

use stwo::{
    core::{
        channel::{Blake2sChannel, Channel},
        pcs::PcsConfig,
        poly::circle::CanonicCoset,
        proof::StarkProof,
        proof_of_work::GrindOps,
        vcs::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher},
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
pub fn prove_falcon(
    s1: &[u32; POLY_SIZE],
    pk: &[u32; POLY_SIZE],
    msg_point: &[u32; POLY_SIZE],
) -> Result<StarkProof<Blake2sMerkleHasher>, ProvingError> {
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
    let (preprocessed_columns, preprocessed_columns_ids) = BigClaim::create_preprocessed_columns();

    tree_builder.extend_evals(preprocessed_columns);
    tree_builder.commit(channel);

    // Generate and commit to main traces
    let claim = BigClaim::new_standard();
    let (trace, traces) = claim.gen_trace(s1, pk, msg_point);
    claim.mix_into(channel);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace);
    tree_builder.commit(channel);

    // Generate proof of work and draw lookup relations
    let interaction_pow = SimdBackend::grind(channel, 2);
    channel.mix_u64(interaction_pow);

    let lookup_elements = LookupElements::draw(channel);

    // Generate and commit to interaction traces
    let (interaction_trace, interaction_claim) = BigInteractionClaim::gen_interaction_trace(
        &lookup_elements,
        &traces.f_ntt_butterfly,
        &traces.f_ntt_merges,
        &traces.g_ntt_butterfly,
        &traces.g_ntt_merges,
        &traces.mul,
        &traces.intt_merges,
        &traces.ibutterfly,
        &traces.sub,
        &traces.euclidean_norm,
        &traces.half_range_check,
        &traces.low_sig_bound_check,
        &traces.high_sig_bound_check,
        &traces.range_check,
        &traces.roots,
        &traces.inv_roots,
    );

    interaction_claim.mix_into(channel);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction_trace);
    tree_builder.commit(channel);

    // Set up trace location allocator with preprocessed columns
    let mut tree_span_provider =
        TraceLocationAllocator::new_with_preproccessed_columns(&preprocessed_columns_ids);

    let (
        f_ntt_butterfly_component,
        f_ntt_merges_components,
        g_ntt_butterfly_component,
        g_ntt_merges_components,
    ) = BigClaim::create_ntt_components(
        &claim,
        &lookup_elements,
        &interaction_claim,
        &mut tree_span_provider,
    );
    let (
        mul_component,
        intt_merges_components,
        ibutterfly_component,
        sub_component,
        euclidean_norm_component,
        half_range_check_component,
        low_sig_bound_check_component,
        high_sig_bound_check_component,
        range_check_component,
        roots_components,
        inv_roots_components,
    ) = BigClaim::create_remaining_components(
        &claim,
        &lookup_elements,
        &interaction_claim,
        &mut tree_span_provider,
    );

    #[cfg(test)]
    {
        use crate::relation_tracker::{BigAirComponents, track_and_summarize_big_air_relations};

        let components = &BigAirComponents {
            f_ntt_butterfly: &f_ntt_butterfly_component,
            f_ntt_merges: &f_ntt_merges_components,
            g_ntt_butterfly: &g_ntt_butterfly_component,
            g_ntt_merges: &g_ntt_merges_components,
            mul: &mul_component,
            intt_merges: &intt_merges_components,
            ibutterfly: &ibutterfly_component,
            sub: &sub_component,
            euclidean_norm: &euclidean_norm_component,
            half_range_check: &half_range_check_component,
            low_sig_bound_check: &low_sig_bound_check_component,
            high_sig_bound_check: &high_sig_bound_check_component,
            range_check: &range_check_component,
            roots: &roots_components,
            inv_roots: &inv_roots_components,
        };
        let summary = track_and_summarize_big_air_relations(&commitment_scheme, components);
        std::fs::write("summary.txt", format!("{:?}", summary)).unwrap();

        // println!("summary: {:?}", summary);
    }
    assert_eq!(
        interaction_claim.claimed_sum(),
        QM31::zero(),
        "invalid logup sum"
    );

    let mut components: Vec<&dyn ComponentProver<SimdBackend>> = vec![];
    components.push(&f_ntt_butterfly_component);
    for merge in f_ntt_merges_components.iter() {
        components.push(merge);
    }
    components.push(&g_ntt_butterfly_component);
    for merge in g_ntt_merges_components.iter() {
        components.push(merge);
    }
    components.push(&mul_component);
    for merge in intt_merges_components.iter() {
        components.push(merge);
    }
    components.push(&ibutterfly_component);
    components.push(&sub_component);
    components.push(&euclidean_norm_component);
    components.push(&half_range_check_component);
    components.push(&low_sig_bound_check_component);
    components.push(&high_sig_bound_check_component);
    components.push(&range_check_component);

    for root in roots_components.iter() {
        components.push(root);
    }
    for inv_root in inv_roots_components.iter() {
        components.push(inv_root);
    }

    // Generate the final STARK proof
    prove::<SimdBackend, _>(&components, channel, commitment_scheme)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        debug,
        input::{MSG_POINT, PK, TEST_S1},
    };

    /// Tests the complete STARK proof generation for all arithmetic operations.
    ///
    /// This test verifies that:
    /// - All traces can be generated correctly
    /// - All constraints are satisfied
    /// - The proof can be generated without errors
    #[test]
    fn test_prove_falcon() {
        match prove_falcon(TEST_S1, PK, MSG_POINT) {
            Ok(_) => println!("Proof generation successful!"),
            Err(e) => {
                eprintln!("Proof generation failed: {:?}", e);
                panic!("Proof generation failed: {:?}", e);
            }
        }
    }

    #[test]
    fn test_debug_constraints() {
        debug::assert_constraints(TEST_S1, PK, MSG_POINT);
    }
}
