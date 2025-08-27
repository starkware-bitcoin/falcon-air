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
    HIGH_SIG_BOUND, LOW_SIG_BOUND, POLY_LOG_SIZE, POLY_SIZE,
    big_air::{
        claim::BigClaim,
        interaction_claim::BigInteractionClaim,
        relation::{INTTInputLookupElements, LookupElements},
    },
    ntts::{intt, ntt},
    polys::{euclidean_norm, mul, sub},
    zq::{Q, range_check},
};
use itertools::Itertools;
use num_traits::Zero;
use stwo::{
    core::fields::qm31::QM31,
    prover::{ComponentProver, backend::simd::m31::LOG_N_LANES},
};

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
    let range_check_preprocessed = range_check::RangeCheck::<Q>::gen_column_simd();
    let half_range_check_preprocessed = range_check::RangeCheck::<{ Q / 2 }>::gen_column_simd();

    let low_sig_bound_check_preprocessed =
        range_check::RangeCheck::<LOW_SIG_BOUND>::gen_column_simd();
    let high_sig_bound_check_preprocessed =
        range_check::RangeCheck::<HIGH_SIG_BOUND>::gen_column_simd();
    tree_builder.extend_evals([
        range_check_preprocessed,
        half_range_check_preprocessed,
        low_sig_bound_check_preprocessed,
        high_sig_bound_check_preprocessed,
    ]);
    tree_builder.commit(channel);

    let f_ntt_merges = (1..POLY_LOG_SIZE)
        .map(|log_size| {
            let log_size = POLY_LOG_SIZE - log_size - 1;
            ntt::Claim {
                log_size: std::cmp::max(LOG_N_LANES, log_size),
            }
        })
        .collect_vec();
    let g_ntt_merges = (1..POLY_LOG_SIZE)
        .map(|log_size| {
            let log_size = POLY_LOG_SIZE - log_size - 1;
            ntt::Claim {
                log_size: std::cmp::max(LOG_N_LANES, log_size),
            }
        })
        .collect_vec();

    let intt_merges = (1..POLY_LOG_SIZE)
        .map(|log_size| intt::Claim {
            log_size: std::cmp::max(LOG_N_LANES, log_size),
        })
        .collect_vec();
    // Generate and commit to main traces
    let claim = BigClaim {
        f_ntt_butterfly: ntt::butterfly::Claim {
            log_size: POLY_LOG_SIZE - 1,
        },
        f_ntt_merges,
        g_ntt_butterfly: ntt::butterfly::Claim {
            log_size: POLY_LOG_SIZE - 1,
        },
        g_ntt_merges,
        mul: mul::Claim {
            log_size: POLY_LOG_SIZE,
        },
        intt_merges,
        ibutterfly: intt::ibutterfly::Claim {
            log_size: POLY_LOG_SIZE - 1,
        },
        sub: sub::Claim {
            log_size: POLY_LOG_SIZE,
        },
        euclidean_norm: euclidean_norm::Claim {
            log_size: POLY_LOG_SIZE,
        },
        half_range_check: range_check::Claim {
            log_size: range_check_log_size - 1,
        },
        low_sig_bound_check: range_check::Claim {
            log_size: LOW_SIG_BOUND.next_power_of_two().ilog2(),
        },
        high_sig_bound_check: range_check::Claim {
            log_size: HIGH_SIG_BOUND.next_power_of_two().ilog2(),
        },
        range_check: range_check::Claim {
            log_size: range_check_log_size,
        },
    };
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
    );

    interaction_claim.mix_into(channel);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction_trace);
    tree_builder.commit(channel);

    // Set up trace location allocator with preprocessed columns
    let mut tree_span_provider = TraceLocationAllocator::new_with_preproccessed_columns(&[
        range_check::RangeCheck::<Q>::id(),
        range_check::RangeCheck::<{ Q / 2 }>::id(),
        range_check::RangeCheck::<LOW_SIG_BOUND>::id(),
        range_check::RangeCheck::<HIGH_SIG_BOUND>::id(),
    ]);

    let f_ntt_butterfly_component = ntt::butterfly::Component::new(
        &mut tree_span_provider,
        ntt::butterfly::Eval {
            claim: claim.f_ntt_butterfly,
            rc_lookup_elements: lookup_elements.rc.clone(),
            butterfly_output_lookup_elements: lookup_elements.f_ntt_butterfly.clone(),
        },
        interaction_claim.f_ntt_butterfly.claimed_sum,
    );
    let f_ntt_merges_components = claim
        .f_ntt_merges
        .into_iter()
        .zip_eq(interaction_claim.f_ntt_merges.iter())
        .enumerate()
        .map(|(i, (merge, interaction_claim))| {
            ntt::Component::new(
                &mut tree_span_provider,
                ntt::Eval {
                    claim: merge,
                    rc_lookup_elements: lookup_elements.rc.clone(),
                    ntt_lookup_elements: lookup_elements.f_ntt.clone(),
                    input_lookup_elements: if i == 0 {
                        ntt::InputLookupElements::Butterfly(lookup_elements.f_ntt_butterfly.clone())
                    } else {
                        ntt::InputLookupElements::NTT(lookup_elements.f_ntt.clone())
                    },
                    poly_size: 1 << (i + 1),
                },
                interaction_claim.claimed_sum,
            )
        })
        .collect_vec();

    let g_ntt_butterfly_component = ntt::butterfly::Component::new(
        &mut tree_span_provider,
        ntt::butterfly::Eval {
            claim: claim.g_ntt_butterfly,
            rc_lookup_elements: lookup_elements.rc.clone(),
            butterfly_output_lookup_elements: lookup_elements.g_ntt_butterfly.clone(),
        },
        interaction_claim.g_ntt_butterfly.claimed_sum,
    );
    let g_ntt_merges_components = claim
        .g_ntt_merges
        .into_iter()
        .zip_eq(interaction_claim.g_ntt_merges.iter())
        .enumerate()
        .map(|(i, (merge, interaction_claim))| {
            ntt::Component::new(
                &mut tree_span_provider,
                ntt::Eval {
                    claim: merge,
                    rc_lookup_elements: lookup_elements.rc.clone(),
                    ntt_lookup_elements: lookup_elements.g_ntt.clone(),
                    input_lookup_elements: if i == 0 {
                        ntt::InputLookupElements::Butterfly(lookup_elements.g_ntt_butterfly.clone())
                    } else {
                        ntt::InputLookupElements::NTT(lookup_elements.g_ntt.clone())
                    },
                    poly_size: 1 << (i + 1),
                },
                interaction_claim.claimed_sum,
            )
        })
        .collect_vec();
    let mul_component = mul::Component::new(
        &mut tree_span_provider,
        mul::Eval {
            claim: claim.mul,
            rc_lookup_elements: lookup_elements.rc.clone(),
            f_ntt_lookup_elements: lookup_elements.f_ntt.clone(),
            g_ntt_lookup_elements: lookup_elements.g_ntt.clone(),
            mul_lookup_elements: lookup_elements.mul.clone(),
        },
        interaction_claim.mul.claimed_sum,
    );
    let intt_merges_components = claim
        .intt_merges
        .into_iter()
        .zip_eq(interaction_claim.intt_merges.iter())
        .enumerate()
        .map(|(i, (merge, interaction_claim))| {
            intt::Component::new(
                &mut tree_span_provider,
                intt::Eval {
                    claim: merge,
                    rc_lookup_elements: lookup_elements.rc.clone(),
                    input_lookup_elements: if i == 0 {
                        INTTInputLookupElements::Mul(lookup_elements.mul.clone())
                    } else {
                        INTTInputLookupElements::INTTOutput(lookup_elements.intt.clone())
                    },
                    intt_lookup_elements: lookup_elements.intt.clone(),
                    poly_size: 1 << (POLY_LOG_SIZE as usize - i),
                },
                interaction_claim.claimed_sum,
            )
        })
        .collect_vec();

    let ibutterfly_component = intt::ibutterfly::Component::new(
        &mut tree_span_provider,
        intt::ibutterfly::Eval {
            claim: claim.ibutterfly,
            rc_lookup_elements: lookup_elements.rc.clone(),
            intt_output_lookup_elements: lookup_elements.intt.clone(),
            ibutterfly_output_lookup_elements: lookup_elements.ibutterfly.clone(),
        },
        interaction_claim.ibutterfly.claimed_sum,
    );
    let sub_component = sub::Component::new(
        &mut tree_span_provider,
        sub::Eval {
            claim: claim.sub,
            rc_lookup_elements: lookup_elements.rc.clone(),
            ibutterfly_lookup_elements: lookup_elements.ibutterfly.clone(),
            sub_lookup_elements: lookup_elements.sub.clone(),
        },
        interaction_claim.sub.claimed_sum,
    );
    let euclidean_norm_component = euclidean_norm::Component::new(
        &mut tree_span_provider,
        euclidean_norm::Eval {
            claim: claim.euclidean_norm,
            half_rc_lookup_elements: lookup_elements.half_range_check.clone(),
            s0_lookup_elements: lookup_elements.sub.clone(),
            low_sig_bound_check_lookup_elements: lookup_elements.low_sig_bound_check.clone(),
            high_sig_bound_check_lookup_elements: lookup_elements.high_sig_bound_check.clone(),
        },
        interaction_claim.euclidean_norm.claimed_sum,
    );
    let half_range_check_component = range_check::Component::new(
        &mut tree_span_provider,
        range_check::Eval::<{ Q / 2 }> {
            claim: claim.half_range_check,
            lookup_elements: lookup_elements.half_range_check.clone(),
        },
        interaction_claim.half_range_check.claimed_sum,
    );
    let low_sig_bound_check_component = range_check::Component::new(
        &mut tree_span_provider,
        range_check::Eval::<LOW_SIG_BOUND> {
            claim: claim.low_sig_bound_check,
            lookup_elements: lookup_elements.low_sig_bound_check.clone(),
        },
        interaction_claim.low_sig_bound_check.claimed_sum,
    );
    let high_sig_bound_check_component = range_check::Component::new(
        &mut tree_span_provider,
        range_check::Eval::<HIGH_SIG_BOUND> {
            claim: claim.high_sig_bound_check,
            lookup_elements: lookup_elements.high_sig_bound_check.clone(),
        },
        interaction_claim.high_sig_bound_check.claimed_sum,
    );
    let range_check_component = range_check::Component::new(
        &mut tree_span_provider,
        range_check::Eval::<Q> {
            claim: claim.range_check,
            lookup_elements: lookup_elements.rc.clone(),
        },
        interaction_claim.range_check.claimed_sum,
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
    // Generate the final STARK proof
    prove::<SimdBackend, _>(&components, channel, commitment_scheme)
    // Err(ProvingError::ConstraintsNotSatisfied)
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
