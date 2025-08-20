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

use crate::{
    POLY_LOG_SIZE,
    ntts::{intt, mul, ntt},
    relation_tracker::{BigAirComponents, track_and_summarize_big_air_relations},
    zq::{Q, range_check},
};
use itertools::{Itertools, chain};
use stwo::{
    core::{
        channel::{Blake2sChannel, Channel},
        fields::{m31::M31, qm31::QM31},
        pcs::{PcsConfig, TreeVec},
        poly::circle::CanonicCoset,
        proof::StarkProof,
        proof_of_work::GrindOps,
        vcs::blake2_merkle::Blake2sMerkleChannel,
        vcs::blake2_merkle::Blake2sMerkleHasher,
    },
    prover::{
        CommitmentSchemeProver, ProvingError,
        backend::simd::SimdBackend,
        poly::circle::PolyOps,
        poly::{BitReversedOrder, circle::CircleEvaluation},
        prove,
    },
};
use stwo_constraint_framework::TraceLocationAllocator;

#[derive(Debug, Clone)]
pub struct BigClaim {
    /// Claim for NTT operations
    pub f_ntt: ntt::Claim,
    /// Claim for NTT operations
    pub g_ntt: ntt::Claim,
    /// Claim for multiplication operations
    pub mul: mul::Claim,
    /// Claim for INTT operations
    pub intt: intt::Claim,
    /// Claim for range checking operations
    pub range_check: range_check::Claim,
}

#[derive(Debug, Clone)]
pub struct AllTraces {
    /// Trace columns from NTT operations
    pub f_ntt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from NTT operations
    pub g_ntt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from multiplication operations
    pub mul: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from INTT operations
    pub intt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace column from range checking: multiplicities
    pub range_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
}

impl AllTraces {
    /// Creates a new AllTraces instance with the provided traces.
    pub fn new(
        f_ntt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        g_ntt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        mul: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        intt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        range_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
    ) -> Self {
        Self {
            f_ntt,
            g_ntt,
            mul,
            intt,
            range_check,
        }
    }
}

impl BigClaim {
    /// Returns the combined log sizes for all trace columns.
    ///
    /// Concatenates the log sizes from all four components to determine
    /// the total trace structure.
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let trees = vec![
            self.f_ntt.log_sizes(),
            self.g_ntt.log_sizes(),
            self.mul.log_sizes(),
            self.intt.log_sizes(),
            self.range_check.log_sizes(),
        ];
        TreeVec::concat_cols(trees.into_iter())
    }

    /// Mixes all claim parameters into the Fiat-Shamir channel.
    ///
    /// This ensures that the proof is deterministic and all components
    /// contribute to the randomness.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.f_ntt.mix_into(channel);
        self.g_ntt.mix_into(channel);
        self.mul.mix_into(channel);
        self.intt.mix_into(channel);
        self.range_check.mix_into(channel);
    }

    /// Generates traces for all arithmetic operations.
    ///
    /// # Returns
    ///
    /// Returns a tuple containing:
    /// - A vector of all trace columns concatenated in order
    /// - An AllTraces struct containing the individual traces
    ///
    /// # Algorithm
    ///
    /// 1. Generates traces for addition, multiplication, and subtraction
    /// 2. Collects all remainder values for range checking
    /// 3. Generates the range check trace using all remainders
    /// 4. Concatenates all traces in the correct order
    pub fn gen_trace(
        &self,
    ) -> (
        Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        AllTraces,
    ) {
        let (f_ntt_trace, f_ntt_remainders, f_ntt_output) = self.f_ntt.gen_trace();
        let (g_ntt_trace, g_ntt_remainders, g_ntt_output) = self.g_ntt.gen_trace();
        let (mul_trace, mul_remainders) = self.mul.gen_trace(&f_ntt_output, &g_ntt_output);
        let (intt_trace, intt_remainders) = self
            .intt
            .gen_trace(mul_remainders.iter().map(|r| r.0).collect_vec());
        let range_check_trace = self.range_check.gen_trace(
            &chain!(
                f_ntt_remainders,
                g_ntt_remainders,
                [mul_remainders],
                intt_remainders,
            )
            .collect_vec(),
        );
        (
            chain!(
                f_ntt_trace.clone(),
                g_ntt_trace.clone(),
                mul_trace.clone(),
                intt_trace.clone(),
                [range_check_trace.clone()]
            )
            .collect_vec(),
            AllTraces::new(
                f_ntt_trace,
                g_ntt_trace,
                mul_trace,
                intt_trace,
                range_check_trace,
            ),
        )
    }
}

#[derive(Debug, Clone)]
pub struct BigInteractionClaim {
    /// Interaction claim for NTT operations
    pub f_ntt: ntt::InteractionClaim,
    /// Interaction claim for NTT operations
    pub g_ntt: ntt::InteractionClaim,
    /// Interaction claim for multiplication operations
    pub mul: mul::InteractionClaim,
    /// Interaction claim for INTT operations
    pub intt: intt::InteractionClaim,
    /// Interaction claim for range checking
    pub range_check: range_check::InteractionClaim,
}

impl BigInteractionClaim {
    /// Mixes all interaction claims into the Fiat-Shamir channel.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.f_ntt.mix_into(channel);
        self.g_ntt.mix_into(channel);
        self.mul.mix_into(channel);
        self.intt.mix_into(channel);
        self.range_check.mix_into(channel);
    }

    /// Computes the total claimed sum across all interactions.
    ///
    /// This sum should equal zero for a valid proof, ensuring that
    /// all lookup relations are properly satisfied.
    pub fn claimed_sum(&self) -> QM31 {
        self.f_ntt.claimed_sum
            + self.g_ntt.claimed_sum
            + self.mul.claimed_sum
            + self.intt.claimed_sum
            + self.range_check.claimed_sum
    }

    /// Generates interaction traces for all components.
    ///
    /// # Parameters
    ///
    /// - `lookup_elements`: The lookup elements for range checking
    /// - `add_trace`: Trace columns from modular addition
    /// - `mul_trace`: Trace columns from modular multiplication
    /// - `sub_trace`: Trace columns from modular subtraction
    /// - `range_check_trace`: Trace column from range checking
    ///
    /// # Returns
    ///
    /// Returns the combined interaction traces and the big interaction claim.
    pub fn gen_interaction_trace(
        rc_lookup_elements: &range_check::RCLookupElements,
        f_ntt_lookup_elements: &ntt::NTTLookupElements,
        g_ntt_lookup_elements: &ntt::NTTLookupElements,
        mul_lookup_elements: &mul::MulLookupElements,
        f_ntt_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        g_ntt_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        mul_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        intt_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        range_check_trace: &CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
    ) -> (
        Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Self,
    ) {
        let (f_ntt_interaction_trace, f_ntt_interaction_claim) =
            ntt::InteractionClaim::gen_interaction_trace(
                f_ntt_trace,
                rc_lookup_elements,
                f_ntt_lookup_elements,
            );
        let (g_ntt_interaction_trace, g_ntt_interaction_claim) =
            ntt::InteractionClaim::gen_interaction_trace(
                g_ntt_trace,
                rc_lookup_elements,
                g_ntt_lookup_elements,
            );
        let (mul_interaction_trace, mul_interaction_claim) =
            mul::InteractionClaim::gen_interaction_trace(
                mul_trace,
                rc_lookup_elements,
                f_ntt_lookup_elements,
                g_ntt_lookup_elements,
                mul_lookup_elements,
            );
        let (intt_interaction_trace, intt_interaction_claim) =
            intt::InteractionClaim::gen_interaction_trace(
                intt_trace,
                rc_lookup_elements,
                mul_lookup_elements,
            );
        let (range_check_interaction_trace, range_check_interaction_claim) =
            range_check::InteractionClaim::gen_interaction_trace(
                range_check_trace,
                rc_lookup_elements,
            );
        (
            chain!(
                f_ntt_interaction_trace,
                g_ntt_interaction_trace,
                mul_interaction_trace,
                intt_interaction_trace,
                range_check_interaction_trace,
            )
            .collect_vec(),
            Self {
                f_ntt: f_ntt_interaction_claim,
                g_ntt: g_ntt_interaction_claim,
                mul: mul_interaction_claim,
                intt: intt_interaction_claim,
                range_check: range_check_interaction_claim,
            },
        )
    }
}

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
    println!("big trace: {:?}", trace.len());
    claim.mix_into(channel);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace.clone());
    tree_builder.commit(channel);

    // Generate proof of work and draw lookup relations
    let interaction_pow = SimdBackend::grind(channel, 2);
    channel.mix_u64(interaction_pow);

    let rc_relations = range_check::RCLookupElements::draw(channel);
    let f_ntt_relations = ntt::NTTLookupElements::draw(channel);
    let g_ntt_relations = ntt::NTTLookupElements::draw(channel);
    let mul_relations = mul::MulLookupElements::draw(channel);

    // Generate and commit to interaction traces
    let (interaction_trace, interaction_claim) = BigInteractionClaim::gen_interaction_trace(
        &rc_relations,
        &f_ntt_relations,
        &g_ntt_relations,
        &mul_relations,
        &traces.f_ntt,
        &traces.g_ntt,
        &traces.mul,
        &traces.intt,
        &traces.range_check,
    );
    interaction_claim.mix_into(channel);
    assert_eq!(
        interaction_claim.claimed_sum(),
        <QM31 as num_traits::Zero>::zero(),
        "invalid logup sum"
    );

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
            rc_lookup_elements: rc_relations.clone(),
            ntt_lookup_elements: f_ntt_relations.clone(),
        },
        interaction_claim.f_ntt.claimed_sum,
    );
    let g_ntt_component = ntt::Component::new(
        &mut tree_span_provider,
        ntt::Eval {
            claim: ntt::Claim { log_size: 4 },
            rc_lookup_elements: rc_relations.clone(),
            ntt_lookup_elements: g_ntt_relations.clone(),
        },
        interaction_claim.g_ntt.claimed_sum,
    );
    let mul_component = mul::Component::new(
        &mut tree_span_provider,
        mul::Eval {
            claim: mul::Claim {
                log_size: POLY_LOG_SIZE,
            },
            rc_lookup_elements: rc_relations.clone(),
            f_ntt_lookup_elements: f_ntt_relations.clone(),
            g_ntt_lookup_elements: g_ntt_relations.clone(),
            mul_lookup_elements: mul_relations.clone(),
        },
        interaction_claim.mul.claimed_sum,
    );
    let intt_component = intt::Component::new(
        &mut tree_span_provider,
        intt::Eval {
            claim: intt::Claim { log_size: 4 },
            rc_lookup_elements: rc_relations.clone(),
            mul_lookup_elements: mul_relations.clone(),
        },
        interaction_claim.intt.claimed_sum,
    );
    let range_check_component = range_check::Component::new(
        &mut tree_span_provider,
        range_check::Eval {
            claim: range_check::Claim {
                log_size: range_check_log_size,
            },
            lookup_elements: rc_relations.clone(),
        },
        interaction_claim.range_check.claimed_sum,
    );

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
