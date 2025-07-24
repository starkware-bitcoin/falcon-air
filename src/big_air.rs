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

use crate::zq::*;
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
    /// Claim for modular addition operations
    pub add: add::Claim,
    /// Claim for modular multiplication operations
    pub mul: mul::Claim,
    /// Claim for modular subtraction operations
    pub sub: sub::Claim,
    /// Claim for range checking operations
    pub range_check: range_check::Claim,
}

#[derive(Debug, Clone)]
pub struct AllTraces {
    /// Trace columns from modular addition: [a, b, quotient, remainder]
    add: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from modular multiplication: [a, b, quotient, remainder]
    mul: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from modular subtraction: [a, b, remainder]
    sub: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace column from range checking: multiplicities
    range_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
}

impl AllTraces {
    /// Creates a new AllTraces instance with the provided traces.
    pub fn new(
        add: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        mul: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        sub: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        range_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
    ) -> Self {
        Self {
            add,
            mul,
            sub,
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
            self.add.log_sizes(),
            self.mul.log_sizes(),
            self.sub.log_sizes(),
            self.range_check.log_sizes(),
        ];
        TreeVec::concat_cols(trees.into_iter())
    }

    /// Mixes all claim parameters into the Fiat-Shamir channel.
    ///
    /// This ensures that the proof is deterministic and all components
    /// contribute to the randomness.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.add.mix_into(channel);
        self.mul.mix_into(channel);
        self.sub.mix_into(channel);
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
        let (add_trace, add_remainders) = self.add.gen_trace();
        let (mul_trace, mul_remainders) = self.mul.gen_trace();
        let (sub_trace, sub_remainders) = self.sub.gen_trace();
        let range_check_trace =
            self.range_check
                .gen_trace(&[&add_remainders, &mul_remainders, &sub_remainders]);
        (
            add_trace
                .clone()
                .into_iter()
                .chain(mul_trace.clone())
                .chain(sub_trace.clone())
                .chain([range_check_trace.clone()])
                .collect::<Vec<_>>(),
            AllTraces::new(add_trace, mul_trace, sub_trace, range_check_trace),
        )
    }
}

#[derive(Debug, Clone)]
pub struct BigInteractionClaim {
    /// Interaction claim for modular addition
    pub add: add::InteractionClaim,
    /// Interaction claim for modular multiplication
    pub mul: mul::InteractionClaim,
    /// Interaction claim for modular subtraction
    pub sub: sub::InteractionClaim,
    /// Interaction claim for range checking
    pub range_check: range_check::InteractionClaim,
}

impl BigInteractionClaim {
    /// Mixes all interaction claims into the Fiat-Shamir channel.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.add.mix_into(channel);
        self.mul.mix_into(channel);
        self.sub.mix_into(channel);
        self.range_check.mix_into(channel);
    }

    /// Computes the total claimed sum across all interactions.
    ///
    /// This sum should equal zero for a valid proof, ensuring that
    /// all lookup relations are properly satisfied.
    pub fn claimed_sum(&self) -> QM31 {
        self.add.claimed_sum
            + self.mul.claimed_sum
            + self.sub.claimed_sum
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
        lookup_elements: &range_check::LookupElements,
        add_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        mul_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        sub_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        range_check_trace: &CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
    ) -> (
        Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Self,
    ) {
        let (add_interaction_trace, add_interaction_claim) =
            add::InteractionClaim::gen_interaction_trace(add_trace, lookup_elements);
        let (mul_interaction_trace, mul_interaction_claim) =
            mul::InteractionClaim::gen_interaction_trace(mul_trace, lookup_elements);
        let (sub_interaction_trace, sub_interaction_claim) =
            sub::InteractionClaim::gen_interaction_trace(sub_trace, lookup_elements);
        let (range_check_interaction_trace, range_check_interaction_claim) =
            range_check::InteractionClaim::gen_interaction_trace(
                range_check_trace,
                lookup_elements,
            );
        (
            add_interaction_trace
                .into_iter()
                .chain(mul_interaction_trace)
                .chain(sub_interaction_trace)
                .chain(range_check_interaction_trace)
                .collect(),
            Self {
                add: add_interaction_claim,
                mul: mul_interaction_claim,
                sub: sub_interaction_claim,
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
    let log_size = Q.ilog2() + 1;

    // Initialize Fiat-Shamir channel and commitment scheme
    let channel = &mut Blake2sChannel::default();
    let pcs_config = PcsConfig::default();
    pcs_config.mix_into(channel);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_size + pcs_config.fri_config.log_blowup_factor + 1)
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
        add: add::Claim { log_size },
        mul: mul::Claim { log_size },
        sub: sub::Claim { log_size },
        range_check: range_check::Claim { log_size },
    };
    let (trace, traces) = claim.gen_trace();
    claim.mix_into(channel);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace.clone());
    tree_builder.commit(channel);

    // Generate proof of work and draw lookup relations
    let interaction_pow = SimdBackend::grind(channel, 2);
    channel.mix_u64(interaction_pow);

    let relations = range_check::LookupElements::draw(channel);

    // Generate and commit to interaction traces
    let (interaction_trace, interaction_claim) = BigInteractionClaim::gen_interaction_trace(
        &relations,
        &traces.add,
        &traces.mul,
        &traces.sub,
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

    // Generate the final STARK proof
    prove::<SimdBackend, _>(
        &[
            &add::Component::new(
                &mut tree_span_provider,
                add::Eval {
                    claim: add::Claim { log_size },
                    lookup_elements: relations.clone(),
                },
                interaction_claim.add.claimed_sum,
            ),
            &mul::Component::new(
                &mut tree_span_provider,
                mul::Eval {
                    claim: mul::Claim { log_size },
                    lookup_elements: relations.clone(),
                },
                interaction_claim.mul.claimed_sum,
            ),
            &sub::Component::new(
                &mut tree_span_provider,
                sub::Eval {
                    claim: sub::Claim { log_size },
                    lookup_elements: relations.clone(),
                },
                interaction_claim.sub.claimed_sum,
            ),
            &range_check::Component::new(
                &mut tree_span_provider,
                range_check::Eval {
                    claim: range_check::Claim { log_size },
                    lookup_elements: relations.clone(),
                },
                interaction_claim.range_check.claimed_sum,
            ),
        ],
        channel,
        commitment_scheme,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

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
}
