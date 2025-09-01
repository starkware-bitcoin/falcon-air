//! # Debug Utilities
//!
//! This module provides debugging utilities for the Falcon-AIR STARK proof system.
//! It includes functions for constraint verification and trace validation to help
//! with development and testing of the proof components.
//!
//! # Features
//!
//! - **Constraint Verification**: Validates that all arithmetic constraints are satisfied
//! - **Trace Validation**: Ensures trace generation produces correct results
//! - **Mock Commitment Scheme**: Provides a simplified commitment scheme for testing
//! - **Debug Assertions**: Helper functions for development and debugging
//!
//! This module is primarily used during development and testing phases.

#![allow(unused)]

use std::ops::Deref;

use itertools::Itertools;
use num_traits::Zero;
use stwo::core::ColumnVec;
use stwo::core::fields::qm31::QM31;

use stwo::core::channel::{Blake2sChannel, MerkleChannel};
use stwo::core::fields::m31::M31;
use stwo::core::pcs::{TreeSubspan, TreeVec};

use stwo::core::vcs::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::{Backend, BackendForChannel, Column};
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::{
    FrameworkComponent, FrameworkEval, PREPROCESSED_TRACE_IDX, TraceLocationAllocator,
    assert_constraints_on_trace,
};

use crate::big_air::relation::INTTInputLookupElements;
use crate::big_air::{
    claim::BigClaim, interaction_claim::BigInteractionClaim, relation::LookupElements,
};
use crate::ntts::{intt, ntt, roots};
use crate::polys::sub;
use crate::polys::{euclidean_norm, mul};
use crate::zq::range_check::RangeCheck;
use crate::zq::{Q, range_check};
use crate::{HIGH_SIG_BOUND, LOW_SIG_BOUND, POLY_LOG_SIZE, POLY_SIZE, SIGNATURE_BOUND};

pub fn assert_constraints(
    s1: &[u32; POLY_SIZE],
    pk: &[u32; POLY_SIZE],
    msg_point: &[u32; POLY_SIZE],
) {
    let mut commitment_scheme = MockCommitmentScheme::default();
    let range_check_log_size = Q.ilog2() + 1;

    // Preprocessed trace.
    let (preprocessed_columns, preprocessed_columns_ids) =
        crate::big_air::claim::BigClaim::create_preprocessed_columns();

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed_columns);
    tree_builder.finalize_interaction();

    // Generate and commit to main traces
    let claim = BigClaim::new_standard();
    let (trace, traces) = claim.gen_trace(s1, pk, msg_point);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace);
    tree_builder.finalize_interaction();

    // Interaction trace.

    let mut dummy_channel = Blake2sChannel::default();
    let lookup_elements = LookupElements::draw(&mut dummy_channel);
    let mut tree_builder = commitment_scheme.tree_builder();
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
    );
    tree_builder.extend_evals(interaction_trace);
    tree_builder.finalize_interaction();

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
        intt_components,
        ibutterfly_component,
        sub_component,
        euclidean_norm_component,
        half_range_check_component,
        low_sig_bound_check_component,
        high_sig_bound_check_component,
        range_check_component,
        roots_components,
    ) = BigClaim::create_remaining_components(
        &claim,
        &lookup_elements,
        &interaction_claim,
        &mut tree_span_provider,
    );

    let components = (
        &f_ntt_butterfly_component,
        f_ntt_merges_components.as_slice(),
        &g_ntt_butterfly_component,
        g_ntt_merges_components.as_slice(),
        &mul_component,
        intt_components.as_slice(),
        &ibutterfly_component,
        &sub_component,
        &euclidean_norm_component,
        &half_range_check_component,
        &low_sig_bound_check_component,
        &high_sig_bound_check_component,
        &range_check_component,
        roots_components.as_slice(),
    );

    assert_components(commitment_scheme.trace_domain_evaluations(), components);
    assert_eq!(
        interaction_claim.claimed_sum(),
        QM31::zero(),
        "invalid logup sum"
    );
}

#[derive(Default)]
pub struct MockCommitmentScheme {
    trees: TreeVec<ColumnVec<Vec<M31>>>,
}

impl MockCommitmentScheme {
    pub fn tree_builder(&mut self) -> MockTreeBuilder<'_> {
        MockTreeBuilder {
            tree_index: self.trees.len(),
            commitment_scheme: self,
            evals: Vec::default(),
        }
    }

    pub fn next_interaction(&mut self, evals: ColumnVec<Vec<M31>>) {
        self.trees.push(evals);
    }

    /// Returns the trace domain evaluations.
    /// Used for testing purposes.
    pub fn trace_domain_evaluations(&self) -> TreeVec<ColumnVec<&Vec<M31>>> {
        self.trees.as_cols_ref()
    }
}

/// A [`TreeBuilder`] used by [`MockCommitmentScheme`] to aggregate trace values.
/// This implementation avoids low degree extension and Merkle commitments.
pub struct MockTreeBuilder<'a> {
    tree_index: usize,
    evals: ColumnVec<Vec<M31>>,
    commitment_scheme: &'a mut MockCommitmentScheme,
}
impl MockTreeBuilder<'_> {
    pub fn extend_evals<B: Backend>(
        &mut self,
        columns: impl IntoIterator<Item = CircleEvaluation<B, M31, BitReversedOrder>>,
    ) {
        self.evals
            .extend(columns.into_iter().map(|s| s.to_cpu()).collect_vec());
    }

    pub fn finalize_interaction(self) {
        self.commitment_scheme.next_interaction(self.evals);
    }
}

impl<B: Backend> TreeBuilder<B> for MockTreeBuilder<'_> {
    fn extend_evals(
        &mut self,
        columns: impl IntoIterator<Item = CircleEvaluation<B, M31, BitReversedOrder>>,
    ) -> TreeSubspan {
        let col_start = self.evals.len();
        let tree_index = self.tree_index;
        self.extend_evals(columns);
        let col_end = self.evals.len();
        TreeSubspan {
            tree_index,
            col_start,
            col_end,
        }
    }
}

// Extenders of a commitment-tree with evaluations.
trait TreeBuilder<B: Backend> {
    fn extend_evals(
        &mut self,
        columns: impl IntoIterator<Item = CircleEvaluation<B, M31, BitReversedOrder>>,
    ) -> TreeSubspan;
}

impl<B: BackendForChannel<MC>, MC: MerkleChannel> TreeBuilder<B>
    for stwo::prover::TreeBuilder<'_, '_, B, MC>
{
    fn extend_evals(
        &mut self,
        columns: impl IntoIterator<Item = CircleEvaluation<B, M31, BitReversedOrder>>,
    ) -> TreeSubspan {
        self.extend_evals(columns)
    }
}

#[allow(clippy::type_complexity)]
fn assert_components(
    trace: TreeVec<Vec<&Vec<M31>>>,
    components: (
        &FrameworkComponent<ntt::butterfly::Eval>,
        &[FrameworkComponent<ntt::Eval>],
        &FrameworkComponent<ntt::butterfly::Eval>,
        &[FrameworkComponent<ntt::Eval>],
        &FrameworkComponent<mul::Eval>,
        &[FrameworkComponent<intt::Eval>],
        &FrameworkComponent<intt::ibutterfly::Eval>,
        &FrameworkComponent<sub::Eval>,
        &FrameworkComponent<euclidean_norm::Eval>,
        &FrameworkComponent<range_check::Eval<{ Q / 2 }>>,
        &FrameworkComponent<range_check::Eval<LOW_SIG_BOUND>>,
        &FrameworkComponent<range_check::Eval<HIGH_SIG_BOUND>>,
        &FrameworkComponent<range_check::Eval<Q>>,
        &[FrameworkComponent<roots::preprocessed::Eval>],
    ),
) {
    let (
        f_ntt_butterfly,
        f_ntt_merges,
        g_ntt_butterfly,
        g_ntt_merges,
        mul,
        intt_components,
        ibutterfly,
        sub,
        euclidean_norm,
        half_range_check,
        low_sig_bound_check,
        high_sig_bound_check,
        range_check,
        roots,
    ) = components;
    println!("f_ntt_butterfly");
    assert_component(f_ntt_butterfly, &trace);
    println!("f_ntt_merges");
    for (i, merge) in f_ntt_merges.iter().enumerate() {
        println!("merge {}", i);
        assert_component(merge, &trace);
    }
    println!("g_ntt_butterfly");
    assert_component(g_ntt_butterfly, &trace);
    println!("g_ntt_merges");
    for (i, merge) in g_ntt_merges.iter().enumerate() {
        println!("merge {}", i);
        assert_component(merge, &trace);
    }
    println!("mul");
    assert_component(mul, &trace);
    println!("intt");
    for (i, intt) in intt_components.iter().enumerate() {
        println!("split {}", i);
        assert_component(intt, &trace);
    }
    println!("ibutterfly");
    assert_component(ibutterfly, &trace);
    println!("sub");
    assert_component(sub, &trace);
    println!("euclidean_norm");
    assert_component(euclidean_norm, &trace);
    println!("half_range_check");
    assert_component(half_range_check, &trace);
    println!("low_sig_bound_check");
    assert_component(low_sig_bound_check, &trace);
    println!("high_sig_bound_check");
    assert_component(high_sig_bound_check, &trace);
    println!("range_check");
    assert_component(range_check, &trace);
    println!("roots");
    for (i, root) in roots.iter().enumerate() {
        println!("root {}", i);
        assert_component(root, &trace);
    }
}

fn assert_component<E: FrameworkEval + Sync>(
    component: &FrameworkComponent<E>,
    trace: &TreeVec<Vec<&Vec<M31>>>,
) {
    let mut component_trace = trace
        .sub_tree(component.trace_locations())
        .map(|tree| tree.into_iter().cloned().collect_vec());
    component_trace[PREPROCESSED_TRACE_IDX] = component
        .preproccessed_column_indices()
        .iter()
        .map(|idx| trace[PREPROCESSED_TRACE_IDX][*idx])
        .collect();

    let log_size = component.log_size();

    let component_eval = component.deref();
    assert_constraints_on_trace(
        &component_trace,
        log_size,
        |eval| {
            component_eval.evaluate(eval);
        },
        component.claimed_sum(),
    );
}
