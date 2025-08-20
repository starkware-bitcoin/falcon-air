// Adapted from https://github.com/starkware-libs/stwo-cairo/blob/main/stwo_cairo_prover/crates/prover/src/debug_tools/assert_constraints.rs
#![allow(unused)]

use std::ops::Deref;

use itertools::Itertools;
use stwo::core::ColumnVec;

use stwo::core::channel::{Blake2sChannel, MerkleChannel};
use stwo::core::fields::m31::M31;
use stwo::core::pcs::{TreeSubspan, TreeVec};

use stwo::core::vcs::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::{Backend, BackendForChannel, Column};
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::{
    FrameworkComponent, FrameworkEval, PREPROCESSED_TRACE_IDX, TraceLocationAllocator,
    assert_constraints_on_trace,
};

use crate::POLY_LOG_SIZE;
use crate::big_air::{BigClaim, BigInteractionClaim};
use crate::ntts::{intt, mul, ntt};
use crate::zq::range_check::RangeCheck12289;
use crate::zq::{Q, range_check};

pub fn assert_constraints() {
    let mut commitment_scheme = MockCommitmentScheme::default();
    let range_check_log_size = Q.ilog2() + 1;

    // Preprocessed trace.
    let range_check_preprocessed = range_check::RangeCheck12289::gen_column_simd();

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals([range_check_preprocessed]);
    tree_builder.finalize_interaction();

    // Base trace.
    let claim = BigClaim {
        f_ntt: ntt::Claim {
            log_size: POLY_LOG_SIZE,
        },
        g_ntt: ntt::Claim {
            log_size: POLY_LOG_SIZE,
        },
        mul: mul::Claim {
            log_size: POLY_LOG_SIZE,
        },
        intt: intt::Claim {
            log_size: POLY_LOG_SIZE,
        },
        range_check: range_check::Claim {
            log_size: range_check_log_size,
        },
    };
    let (trace, traces) = claim.gen_trace();
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace);
    tree_builder.finalize_interaction();

    // Interaction trace.

    let mut dummy_channel = Blake2sChannel::default();
    let rc_relations = range_check::LookupElements::draw(&mut dummy_channel);
    let f_ntt_relations = ntt::LookupElements::draw(&mut dummy_channel);
    let g_ntt_relations = ntt::LookupElements::draw(&mut dummy_channel);
    let mul_relations = mul::LookupElements::draw(&mut dummy_channel);
    let mut tree_builder = commitment_scheme.tree_builder();
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
    tree_builder.extend_evals(interaction_trace);
    tree_builder.finalize_interaction();

    let mut tree_span_provider =
        TraceLocationAllocator::new_with_preproccessed_columns(&[RangeCheck12289::id()]);

    let components = (
        &ntt::Component::new(
            &mut tree_span_provider,
            ntt::Eval {
                claim: ntt::Claim {
                    log_size: POLY_LOG_SIZE,
                },
                rc_lookup_elements: rc_relations.clone(),
                ntt_lookup_elements: f_ntt_relations.clone(),
            },
            interaction_claim.f_ntt.claimed_sum,
        ),
        &ntt::Component::new(
            &mut tree_span_provider,
            ntt::Eval {
                claim: ntt::Claim {
                    log_size: POLY_LOG_SIZE,
                },
                rc_lookup_elements: rc_relations.clone(),
                ntt_lookup_elements: g_ntt_relations.clone(),
            },
            interaction_claim.g_ntt.claimed_sum,
        ),
        &mul::Component::new(
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
        ),
        &intt::Component::new(
            &mut tree_span_provider,
            intt::Eval {
                claim: intt::Claim {
                    log_size: POLY_LOG_SIZE,
                },
                rc_lookup_elements: rc_relations.clone(),
                mul_lookup_elements: mul_relations.clone(),
            },
            interaction_claim.intt.claimed_sum,
        ),
        &range_check::Component::new(
            &mut tree_span_provider,
            range_check::Eval {
                claim: range_check::Claim {
                    log_size: range_check_log_size,
                },
                lookup_elements: rc_relations.clone(),
            },
            interaction_claim.range_check.claimed_sum,
        ),
    );

    assert_components(commitment_scheme.trace_domain_evaluations(), components);
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
        &FrameworkComponent<ntt::Eval>,
        &FrameworkComponent<ntt::Eval>,
        &FrameworkComponent<mul::Eval>,
        &FrameworkComponent<intt::Eval>,
        &FrameworkComponent<range_check::Eval>,
    ),
) {
    let (f_ntt, g_ntt, mul, intt, range_check) = components;
    println!("f_ntt");
    assert_component(f_ntt, &trace);
    println!("g_ntt");
    assert_component(g_ntt, &trace);
    println!("mul");
    assert_component(mul, &trace);
    println!("intt");
    assert_component(intt, &trace);
    println!("range_check");
    assert_component(range_check, &trace);
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
