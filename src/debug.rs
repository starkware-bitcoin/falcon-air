// Copy pasted from cairo m
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

use crate::big_air::{
    claim::BigClaim, interaction_claim::BigInteractionClaim, relation::LookupElements,
};
use crate::ntts::{intt, ntt};
use crate::polys::sub;
use crate::polys::{euclidean_norm, mul};
use crate::zq::range_check::RangeCheck;
use crate::zq::{Q, range_check};
use crate::{POLY_LOG_SIZE, POLY_SIZE, SIGNATURE_BOUND};

pub fn assert_constraints(
    s1: &[u32; POLY_SIZE],
    pk: &[u32; POLY_SIZE],
    msg_point: &[u32; POLY_SIZE],
) {
    let mut commitment_scheme = MockCommitmentScheme::default();
    let range_check_log_size = Q.ilog2() + 1;

    // Preprocessed trace.
    let range_check_preprocessed = range_check::RangeCheck::<Q>::gen_column_simd();
    let half_range_check_preprocessed = range_check::RangeCheck::<{ Q / 2 }>::gen_column_simd();

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals([range_check_preprocessed, half_range_check_preprocessed]);
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
        sub: sub::Claim {
            log_size: POLY_LOG_SIZE,
        },
        euclidean_norm: euclidean_norm::Claim {
            log_size: POLY_LOG_SIZE,
        },
        half_range_check: range_check::Claim {
            log_size: range_check_log_size - 1,
        },
        sig_bound_check: range_check::Claim {
            log_size: SIGNATURE_BOUND.next_power_of_two().ilog2(),
        },
        range_check: range_check::Claim {
            log_size: range_check_log_size,
        },
    };
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
        &traces.f_ntt,
        &traces.g_ntt,
        &traces.mul,
        &traces.intt,
        &traces.sub,
        &traces.euclidean_norm,
        &traces.half_range_check,
        &traces.sig_bound_check,
        &traces.range_check,
    );
    tree_builder.extend_evals(interaction_trace);
    tree_builder.finalize_interaction();

    let mut tree_span_provider = TraceLocationAllocator::new_with_preproccessed_columns(&[
        RangeCheck::<Q>::id(),
        RangeCheck::<{ Q / 2 }>::id(),
    ]);

    let components = (
        &ntt::Component::new(
            &mut tree_span_provider,
            ntt::Eval {
                claim: claim.f_ntt,
                rc_lookup_elements: lookup_elements.rc.clone(),
                ntt_lookup_elements: lookup_elements.f_ntt.clone(),
            },
            interaction_claim.f_ntt.claimed_sum,
        ),
        &ntt::Component::new(
            &mut tree_span_provider,
            ntt::Eval {
                claim: claim.g_ntt,
                rc_lookup_elements: lookup_elements.rc.clone(),
                ntt_lookup_elements: lookup_elements.g_ntt.clone(),
            },
            interaction_claim.g_ntt.claimed_sum,
        ),
        &mul::Component::new(
            &mut tree_span_provider,
            mul::Eval {
                claim: claim.mul,
                rc_lookup_elements: lookup_elements.rc.clone(),
                f_ntt_lookup_elements: lookup_elements.f_ntt.clone(),
                g_ntt_lookup_elements: lookup_elements.g_ntt.clone(),
                mul_lookup_elements: lookup_elements.mul.clone(),
            },
            interaction_claim.mul.claimed_sum,
        ),
        &intt::Component::new(
            &mut tree_span_provider,
            intt::Eval {
                claim: claim.intt,
                rc_lookup_elements: lookup_elements.rc.clone(),
                mul_lookup_elements: lookup_elements.mul.clone(),
                intt_lookup_elements: lookup_elements.intt.clone(),
            },
            interaction_claim.intt.claimed_sum,
        ),
        &sub::Component::new(
            &mut tree_span_provider,
            sub::Eval {
                claim: claim.sub,
                rc_lookup_elements: lookup_elements.rc.clone(),
                intt_lookup_elements: lookup_elements.intt.clone(),
                sub_lookup_elements: lookup_elements.sub.clone(),
            },
            interaction_claim.sub.claimed_sum,
        ),
        &euclidean_norm::Component::new(
            &mut tree_span_provider,
            euclidean_norm::Eval {
                claim: claim.euclidean_norm,
                half_rc_lookup_elements: lookup_elements.half_range_check.clone(),
                s0_lookup_elements: lookup_elements.sub.clone(),
                signature_bound_lookup_elements: lookup_elements.sig_bound_check.clone(),
            },
            interaction_claim.euclidean_norm.claimed_sum,
        ),
        &range_check::Component::new(
            &mut tree_span_provider,
            range_check::Eval::<{ Q / 2 }> {
                claim: claim.half_range_check,
                lookup_elements: lookup_elements.half_range_check.clone(),
            },
            interaction_claim.half_range_check.claimed_sum,
        ),
        &range_check::Component::new(
            &mut tree_span_provider,
            range_check::Eval::<SIGNATURE_BOUND> {
                claim: claim.sig_bound_check,
                lookup_elements: lookup_elements.sig_bound_check.clone(),
            },
            interaction_claim.sig_bound_check.claimed_sum,
        ),
        &range_check::Component::new(
            &mut tree_span_provider,
            range_check::Eval {
                claim: claim.range_check,
                lookup_elements: lookup_elements.rc.clone(),
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
        &FrameworkComponent<sub::Eval>,
        &FrameworkComponent<euclidean_norm::Eval>,
        &FrameworkComponent<range_check::Eval<{ Q / 2 }>>,
        &FrameworkComponent<range_check::Eval<SIGNATURE_BOUND>>,
        &FrameworkComponent<range_check::Eval<Q>>,
    ),
) {
    let (
        f_ntt,
        g_ntt,
        mul,
        intt,
        sub,
        euclidean_norm,
        half_range_check,
        sig_bound_check,
        range_check,
    ) = components;
    println!("f_ntt");
    assert_component(f_ntt, &trace);
    println!("g_ntt");
    assert_component(g_ntt, &trace);
    println!("mul");
    assert_component(mul, &trace);
    println!("intt");
    assert_component(intt, &trace);
    println!("sub");
    assert_component(sub, &trace);
    println!("euclidean_norm");
    assert_component(euclidean_norm, &trace);
    println!("half_range_check");
    assert_component(half_range_check, &trace);
    println!("sig_bound_check");
    assert_component(sig_bound_check, &trace);
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
