//! # Debug Utilities
//!
//! This module provides comprehensive debugging utilities for the Falcon-AIR STARK proof system.
//! It includes functions for constraint verification, trace validation, and testing infrastructure
//! to help with development and validation of the proof components.
//!
//! # Features
//!
//! - **Constraint Verification**: Validates that all arithmetic constraints are satisfied
//! - **Trace Validation**: Ensures trace generation produces correct results
//! - **Mock Commitment Scheme**: Provides a simplified commitment scheme for testing
//! - **Component Testing**: Comprehensive testing of all proof components
//! - **Debug Assertions**: Helper functions for development and debugging
//!
//! # Usage
//!
//! This module is primarily used during development and testing phases to:
//! - Verify the correctness of STARK proof generation
//! - Test individual components in isolation
//! - Debug constraint violations and trace errors
//! - Validate the complete proof system integration
//!
//! # Testing Strategy
//!
//! The debug utilities provide a complete testing framework that:
//! - Tests all arithmetic operations (addition, multiplication, subtraction)
//! - Validates NTT and INTT operations
//! - Checks range checking and signature bound validation
//! - Verifies lookup relations and interaction claims

pub mod relation_tracker;

use std::ops::Deref;

use itertools::Itertools;
use num_traits::Zero;
use stwo::core::ColumnVec;
use stwo::core::fields::qm31::QM31;

use stwo::core::channel::{Blake2sChannel, MerkleChannel};
use stwo::core::fields::m31::M31;
use stwo::core::pcs::{TreeSubspan, TreeVec};

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
use crate::ntts::{intt, ntt, roots};
use crate::polys::sub;
use crate::polys::{euclidean_norm, mul};

use crate::zq::{Q, range_check};
use crate::{HIGH_SIG_BOUND, LOW_SIG_BOUND, POLY_SIZE};

/// Asserts that all constraints are satisfied for the given Falcon signature inputs.
///
/// This function performs comprehensive constraint verification for the complete
/// STARK proof system, including all arithmetic operations, NTT transformations,
/// range checking, and signature validation.
///
/// # Parameters
///
/// - `s1`: The signature polynomial S1 with coefficients in [0, Q)
/// - `pk`: The public key polynomial with coefficients in [0, Q)
/// - `msg_point`: The message point polynomial with coefficients in [0, Q)
///
/// # What This Function Tests
///
/// 1. **Preprocessed Columns**: Range check tables and root of unity values
/// 2. **Main Traces**: All arithmetic operations and NTT transformations
/// 3. **Interaction Traces**: Lookup relations and range checking
/// 4. **Component Constraints**: Individual component constraint satisfaction
/// 5. **Lookup Protocol**: Validation that all lookup relations sum to zero
///
/// # Panics
///
/// This function will panic if any constraint is violated, providing detailed
/// error information about which component failed validation.
pub fn assert_constraints(
    s1: &[u32; POLY_SIZE],
    pk: &[u32; POLY_SIZE],
    msg_point: &[u32; POLY_SIZE],
) {
    let mut commitment_scheme = MockCommitmentScheme::default();

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
    let (interaction_trace, interaction_claim) =
        BigInteractionClaim::gen_interaction_trace(&lookup_elements, &traces);
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
        inv_roots_components,
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
        inv_roots_components.as_slice(),
    );

    assert_components(commitment_scheme.trace_domain_evaluations(), components);
    assert_eq!(
        interaction_claim.claimed_sum(),
        QM31::zero(),
        "invalid logup sum"
    );
}

/// Mock commitment scheme for testing and debugging purposes.
///
/// This struct provides a simplified commitment scheme that avoids the complexity
/// of low degree extension and Merkle commitments. It's used during development
/// and testing to validate constraint satisfaction without the overhead of
/// full cryptographic commitments.
///
/// # Fields
///
/// - `trees`: A collection of trace trees containing the evaluation data
///   for all proof components (preprocessed, main, and interaction traces)
///
/// # Usage
///
/// This mock scheme is used in the debug utilities to:
/// - Validate constraint satisfaction across all components
/// - Test trace generation and evaluation logic
/// - Debug constraint violations without cryptographic overhead
/// - Provide a simplified testing environment
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

/// A mock tree builder used by [`MockCommitmentScheme`] to aggregate trace values.
///
/// This implementation provides a simplified tree building interface that avoids
/// the complexity of low degree extension and Merkle commitments. It's designed
/// for testing and debugging purposes where cryptographic security is not required.
///
/// # Fields
///
/// - `tree_index`: The index of the current tree being built
/// - `evals`: The evaluation data for the current tree
/// - `commitment_scheme`: Reference to the parent commitment scheme
///
/// # Purpose
///
/// This mock builder is used to:
/// - Collect trace evaluations from proof components
/// - Organize data into trace trees for validation
/// - Provide a simplified interface for testing
/// - Avoid cryptographic overhead during development
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
pub trait TreeBuilder<B: Backend> {
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

/// Asserts that all proof components satisfy their constraints.
///
/// This function performs comprehensive constraint verification across all
/// components of the Big AIR proof system. It tests each component individually
/// and validates that all constraints are satisfied.
///
/// # Parameters
///
/// - `trace`: The complete trace data containing all evaluation values
/// - `components`: Tuple containing all proof components to be tested
///
/// # Components Tested
///
/// 1. **NTT Components**: Forward NTT butterfly and merge operations
/// 2. **Arithmetic Components**: Multiplication, subtraction, and Euclidean norm
/// 3. **Range Check Components**: Various range checking operations
/// 4. **Root Components**: Precomputed roots of unity validation
///
/// # Testing Process
///
/// For each component, this function:
/// - Extracts the relevant trace data for that component
/// - Evaluates all constraints defined by the component
/// - Verifies that the claimed sums are correct
/// - Reports any constraint violations with detailed information
///
/// # Panics
///
/// This function will panic if any component fails constraint validation,
/// providing detailed information about which component and constraint failed.
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
        &[FrameworkComponent<roots::inv_preprocessed::Eval>],
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
        inv_roots,
    ) = components;
    // Test forward NTT butterfly operations for F polynomial
    println!("f_ntt_butterfly");
    assert_component(f_ntt_butterfly, &trace);

    // Test forward NTT merge operations for F polynomial
    println!("f_ntt_merges");
    for (i, merge) in f_ntt_merges.iter().enumerate() {
        println!("merge {}", i);
        assert_component(merge, &trace);
    }

    // Test forward NTT butterfly operations for G polynomial
    println!("g_ntt_butterfly");
    assert_component(g_ntt_butterfly, &trace);

    // Test forward NTT merge operations for G polynomial
    println!("g_ntt_merges");
    for (i, merge) in g_ntt_merges.iter().enumerate() {
        println!("merge {}", i);
        assert_component(merge, &trace);
    }

    // Test modular multiplication operations
    println!("mul");
    assert_component(mul, &trace);

    // Test inverse NTT split operations
    println!("intt");
    for (i, intt) in intt_components.iter().enumerate() {
        println!("split {}", i);
        assert_component(intt, &trace);
    }

    // Test inverse NTT butterfly operations
    println!("ibutterfly");
    assert_component(ibutterfly, &trace);

    // Test modular subtraction operations
    println!("sub");
    assert_component(sub, &trace);

    // Test Euclidean norm computation
    println!("euclidean_norm");
    assert_component(euclidean_norm, &trace);

    // Test half-range checking (0 to Q/2)
    println!("half_range_check");
    assert_component(half_range_check, &trace);

    // Test low signature bound checking
    println!("low_sig_bound_check");
    assert_component(low_sig_bound_check, &trace);

    // Test high signature bound checking
    println!("high_sig_bound_check");
    assert_component(high_sig_bound_check, &trace);

    // Test full range checking (0 to Q)
    println!("range_check");
    assert_component(range_check, &trace);

    // Test precomputed roots of unity validation
    println!("roots");
    for (i, root) in roots.iter().enumerate() {
        println!("root {}", i);
        assert_component(root, &trace);
    }

    // Test precomputed inverse roots of unity validation
    println!("inv_roots");
    for (i, inv_root) in inv_roots.iter().enumerate() {
        println!("inv_root {}", i);
        assert_component(inv_root, &trace);
    }
}

/// Asserts that a single proof component satisfies all its constraints.
///
/// This function validates that a specific proof component correctly
/// evaluates all its constraints using the provided trace data.
///
/// # Type Parameters
///
/// - `E`: The evaluation type that implements `FrameworkEval + Sync`
///
/// # Parameters
///
/// - `component`: The proof component to be tested
/// - `trace`: The complete trace data containing all evaluation values
///
/// # What This Function Tests
///
/// 1. **Trace Extraction**: Extracts the relevant trace data for the component
/// 2. **Constraint Evaluation**: Evaluates all constraints defined by the component
/// 3. **Claimed Sum Validation**: Verifies that the component's claimed sum is correct
/// 4. **Constraint Satisfaction**: Ensures all constraints are satisfied
///
/// # Panics
///
/// This function will panic if the component fails constraint validation,
/// providing detailed information about which constraint failed.
fn assert_component<E: FrameworkEval + Sync>(
    component: &FrameworkComponent<E>,
    trace: &TreeVec<Vec<&Vec<M31>>>,
) {
    // Extract the trace data relevant to this specific component
    // This includes the main trace and any interaction traces needed
    let mut component_trace = trace
        .sub_tree(component.trace_locations())
        .map(|tree| tree.into_iter().cloned().collect_vec());

    // Set up the preprocessed columns for this component
    // These contain lookup tables and other precomputed values
    component_trace[PREPROCESSED_TRACE_IDX] = component
        .preproccessed_column_indices()
        .iter()
        .map(|idx| trace[PREPROCESSED_TRACE_IDX][*idx])
        .collect();

    // Get the log size for this component's trace
    let log_size = component.log_size();

    // Get a reference to the component's evaluation logic
    let component_eval = component.deref();

    // Assert that all constraints are satisfied on the component's trace
    // This validates the mathematical correctness of the component
    assert_constraints_on_trace(
        &component_trace,
        log_size,
        |eval| {
            component_eval.evaluate(eval);
        },
        component.claimed_sum(),
    );
}
