//! # Relation Tracker
//!
//! This module provides comprehensive utilities for tracking and summarizing relation entries
//! across all components in the Big AIR STARK proof system.
//!
//! # Overview
//!
//! The relation tracker is a crucial component that ensures the mathematical soundness
//! of the STARK proof system by validating that all lookup relations are properly
//! balanced across all proof components.
//!
//! # Features
//!
//! - **Relation Tracking**: Collects relation entries from all proof components
//! - **Relation Summarization**: Provides cleaned summaries of relation usage
//! - **Component Integration**: Integrates with all Big AIR components
//! - **Debug Support**: Helps with verification and debugging of proof relations

//!
//! This module is used to ensure that all lookup relations are properly balanced
//! and that the proof system maintains soundness across all components.
use itertools::Itertools;
use stwo::core::fields::m31::M31;
use stwo::core::pcs::TreeVec;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::CommitmentSchemeProver;
use stwo::prover::backend::Column;
use stwo::prover::backend::simd::SimdBackend;

use stwo_constraint_framework::FrameworkComponent;
use stwo_constraint_framework::relation_tracker::{
    RelationSummary, RelationTrackerEntry, add_to_relation_entries,
};

use crate::{HIGH_SIG_BOUND, LOW_SIG_BOUND, zq::Q};

/// Groups all framework components exposed by the Big AIR system.
///
/// This struct provides a comprehensive view of all proof components
/// in the Big AIR STARK proof system. Each field can contain either
/// a single component or a list of components, allowing for flexible
/// component organization and testing.
///
/// # Component Categories
///
/// - **NTT Operations**: Forward and inverse Number Theoretic Transforms
/// - **Arithmetic Operations**: Modular arithmetic and polynomial operations
/// - **Range Checking**: Various range validation components
/// - **Root Validation**: Precomputed roots of unity validation
///
/// # Lifetime Parameter
///
/// - `'a`: The lifetime of the component references
///
/// # Usage
///
/// This struct is used by the relation tracker to:
/// - Collect relation entries from all components
/// - Validate lookup protocol correctness
/// - Provide comprehensive proof system analysis
/// - Support debugging and verification efforts
pub struct BigAirComponents<'a> {
    pub f_ntt_butterfly: &'a FrameworkComponent<crate::ntts::ntt::butterfly::Eval>,
    pub f_ntt_merges: &'a [FrameworkComponent<crate::ntts::ntt::Eval>],
    pub g_ntt_butterfly: &'a FrameworkComponent<crate::ntts::ntt::butterfly::Eval>,
    pub g_ntt_merges: &'a [FrameworkComponent<crate::ntts::ntt::Eval>],
    pub mul: &'a FrameworkComponent<crate::polys::mul::Eval>,
    pub intt_merges: &'a [FrameworkComponent<crate::ntts::intt::Eval>],
    pub ibutterfly: &'a FrameworkComponent<crate::ntts::intt::ibutterfly::Eval>,
    pub sub: &'a FrameworkComponent<crate::polys::sub::Eval>,
    pub euclidean_norm: &'a FrameworkComponent<crate::polys::euclidean_norm::Eval>,
    pub half_range_check: &'a FrameworkComponent<crate::zq::range_check::Eval<{ Q / 2 }>>,
    pub low_sig_bound_check: &'a FrameworkComponent<crate::zq::range_check::Eval<LOW_SIG_BOUND>>,
    pub high_sig_bound_check: &'a FrameworkComponent<crate::zq::range_check::Eval<HIGH_SIG_BOUND>>,
    pub range_check: &'a FrameworkComponent<crate::zq::range_check::Eval<Q>>,
    pub roots: &'a [FrameworkComponent<crate::ntts::roots::preprocessed::Eval>],
    pub inv_roots: &'a [FrameworkComponent<crate::ntts::roots::inv_preprocessed::Eval>],
}

/// Evaluates the committed trace on the circle domain and summarizes relation entries.
///
/// This function performs a comprehensive analysis of all lookup relations across
/// all proof components. It evaluates the committed trace data, collects relation
/// entries from each component, and returns a cleaned summary showing the net
/// balance (emitted - consumed) for each relation type.
///
/// # Parameters
///
/// - `commitment_scheme`: The commitment scheme containing the committed trace data
/// - `components`: All proof components to be analyzed
///
/// # Returns
///
/// Returns a `RelationSummary` containing the cleaned relation balances.
///
/// # Process
///
/// 1. **Trace Evaluation**: Evaluates committed polynomials on their circle domains
/// 2. **Relation Collection**: Gathers relation entries from all components
/// 3. **Summary Generation**: Creates a cleaned summary of relation balances
/// 4. **Validation**: Ensures all relations sum to zero for soundness
///
/// # Performance Note
///
/// This function is intentionally slow as it evaluates each committed polynomial
/// over its full circle domain for comprehensive analysis.
pub fn track_and_summarize_big_air_relations(
    commitment_scheme: &CommitmentSchemeProver<'_, SimdBackend, Blake2sMerkleChannel>,
    components: &BigAirComponents,
) -> RelationSummary {
    let entries = track_big_air_relations(commitment_scheme, components);
    RelationSummary::summarize_relations(&entries).cleaned()
}

/// Evaluates the committed trace and returns raw relation entries for detailed inspection.
///
/// This function is similar to `track_and_summarize_big_air_relations` but returns
/// the raw relation entries instead of a summarized view. This is useful for
/// detailed debugging and inspection of individual relation entries.
///
/// # Parameters
///
/// - `commitment_scheme`: The commitment scheme containing the committed trace data
/// - `components`: All proof components to be analyzed
///
/// # Returns
///
/// Returns a vector of `RelationTrackerEntry` containing all raw relation entries
/// from all components, useful for per-row inspection and debugging.
///
/// # Use Cases
///
/// - **Detailed Debugging**: Inspect individual relation entries
/// - **Row-by-Row Analysis**: Analyze specific trace rows
/// - **Custom Summarization**: Create custom relation summaries
/// - **Verification**: Validate specific component behavior
pub fn track_big_air_relations(
    commitment_scheme: &CommitmentSchemeProver<'_, SimdBackend, Blake2sMerkleChannel>,
    components: &BigAirComponents,
) -> Vec<RelationTrackerEntry> {
    // ⚠️ This is intentionally slow — it evaluates each committed poly over its circle domain.
    // This comprehensive evaluation is necessary for accurate relation tracking and validation.
    let evals = commitment_scheme.trace().polys.map(|tree| {
        tree.iter()
            .map(|poly| {
                // Evaluate each committed polynomial on its circle domain
                // This converts the committed data back to evaluation form
                poly.evaluate(CanonicCoset::new(poly.log_size()).circle_domain())
                    .values
                    .to_cpu()
            })
            .collect_vec()
    });

    // Convert the evaluations to the format expected by the relation tracker
    let evals = &evals.as_ref();
    let trace: &TreeVec<Vec<&Vec<M31>>> = &evals.into();

    big_air_relation_entries(components, trace)
}

/// Collects relation entries from all Big AIR components.
///
/// This function iterates through all proof components and collects their
/// relation entries. It ensures that all lookup relations are properly
/// tracked for validation and debugging purposes.
///
/// # Parameters
///
/// - `components`: All proof components to be analyzed
/// - `trace`: The trace data containing all evaluation values
///
/// # Returns
///
/// Returns a vector containing all relation entries from all components.
///
/// # Component Coverage
///
/// This function covers all component types:
/// - NTT operations (forward and inverse)
/// - Arithmetic operations (multiplication, subtraction, Euclidean norm)
/// - Range checking operations
/// - Root of unity validation
fn big_air_relation_entries(
    components: &BigAirComponents,
    trace: &TreeVec<Vec<&Vec<M31>>>,
) -> Vec<RelationTrackerEntry> {
    // Initialize the collection vector for all relation entries
    let mut entries = vec![];

    // Collect relation entries from forward NTT butterfly operations for F polynomial
    entries.extend(add_to_relation_entries(components.f_ntt_butterfly, trace));

    // Collect relation entries from forward NTT merge operations for F polynomial
    for merge in components.f_ntt_merges.iter() {
        entries.extend(add_to_relation_entries(merge, trace));
    }

    // Collect relation entries from forward NTT butterfly operations for G polynomial
    entries.extend(add_to_relation_entries(components.g_ntt_butterfly, trace));

    // Collect relation entries from forward NTT merge operations for G polynomial
    for merge in components.g_ntt_merges.iter() {
        entries.extend(add_to_relation_entries(merge, trace));
    }

    // Collect relation entries from modular multiplication operations
    entries.extend(add_to_relation_entries(components.mul, trace));

    // Collect relation entries from inverse NTT merge operations
    for merge in components.intt_merges.iter() {
        entries.extend(add_to_relation_entries(merge, trace));
    }

    // Collect relation entries from inverse NTT butterfly operations
    entries.extend(add_to_relation_entries(components.ibutterfly, trace));

    // Collect relation entries from modular subtraction operations
    entries.extend(add_to_relation_entries(components.sub, trace));

    // Collect relation entries from Euclidean norm computation
    entries.extend(add_to_relation_entries(components.euclidean_norm, trace));

    // Collect relation entries from half-range checking (0 to Q/2)
    entries.extend(add_to_relation_entries(components.half_range_check, trace));

    // Collect relation entries from low signature bound checking
    entries.extend(add_to_relation_entries(
        components.low_sig_bound_check,
        trace,
    ));

    // Collect relation entries from high signature bound checking
    entries.extend(add_to_relation_entries(
        components.high_sig_bound_check,
        trace,
    ));

    // Collect relation entries from full range checking (0 to Q)
    entries.extend(add_to_relation_entries(components.range_check, trace));

    // Collect relation entries from precomputed roots of unity validation
    for root in components.roots.iter() {
        entries.extend(add_to_relation_entries(root, trace));
    }

    // Collect relation entries from precomputed inverse roots of unity validation
    for inv_root in components.inv_roots.iter() {
        entries.extend(add_to_relation_entries(inv_root, trace));
    }

    // Return all collected relation entries for analysis and validation
    entries
}
