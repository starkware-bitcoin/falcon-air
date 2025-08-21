// src/debug/relations.rs
use itertools::{Itertools, chain};
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

use crate::{SIGNATURE_BOUND, zq::Q};

/// Group all the *framework* components your AIR exposes. Each field can be a list so
/// you can stuff as many sub-components as you like per module.
pub struct BigAirComponents<'a> {
    pub f_ntt: &'a FrameworkComponent<crate::ntts::ntt::Eval>,
    pub g_ntt: &'a FrameworkComponent<crate::ntts::ntt::Eval>,
    pub mul: &'a FrameworkComponent<crate::polys::mul::Eval>,
    pub intt: &'a FrameworkComponent<crate::ntts::intt::Eval>,
    pub sub: &'a FrameworkComponent<crate::polys::sub::Eval>,
    pub euclidean_norm: &'a FrameworkComponent<crate::polys::euclidean_norm::Eval>,
    pub half_range_check: &'a FrameworkComponent<crate::zq::range_check::Eval<{ Q / 2 }>>,
    pub sig_bound_check: &'a FrameworkComponent<crate::zq::range_check::Eval<SIGNATURE_BOUND>>,
    pub range_check: &'a FrameworkComponent<crate::zq::range_check::Eval<Q>>,
}

/// Evaluate the committed trace back on the circle domain, collect relation entries from all
/// components, and return a *cleaned* summary (emitted - consumed per relation).
pub fn track_and_summarize_big_air_relations(
    commitment_scheme: &CommitmentSchemeProver<'_, SimdBackend, Blake2sMerkleChannel>,
    components: &BigAirComponents,
) -> RelationSummary {
    let entries = track_big_air_relations(commitment_scheme, components);
    RelationSummary::summarize_relations(&entries).cleaned()
}

/// Same as above but returns raw entries (useful if you want to inspect per-row examples).
pub fn track_big_air_relations(
    commitment_scheme: &CommitmentSchemeProver<'_, SimdBackend, Blake2sMerkleChannel>,
    components: &BigAirComponents,
) -> Vec<RelationTrackerEntry> {
    // ⚠️ This is intentionally slow — it evaluates each committed poly over its circle domain.
    let evals = commitment_scheme.trace().polys.map(|tree| {
        tree.iter()
            .map(|poly| {
                poly.evaluate(CanonicCoset::new(poly.log_size()).circle_domain())
                    .values
                    .to_cpu()
            })
            .collect_vec()
    });
    let evals = &evals.as_ref();
    let trace: &TreeVec<Vec<&Vec<M31>>> = &evals.into();

    big_air_relation_entries(components, trace)
}

fn big_air_relation_entries(
    components: &BigAirComponents,
    trace: &TreeVec<Vec<&Vec<M31>>>,
) -> Vec<RelationTrackerEntry> {
    chain!(
        add_to_relation_entries(components.f_ntt, trace),
        add_to_relation_entries(components.g_ntt, trace),
        add_to_relation_entries(components.mul, trace),
        add_to_relation_entries(components.intt, trace),
        add_to_relation_entries(components.sub, trace),
        add_to_relation_entries(components.euclidean_norm, trace),
        add_to_relation_entries(components.half_range_check, trace),
        add_to_relation_entries(components.sig_bound_check, trace),
        add_to_relation_entries(components.range_check, trace),
    )
    .collect()
}
