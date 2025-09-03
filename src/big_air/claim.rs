//! # Big AIR Claims
//!
//! This module defines the claim structures for the Big AIR STARK proof system.
//! It contains the main claim struct that combines all individual component claims
//! and the trace structures used for proof generation.
//!
//! # Components
//!
//! - **BigClaim**: Main claim struct containing all component claims
//! - **AllTraces**: Structure containing all trace data for proof generation
//! - **Trace Generation**: Functions for generating traces from claims
//!
//! This module serves as the central coordination point for all proof components
//! in the Falcon signature scheme implementation.

use crate::{
    HIGH_SIG_BOUND, LOW_SIG_BOUND, POLY_LOG_SIZE, POLY_SIZE,
    big_air::relation::InputLookupElements,
    ntts::{intt, ntt, roots},
    polys::{euclidean_norm, mul, sub},
    zq::{Q, range_check},
};
use itertools::{Itertools, chain};
use stwo::{
    core::{channel::Channel, fields::m31::M31},
    prover::{
        backend::simd::SimdBackend,
        poly::{BitReversedOrder, circle::CircleEvaluation},
    },
};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

#[derive(Debug, Clone)]
pub struct BigClaim {
    /// Claim for butterfly operations
    pub f_ntt_butterfly: ntt::butterfly::Claim,
    /// Claim for NTT operations
    pub f_ntt_merges: Vec<ntt::Claim>,
    /// Claim for butterfly operations
    pub g_ntt_butterfly: ntt::butterfly::Claim,
    /// Claim for NTT operations
    pub g_ntt_merges: Vec<ntt::Claim>,
    /// Claim for multiplication operations
    pub mul: mul::Claim,
    /// Claim for INTT operations
    pub intt_merges: Vec<intt::Claim>,
    /// Claim for INTT operations
    pub ibutterfly: intt::ibutterfly::Claim,
    /// Claim for subtraction operations
    pub sub: sub::Claim,
    /// Claim for euclidean norm operations
    pub euclidean_norm: euclidean_norm::Claim,
    /// Claim for half range checking operations
    pub half_range_check: range_check::Claim,
    /// Claim for signature bound checking operations
    pub low_sig_bound_check: range_check::Claim,
    /// Claim for signature bound checking operations
    pub high_sig_bound_check: range_check::Claim,
    /// Claim for range checking operations
    pub range_check: range_check::Claim,
    /// Claim for roots operations
    pub roots: Vec<roots::preprocessed::Claim>,
    /// Claim for inverse roots operations
    pub inv_roots: Vec<roots::inv_preprocessed::Claim>,
}

#[derive(Debug, Clone)]
pub struct AllTraces {
    /// Trace columns from butterfly operations
    pub f_ntt_butterfly: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from NTT operations
    pub f_ntt_merges: Vec<Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>>,
    /// Trace columns from butterfly operations
    pub g_ntt_butterfly: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from NTT operations
    pub g_ntt_merges: Vec<Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>>,
    /// Trace columns from multiplication operations
    pub mul: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from INTT operations
    pub intt_merges: Vec<Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>>,
    /// Trace columns from INTT operations
    pub ibutterfly: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from subtraction operations
    pub sub: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from euclidean norm operations
    pub euclidean_norm: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace column from half range checking: multiplicities
    pub half_range_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
    /// Trace column from signature bound checking: multiplicities
    pub low_sig_bound_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
    /// Trace column from signature bound checking: multiplicities
    pub high_sig_bound_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
    /// Trace column from range checking: multiplicities
    pub range_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
    /// Trace columns from roots operations
    pub roots: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    pub inv_roots: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
}

impl AllTraces {
    /// Creates a new AllTraces instance with the provided traces.
    pub fn new(
        f_ntt_butterfly: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        f_ntt_merges: Vec<Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>>,
        g_ntt_butterfly: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        g_ntt_merges: Vec<Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>>,
        mul: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        intt_merges: Vec<Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>>,
        ibutterfly: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        sub: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        euclidean_norm: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        half_range_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
        low_sig_bound_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
        high_sig_bound_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
        range_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
        roots: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        inv_roots: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    ) -> Self {
        Self {
            f_ntt_butterfly,
            f_ntt_merges,
            g_ntt_butterfly,
            g_ntt_merges,
            mul,
            intt_merges,
            ibutterfly,
            sub,
            euclidean_norm,
            half_range_check,
            low_sig_bound_check,
            high_sig_bound_check,
            range_check,
            roots,
            inv_roots,
        }
    }
}

impl BigClaim {
    /// Creates a standard BigClaim with all the default component claims.
    ///
    /// This function centralizes the creation of the BigClaim structure to avoid
    /// duplication between debug and main modules.
    ///
    /// # Returns
    ///
    /// Returns a `BigClaim` with all the standard component claims configured.
    pub fn new_standard() -> Self {
        use crate::{HIGH_SIG_BOUND, LOW_SIG_BOUND, POLY_LOG_SIZE};
        use stwo::prover::backend::simd::m31::LOG_N_LANES;

        let range_check_log_size = crate::zq::Q.ilog2() + 1;

        let f_ntt_merges = (1..POLY_LOG_SIZE)
            .map(|_| ntt::Claim {
                log_size: POLY_LOG_SIZE - 1,
            })
            .collect_vec();
        let g_ntt_merges = (1..POLY_LOG_SIZE)
            .map(|_| ntt::Claim {
                log_size: POLY_LOG_SIZE - 1,
            })
            .collect_vec();
        let intt_merges = (1..POLY_LOG_SIZE)
            .map(|_| intt::Claim {
                log_size: POLY_LOG_SIZE - 1,
            })
            .collect_vec();
        // TODO: add the last roots when butterfly is using this preprocessed column as well
        let roots = (2..=POLY_LOG_SIZE)
            .map(|i| roots::preprocessed::Claim {
                log_size: std::cmp::max(LOG_N_LANES, i),
            })
            .collect_vec();
        let inv_roots = (2..=POLY_LOG_SIZE)
            .rev()
            .map(|i| roots::inv_preprocessed::Claim {
                log_size: std::cmp::max(LOG_N_LANES, i),
            })
            .collect_vec();
        Self {
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
            roots,
            inv_roots,
        }
    }

    /// Mixes all claim parameters into the Fiat-Shamir channel.
    ///
    /// This ensures that the proof is deterministic and all components
    /// contribute to the randomness.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.f_ntt_butterfly.mix_into(channel);
        self.f_ntt_merges.iter().for_each(|merge| {
            merge.mix_into(channel);
        });
        self.g_ntt_butterfly.mix_into(channel);
        self.g_ntt_merges.iter().for_each(|merge| {
            merge.mix_into(channel);
        });
        self.mul.mix_into(channel);
        self.intt_merges.iter().for_each(|merge| {
            merge.mix_into(channel);
        });
        self.ibutterfly.mix_into(channel);
        self.sub.mix_into(channel);
        self.euclidean_norm.mix_into(channel);
        self.half_range_check.mix_into(channel);
        self.low_sig_bound_check.mix_into(channel);
        self.high_sig_bound_check.mix_into(channel);
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
        s1: &[u32; POLY_SIZE],
        pk: &[u32; POLY_SIZE],
        msg_point: &[u32; POLY_SIZE],
    ) -> (
        Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        AllTraces,
    ) {
        let mut range_check_input = vec![];
        let (f_ntt_butterfly_trace, f_ntt_butterfly_remainders, f_ntt_butterfly_output) =
            self.f_ntt_butterfly.gen_trace(s1);
        range_check_input.extend(f_ntt_butterfly_remainders);

        let mut f_ntt_outputs = vec![f_ntt_butterfly_output];
        let mut f_ntt_traces = vec![];
        let mut f_ntt_js = vec![];
        for (i, merge) in self.f_ntt_merges.iter().enumerate() {
            let (f_ntt_trace, f_ntt_remainders, f_ntt_output, js) =
                merge.gen_trace(&f_ntt_outputs[i], i + 1);
            range_check_input.extend(f_ntt_remainders);
            f_ntt_outputs.push(f_ntt_output);
            f_ntt_traces.push(f_ntt_trace);
            f_ntt_js.push(js);
        }

        let (g_ntt_butterfly_trace, g_ntt_butterfly_remainders, g_ntt_butterfly_output) =
            self.g_ntt_butterfly.gen_trace(pk);
        range_check_input.extend(g_ntt_butterfly_remainders);

        let mut g_ntt_outputs = vec![g_ntt_butterfly_output];
        let mut g_ntt_traces = vec![];
        let mut g_ntt_js = vec![];
        for (i, merge) in self.g_ntt_merges.iter().enumerate() {
            let (g_ntt_trace, g_ntt_remainders, g_ntt_output, js) =
                merge.gen_trace(&g_ntt_outputs[i], i + 1);
            range_check_input.extend(g_ntt_remainders);
            g_ntt_outputs.push(g_ntt_output);
            g_ntt_traces.push(g_ntt_trace);
            g_ntt_js.push(js);
        }

        let (mul_trace, mul_remainders) = self.mul.gen_trace(
            &f_ntt_outputs.last().unwrap()[0],
            &g_ntt_outputs.last().unwrap()[0],
        );
        range_check_input.push(mul_remainders.clone());

        let mut intt_outputs = vec![vec![mul_remainders.into_iter().map(|r| r.0).collect_vec()]];
        let mut intt_traces = vec![];
        let mut intt_js = vec![];

        for (i, split) in self.intt_merges.iter().enumerate() {
            let (intt_trace, intt_remainders, intt_output, js) = split.gen_trace(&intt_outputs[i]);
            range_check_input.extend(intt_remainders);
            intt_outputs.push(intt_output);
            intt_traces.push(intt_trace);
            intt_js.push(js);
        }

        let ibutterfly_input = intt_outputs.last().unwrap().clone();

        let (ibutterfly_trace, ibutterfly_remainders, ibutterflied_poly) =
            self.ibutterfly.gen_trace(&ibutterfly_input);

        range_check_input.extend(ibutterfly_remainders);

        let (sub_trace, sub_remainders) = self.sub.gen_trace(msg_point, &ibutterflied_poly);
        range_check_input.push(sub_remainders.clone());

        let (
            euclidean_norm_trace,
            euclidean_norm_remainders,
            (euclidean_norm_output_low, euclidean_norm_output_high),
        ) = self.euclidean_norm.gen_trace(
            &sub_remainders
                .iter()
                .map(|r| r.0)
                .collect_vec()
                .try_into()
                .unwrap(),
            s1,
        );
        let half_range_check_trace = self
            .half_range_check
            .gen_trace(&chain!([euclidean_norm_remainders]).collect_vec());

        let low_sig_bound_check_trace = self
            .low_sig_bound_check
            .gen_trace(&[vec![M31(euclidean_norm_output_low)]]);
        let high_sig_bound_check_trace = self
            .high_sig_bound_check
            .gen_trace(&[vec![M31(euclidean_norm_output_high)]]);
        let range_check_trace = self.range_check.gen_trace(&range_check_input);

        let mut roots = vec![];

        for ((roots_claim, f_ntt_js), g_ntt_js) in
            self.roots.iter().zip_eq(f_ntt_js).zip_eq(g_ntt_js)
        {
            let roots_trace = roots_claim.gen_trace(
                &f_ntt_js
                    .into_iter()
                    .chain(g_ntt_js.into_iter())
                    .collect_vec(),
            );
            roots.push(roots_trace);
        }
        let mut inv_roots = vec![];

        for (inv_roots_claim, intt_js) in self.inv_roots.iter().zip_eq(intt_js) {
            let roots_trace = inv_roots_claim.gen_trace(&intt_js);
            inv_roots.push(roots_trace);
        }

        (
            chain!(
                f_ntt_butterfly_trace.clone(),
                f_ntt_traces.iter().flatten().cloned().collect_vec(),
                g_ntt_butterfly_trace.clone(),
                g_ntt_traces.iter().flatten().cloned().collect_vec(),
                mul_trace.clone(),
                intt_traces.iter().flatten().cloned().collect_vec(),
                ibutterfly_trace.clone(),
                sub_trace.clone(),
                euclidean_norm_trace.clone(),
                [half_range_check_trace.clone()],
                [low_sig_bound_check_trace.clone()],
                [high_sig_bound_check_trace.clone()],
                [range_check_trace.clone()],
                roots.clone(),
                inv_roots.clone(),
            )
            .collect_vec(),
            AllTraces::new(
                f_ntt_butterfly_trace,
                f_ntt_traces,
                g_ntt_butterfly_trace,
                g_ntt_traces,
                mul_trace,
                intt_traces,
                ibutterfly_trace,
                sub_trace,
                euclidean_norm_trace,
                half_range_check_trace,
                low_sig_bound_check_trace,
                high_sig_bound_check_trace,
                range_check_trace,
                roots,
                inv_roots,
            ),
        )
    }

    /// Creates the standard preprocessed columns for range checking.
    ///
    /// This function creates and returns the standard preprocessed columns used
    /// for range checking across the Big AIR system.
    ///
    /// # Returns
    ///
    /// Returns a tuple containing all the preprocessed range check columns.
    pub fn create_preprocessed_columns() -> (
        Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Vec<PreProcessedColumnId>,
    ) {
        let mut columns = vec![];
        let mut ids = vec![];

        let range_check_preprocessed = range_check::RangeCheck::<Q>::gen_column_simd();
        columns.push(range_check_preprocessed);
        ids.push(range_check::RangeCheck::<Q>::id());

        let half_range_check_preprocessed = range_check::RangeCheck::<{ Q / 2 }>::gen_column_simd();
        columns.push(half_range_check_preprocessed);
        ids.push(range_check::RangeCheck::<{ Q / 2 }>::id());

        let low_sig_bound_check_preprocessed =
            range_check::RangeCheck::<LOW_SIG_BOUND>::gen_column_simd();
        columns.push(low_sig_bound_check_preprocessed);
        ids.push(range_check::RangeCheck::<LOW_SIG_BOUND>::id());

        let high_sig_bound_check_preprocessed =
            range_check::RangeCheck::<HIGH_SIG_BOUND>::gen_column_simd();
        columns.push(high_sig_bound_check_preprocessed);
        ids.push(range_check::RangeCheck::<HIGH_SIG_BOUND>::id());

        // TODO; add the last roots when butterfly is using this preprocessed column as well
        for i in 2..=POLY_LOG_SIZE {
            let roots_preprocessed = roots::preprocessed::Roots::new(i as usize).gen_column_simd();
            columns.extend(roots_preprocessed);
            ids.push(roots::preprocessed::Roots::new(i as usize).id());
            let mut root_id = roots::preprocessed::Roots::new(i as usize).id();
            root_id.id.push_str("_root");
            ids.push(root_id);
        }
        for i in (2..=POLY_LOG_SIZE).rev() {
            let inv_roots_preprocessed =
                roots::inv_preprocessed::InvRoots::new(i as usize).gen_column_simd();
            columns.extend(inv_roots_preprocessed);
            ids.push(roots::inv_preprocessed::InvRoots::new(i as usize).id());
            let mut inv_root_id = roots::inv_preprocessed::InvRoots::new(i as usize).id();
            inv_root_id.id.push_str("_inv_root");
            ids.push(inv_root_id);
        }
        (columns, ids)
    }

    /// Creates all NTT components (butterfly and merge components for both f and g).
    ///
    /// # Arguments
    ///
    /// * `claim` - The BigClaim containing all component claims
    /// * `lookup_elements` - The lookup elements for all operations
    /// * `interaction_claim` - The interaction claim containing claimed sums
    /// * `tree_span_provider` - The trace location allocator
    ///
    /// # Returns
    ///
    /// Returns tuples containing the butterfly and merge components for both f and g NTTs.
    pub fn create_ntt_components(
        claim: &BigClaim,
        lookup_elements: &crate::big_air::relation::LookupElements,
        interaction_claim: &crate::big_air::interaction_claim::BigInteractionClaim,
        tree_span_provider: &mut stwo_constraint_framework::TraceLocationAllocator,
    ) -> (
        ntt::butterfly::Component,
        Vec<ntt::Component>,
        ntt::butterfly::Component,
        Vec<ntt::Component>,
    ) {
        let f_ntt_butterfly_component = ntt::butterfly::Component::new(
            tree_span_provider,
            ntt::butterfly::Eval {
                claim: claim.f_ntt_butterfly.clone(),
                rc_lookup_elements: lookup_elements.rc.clone(),
                butterfly_output_lookup_elements: lookup_elements.f_ntt_butterfly.clone(),
            },
            interaction_claim.f_ntt_butterfly.claimed_sum,
        );

        let f_ntt_merges_components = claim
            .f_ntt_merges
            .iter()
            .zip_eq(interaction_claim.f_ntt_merges.iter())
            .enumerate()
            .map(|(i, (merge, interaction_claim))| {
                ntt::Component::new(
                    tree_span_provider,
                    ntt::Eval {
                        claim: merge.clone(),
                        rc_lookup_elements: lookup_elements.rc.clone(),
                        ntt_lookup_elements: lookup_elements.f_ntt.clone(),
                        input_lookup_elements: if i == 0 {
                            InputLookupElements::Butterfly(lookup_elements.f_ntt_butterfly.clone())
                        } else {
                            InputLookupElements::NTT(lookup_elements.f_ntt.clone())
                        },
                        poly_size: 1 << (i + 1),
                        roots_lookup_elements: lookup_elements.roots.clone(),
                    },
                    interaction_claim.claimed_sum,
                )
            })
            .collect_vec();

        let g_ntt_butterfly_component = ntt::butterfly::Component::new(
            tree_span_provider,
            ntt::butterfly::Eval {
                claim: claim.g_ntt_butterfly.clone(),
                rc_lookup_elements: lookup_elements.rc.clone(),
                butterfly_output_lookup_elements: lookup_elements.g_ntt_butterfly.clone(),
            },
            interaction_claim.g_ntt_butterfly.claimed_sum,
        );

        let g_ntt_merges_components = claim
            .g_ntt_merges
            .iter()
            .zip_eq(interaction_claim.g_ntt_merges.iter())
            .enumerate()
            .map(|(i, (merge, interaction_claim))| {
                ntt::Component::new(
                    tree_span_provider,
                    ntt::Eval {
                        claim: merge.clone(),
                        rc_lookup_elements: lookup_elements.rc.clone(),
                        ntt_lookup_elements: lookup_elements.g_ntt.clone(),
                        input_lookup_elements: if i == 0 {
                            InputLookupElements::Butterfly(lookup_elements.g_ntt_butterfly.clone())
                        } else {
                            InputLookupElements::NTT(lookup_elements.g_ntt.clone())
                        },
                        poly_size: 1 << (i + 1),
                        roots_lookup_elements: lookup_elements.roots.clone(),
                    },
                    interaction_claim.claimed_sum,
                )
            })
            .collect_vec();

        (
            f_ntt_butterfly_component,
            f_ntt_merges_components,
            g_ntt_butterfly_component,
            g_ntt_merges_components,
        )
    }

    /// Creates all the remaining components (mul, intt, ibutterfly, sub, euclidean_norm, range_checks).
    ///
    /// # Arguments
    ///
    /// * `claim` - The BigClaim containing all component claims
    /// * `lookup_elements` - The lookup elements for all operations
    /// * `interaction_claim` - The interaction claim containing claimed sums
    /// * `tree_span_provider` - The trace location allocator
    ///
    /// # Returns
    ///
    /// Returns all the remaining components as individual variables.
    pub fn create_remaining_components(
        claim: &BigClaim,
        lookup_elements: &crate::big_air::relation::LookupElements,
        interaction_claim: &crate::big_air::interaction_claim::BigInteractionClaim,
        tree_span_provider: &mut stwo_constraint_framework::TraceLocationAllocator,
    ) -> (
        mul::Component,
        Vec<intt::Component>,
        intt::ibutterfly::Component,
        sub::Component,
        euclidean_norm::Component,
        range_check::Component<{ Q / 2 }>,
        range_check::Component<LOW_SIG_BOUND>,
        range_check::Component<HIGH_SIG_BOUND>,
        range_check::Component<Q>,
        Vec<roots::preprocessed::Component>,
        Vec<roots::inv_preprocessed::Component>,
    ) {
        let mul_component = mul::Component::new(
            tree_span_provider,
            mul::Eval {
                claim: claim.mul.clone(),
                rc_lookup_elements: lookup_elements.rc.clone(),
                f_ntt_lookup_elements: lookup_elements.f_ntt.clone(),
                g_ntt_lookup_elements: lookup_elements.g_ntt.clone(),
                mul_lookup_elements: lookup_elements.mul.clone(),
            },
            interaction_claim.mul.claimed_sum,
        );

        let intt_merges_components = claim
            .intt_merges
            .iter()
            .zip_eq(interaction_claim.intt_merges.iter())
            .enumerate()
            .map(|(i, (merge, interaction_claim))| {
                intt::Component::new(
                    tree_span_provider,
                    intt::Eval {
                        claim: merge.clone(),
                        rc_lookup_elements: lookup_elements.rc.clone(),
                        input_lookup_elements: if i == 0 {
                            crate::big_air::relation::INTTInputLookupElements::Mul(
                                lookup_elements.mul.clone(),
                            )
                        } else {
                            crate::big_air::relation::INTTInputLookupElements::INTTOutput(
                                lookup_elements.intt.clone(),
                            )
                        },
                        intt_lookup_elements: lookup_elements.intt.clone(),
                        poly_size: 1 << (crate::POLY_LOG_SIZE as usize - i),
                        inv_roots_lookup_elements: lookup_elements.inv_roots.clone(),
                    },
                    interaction_claim.claimed_sum,
                )
            })
            .collect_vec();

        let ibutterfly_component = intt::ibutterfly::Component::new(
            tree_span_provider,
            intt::ibutterfly::Eval {
                claim: claim.ibutterfly.clone(),
                rc_lookup_elements: lookup_elements.rc.clone(),
                intt_output_lookup_elements: lookup_elements.intt.clone(),
                ibutterfly_output_lookup_elements: lookup_elements.ibutterfly.clone(),
            },
            interaction_claim.ibutterfly.claimed_sum,
        );

        let sub_component = sub::Component::new(
            tree_span_provider,
            sub::Eval {
                claim: claim.sub.clone(),
                rc_lookup_elements: lookup_elements.rc.clone(),
                ibutterfly_lookup_elements: lookup_elements.ibutterfly.clone(),
                sub_lookup_elements: lookup_elements.sub.clone(),
            },
            interaction_claim.sub.claimed_sum,
        );

        let euclidean_norm_component = euclidean_norm::Component::new(
            tree_span_provider,
            euclidean_norm::Eval {
                claim: claim.euclidean_norm.clone(),
                half_rc_lookup_elements: lookup_elements.half_range_check.clone(),
                s0_lookup_elements: lookup_elements.sub.clone(),
                low_sig_bound_check_lookup_elements: lookup_elements.low_sig_bound_check.clone(),
                high_sig_bound_check_lookup_elements: lookup_elements.high_sig_bound_check.clone(),
            },
            interaction_claim.euclidean_norm.claimed_sum,
        );

        let half_range_check_component = range_check::Component::new(
            tree_span_provider,
            range_check::Eval::<{ Q / 2 }> {
                claim: claim.half_range_check.clone(),
                lookup_elements: lookup_elements.half_range_check.clone(),
            },
            interaction_claim.half_range_check.claimed_sum,
        );

        let low_sig_bound_check_component = range_check::Component::new(
            tree_span_provider,
            range_check::Eval::<LOW_SIG_BOUND> {
                claim: claim.low_sig_bound_check.clone(),
                lookup_elements: lookup_elements.low_sig_bound_check.clone(),
            },
            interaction_claim.low_sig_bound_check.claimed_sum,
        );

        let high_sig_bound_check_component = range_check::Component::new(
            tree_span_provider,
            range_check::Eval::<HIGH_SIG_BOUND> {
                claim: claim.high_sig_bound_check.clone(),
                lookup_elements: lookup_elements.high_sig_bound_check.clone(),
            },
            interaction_claim.high_sig_bound_check.claimed_sum,
        );

        let range_check_component = range_check::Component::new(
            tree_span_provider,
            range_check::Eval::<Q> {
                claim: claim.range_check.clone(),
                lookup_elements: lookup_elements.rc.clone(),
            },
            interaction_claim.range_check.claimed_sum,
        );
        let roots_components = claim
            .roots
            .iter()
            .zip_eq(interaction_claim.roots.iter())
            .enumerate()
            .map(|(i, (roots_claim, interaction_claim))| {
                roots::preprocessed::Component::new(
                    tree_span_provider,
                    roots::preprocessed::Eval {
                        claim: roots_claim.clone(),
                        lookup_elements: lookup_elements.roots.clone(),
                        poly_log_size: i + 2,
                    },
                    interaction_claim.claimed_sum,
                )
            })
            .collect_vec();
        let inv_roots_components = claim
            .inv_roots
            .iter()
            .zip_eq(interaction_claim.inv_roots.iter())
            .enumerate()
            .map(|(i, (inv_roots_claim, interaction_claim))| {
                roots::inv_preprocessed::Component::new(
                    tree_span_provider,
                    roots::inv_preprocessed::Eval {
                        claim: inv_roots_claim.clone(),
                        lookup_elements: lookup_elements.inv_roots.clone(),
                        poly_log_size: POLY_LOG_SIZE as usize - i,
                    },
                    interaction_claim.claimed_sum,
                )
            })
            .collect_vec();

        (
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
        )
    }
}
