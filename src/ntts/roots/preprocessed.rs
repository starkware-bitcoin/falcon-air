//! # Range Check Component
//!
//! This module implements STARK proof components for range checking operations.
//!
//! The range check ensures that values are within the valid range [0, q) where q = 12289.
//! This is implemented using a lookup table approach where:
//! - A preprocessed column contains all values in [0, q)
//! - The trace column contains the multiplicities of each value
//! - The lookup protocol ensures the sum of multiplicities equals zero
//!
//! This component is used by all arithmetic operations to ensure their results
//! remain within the valid field range.

use itertools::Itertools;
use num_traits::{One, Zero};
use stwo::{
    core::{
        ColumnVec,
        channel::Channel,
        fields::{
            m31::{BaseField, M31},
            qm31::QM31,
        },
        poly::circle::CanonicCoset,
    },
    prover::{
        backend::simd::{SimdBackend, column::BaseColumn, m31::LOG_N_LANES, qm31::PackedQM31},
        poly::{BitReversedOrder, circle::CircleEvaluation},
    },
};
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    preprocessed_columns::PreProcessedColumnId,
};

use crate::{big_air::relation::RootsLookupElements, ntts::ROOTS};

#[derive(Debug, Clone)]
pub struct Roots {
    pub poly_log_size: usize,
}

impl Roots {
    pub fn new(poly_log_size: usize) -> Self {
        Self { poly_log_size }
    }

    /// Returns the log size needed for the range check column.
    ///
    /// The size is log₂(Q) + 1 to accommodate all values in [0, Q).
    pub fn log_size(&self) -> u32 {
        self.poly_log_size as u32
    }

    /// Generates the preprocessed column for range checking.
    ///
    /// The column contains all values from 0 to Q-1, followed by zeros
    /// to fill the remaining space up to the next power of 2.
    pub fn gen_column_simd(
        &self,
    ) -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
        let mut js = (0..(1 << self.poly_log_size)).collect_vec();
        let mut roots = ROOTS[self.poly_log_size - 1].to_vec();
        if self.poly_log_size < LOG_N_LANES as usize {
            js.resize(1 << (LOG_N_LANES as usize), 0);
            roots.resize(1 << (LOG_N_LANES as usize), 0);
        }
        [js, roots]
            .iter()
            .map(|col| {
                CircleEvaluation::new(
                    CanonicCoset::new(std::cmp::max(self.log_size(), LOG_N_LANES)).circle_domain(),
                    BaseColumn::from_iter(col.iter().map(|x| M31(*x))),
                )
            })
            .collect_vec()
    }

    /// Returns the unique identifier for this preprocessed column.
    pub fn id(&self) -> PreProcessedColumnId {
        PreProcessedColumnId {
            id: format!("roots_of_unity_{}", self.poly_log_size),
        }
    }
}

// This is a helper function for the prover to generate the trace for the range_check component
#[derive(Debug, Clone)]
pub struct Claim {
    /// The log base 2 of the trace size
    pub log_size: u32,
}

impl Claim {
    /// Mixes the claim parameters into the Fiat-Shamir channel.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    /// Generates the trace for the range_check component
    /// The trace contains the multiplicities of each value
    pub fn gen_trace(&self, js: &[u32]) -> CircleEvaluation<SimdBackend, M31, BitReversedOrder> {
        let mut trace = vec![M31::zero(); 1 << self.log_size as usize];
        for j in js {
            trace[*j as usize] += M31::one();
        }
        CircleEvaluation::new(
            CanonicCoset::new(self.log_size).circle_domain(),
            BaseColumn::from_iter(trace),
        )
    }
}

// Actual component that is used in the framework
#[derive(Debug, Clone)]
pub struct Eval {
    /// The claim parameters
    pub claim: Claim,
    /// Lookup elements for range checking
    pub lookup_elements: RootsLookupElements,
    pub poly_log_size: usize,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.claim.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let multiplicity = eval.next_trace_mask();
        let j = eval.get_preprocessed_column(Roots::new(self.poly_log_size).id());
        let mut root_id = Roots::new(self.poly_log_size).id();
        root_id.id.push_str("_root");
        let root = eval.get_preprocessed_column(root_id);

        // Add the trace column to the lookup relation with coefficient -1
        // This ensures that the sum of all lookups equals zero
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            -E::EF::from(multiplicity),
            &[j, root],
        ));

        eval.finalize_logup();

        eval
    }
}

#[derive(Debug, Clone)]
pub struct InteractionClaim {
    /// The claimed sum for the interaction
    pub claimed_sum: QM31,
}

impl InteractionClaim {
    /// Mixes the interaction claim into the Fiat-Shamir channel.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }

    /// Generates the interaction trace for range checking.
    ///
    /// This method creates the interaction trace that connects the range check component
    /// with the arithmetic components through the lookup protocol.
    ///
    /// # Parameters
    ///
    /// - `trace`: The trace column from the range check component
    /// - `lookup_elements`: The lookup elements for range checking
    ///
    /// # Returns
    ///
    /// Returns the interaction trace and the interaction claim.
    pub fn gen_interaction_trace(
        trace: &CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
        lookup_elements: &RootsLookupElements,
        poly_log_size: usize,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Self,
    ) {
        let log_size = trace.domain.log_size();
        println!("log_size = {:?}", log_size);
        let mut logup_gen = LogupTraceGenerator::new(log_size);
        let mut col_gen = logup_gen.new_col();
        let js_and_roots = Roots::new(poly_log_size).gen_column_simd();
        let js = js_and_roots[0].clone();
        let roots = js_and_roots[1].clone();

        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            // Get the multiplicity value from the trace
            let multiplicity = trace.data[vec_row];

            let denom: PackedQM31 =
                lookup_elements.combine(&[js.data[vec_row], roots.data[vec_row]]);

            // The numerator is 1 (we want to check that result is in the range)
            let numerator = -PackedQM31::from(multiplicity);

            col_gen.write_frac(vec_row, numerator, denom);
        }
        col_gen.finalize_col();

        let (interaction_trace, claimed_sum) = logup_gen.finalize_last();
        (interaction_trace, Self { claimed_sum })
    }
}

/// Type alias for the range check component.
pub type Component = FrameworkComponent<Eval>;
