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

use crate::big_air::relation::RCLookupElements;

#[derive(Debug, Clone)]
pub struct RangeCheck<const Q: u32>;

impl<const Q: u32> RangeCheck<Q> {
    /// Returns the log size needed for the range check column.
    ///
    /// The size is log₂(Q) + 1 to accommodate all values in [0, Q).
    pub fn log_size() -> u32 {
        Q.next_power_of_two().ilog2()
    }

    /// Generates the preprocessed column for range checking.
    ///
    /// The column contains all values from 0 to Q-1, followed by zeros
    /// to fill the remaining space up to the next power of 2.
    pub fn gen_column_simd() -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
        CircleEvaluation::new(
            CanonicCoset::new(Self::log_size()).circle_domain(),
            BaseColumn::from_iter(
                (0..Q)
                    .map(M31)
                    .chain((Q..Q.next_power_of_two()).map(|_| M31::zero())),
            ),
        )
    }

    /// Returns the unique identifier for this preprocessed column.
    pub fn id() -> PreProcessedColumnId {
        PreProcessedColumnId {
            id: format!("range_check_{}", Q),
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
    pub fn gen_trace(
        &self,
        remainders: &[Vec<M31>],
    ) -> CircleEvaluation<SimdBackend, M31, BitReversedOrder> {
        let mut trace = vec![M31::zero(); 1 << self.log_size as usize];
        for col in remainders {
            for remainder in col.iter() {
                trace[remainder.0 as usize] += M31::one();
            }
        }
        CircleEvaluation::new(
            CanonicCoset::new(self.log_size).circle_domain(),
            BaseColumn::from_iter(trace),
        )
    }
}

// Actual component that is used in the framework
#[derive(Debug, Clone)]
pub struct Eval<const Q: u32> {
    /// The claim parameters
    pub claim: Claim,
    /// Lookup elements for range checking
    pub lookup_elements: RCLookupElements,
}

impl<const Q: u32> FrameworkEval for Eval<Q> {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.claim.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let lookup_col_1 = eval.next_trace_mask();
        let range_check_col = eval.get_preprocessed_column(RangeCheck::<Q>::id());

        // Add the trace column to the lookup relation with coefficient -1
        // This ensures that the sum of all lookups equals zero
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            -E::EF::from(lookup_col_1),
            &[range_check_col],
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
    pub fn gen_interaction_trace<const Q: u32>(
        trace: &CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
        lookup_elements: &RCLookupElements,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Self,
    ) {
        let log_size = trace.domain.log_size();
        let mut logup_gen = LogupTraceGenerator::new(log_size);
        let mut col_gen = logup_gen.new_col();
        let range_check_col = RangeCheck::<Q>::gen_column_simd();

        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            // Get the multiplicity value from the trace
            let multiplicity = trace.data[vec_row];

            let denom: PackedQM31 = lookup_elements.combine(&[range_check_col.data[vec_row]]);

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
pub type Component<const Q: u32> = FrameworkComponent<Eval<Q>>;
