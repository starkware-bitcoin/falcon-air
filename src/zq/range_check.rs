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
//! The range check ensures that values are within the valid range [0, q) by using
//! a lookup table approach based on the lookup protocol. This provides efficient
//! verification that all arithmetic operation results remain within field bounds.
//!
//! # Lookup Protocol Implementation
//!
//! The range checking is implemented using a lookup table approach where:
//! - **Preprocessed Column**: Contains all values in [0, q) followed by zeros
//! - **Trace Column**: Contains the multiplicities of each value appearing in the trace
//! - **Lookup Protocol**: Ensures the sum of all lookup relations equals zero
//!
//! # Trace Structure
//!
//! The component generates execution traces containing:
//! - Multiplicities of each value in [0, q) that appears in arithmetic operations
//! - Connection to preprocessed range check table through lookup relations
//! - Validation that all values remain within the valid field range
//!
//! # Constraints
//!
//! The component enforces:
//! 1. **Range Validation**: All values must be in [0, q) through lookup protocol
//! 2. **Multiplicity Tracking**: Accurate counting of value occurrences
//! 3. **Lookup Balance**: Sum of all lookup relations must equal zero
//!
//! # Usage
//!
//! This component is used by all arithmetic operations (addition, multiplication,
//! subtraction) to ensure their results remain within the valid field range.
//! It's integrated into the larger Big AIR proof system for comprehensive validation.

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

/// Range check component for values in the field Z_q.
///
/// This struct provides utility functions for range checking operations
/// in the field Z_q where Q is the field size. It handles preprocessed
/// column generation and sizing for efficient range validation.
///
/// # Type Parameters
///
/// - `Q`: The field size (e.g., 12289 for the main field)
///
/// # Mathematical Properties
///
/// - Ensures all values are in the range [0, Q)
/// - Uses lookup tables for efficient verification
/// - Supports arbitrary field sizes through const generics
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

/// Claim structure for range check component trace generation.
///
/// This struct contains the parameters needed to generate execution traces
/// for the range check component. It's used by the prover to create
/// the necessary trace data for STARK proof generation.
///
/// # Fields
///
/// - `log_size`: The log base 2 of the trace size, determining the number
///   of rows in the execution trace (2^log_size rows)
#[derive(Debug, Clone)]
pub struct Claim {
    /// The log base 2 of the trace size
    pub log_size: u32,
}

impl Claim {
    /// Mixes the claim parameters into the Fiat-Shamir channel.
    ///
    /// This function contributes the claim parameters to the Fiat-Shamir
    /// transformation, ensuring that the proof is bound to these specific
    /// parameters and cannot be reused for different trace sizes.
    ///
    /// # Parameters
    ///
    /// - `channel`: The Fiat-Shamir channel for mixing claim parameters
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    /// Generates the trace for the range_check component.
    ///
    /// The trace contains the multiplicities of each value that appears
    /// in the arithmetic operations. Each position in the trace corresponds
    /// to a field value, and the value at that position indicates how many
    /// times that field value appears in the computation.
    ///
    /// # Parameters
    ///
    /// - `remainders`: Array of remainder vectors from arithmetic operations
    ///   Each vector contains the remainders from one arithmetic component
    ///
    /// # Returns
    ///
    /// Returns a circle evaluation containing the multiplicity trace for
    /// range checking validation.
    ///
    /// # Trace Generation Algorithm
    ///
    /// 1. Initialize trace with zeros for all possible field values
    /// 2. For each remainder in each arithmetic operation:
    ///    - Increment the multiplicity at the remainder's position
    /// 3. Return the final multiplicity trace
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

/// Evaluation component for range checking operations.
///
/// This struct represents the actual range check component used in the
/// STARK proof framework. It combines the claim parameters with lookup
/// elements to provide comprehensive range checking functionality.
///
/// # Type Parameters
///
/// - `Q`: The field size for range checking (e.g., 12289)
///
/// # Fields
///
/// - `claim`: The claim parameters defining the trace size and properties
/// - `lookup_elements`: The lookup elements for establishing range check relations
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
        let multiplicity = eval.next_trace_mask();
        let range_check_col = eval.get_preprocessed_column(RangeCheck::<Q>::id());

        // Add the trace column to the lookup relation with coefficient -1
        // This ensures that the sum of all lookups equals zero
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            -E::EF::from(multiplicity),
            &[range_check_col],
        ));

        eval.finalize_logup();

        eval
    }
}

/// Interaction claim for range checking lookup relations.
///
/// This struct represents the claim about the sum of lookup relations
/// in the range checking component. It's used to establish the connection
/// between arithmetic operations and range checking through the lookup protocol.
///
/// # Fields
///
/// - `claimed_sum`: The claimed sum of all lookup relations, which should
///   equal zero for a valid range checking proof
#[derive(Debug, Clone)]
pub struct InteractionClaim {
    /// The claimed sum for the interaction
    pub claimed_sum: QM31,
}

impl InteractionClaim {
    /// Mixes the interaction claim into the Fiat-Shamir channel.
    ///
    /// This function contributes the interaction claim to the Fiat-Shamir
    /// transformation, ensuring that the proof is bound to the specific
    /// lookup relation sums and cannot be reused for different claims.
    ///
    /// # Parameters
    ///
    /// - `channel`: The Fiat-Shamir channel for mixing interaction claims
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }

    /// Generates the interaction trace for range checking.
    ///
    /// This method creates the interaction trace that connects the range check component
    /// with the arithmetic components through the lookup protocol. It establishes
    /// the lookup relations that validate that all values remain within the field bounds.
    ///
    /// # Parameters
    ///
    /// - `trace`: The trace column from the range check component containing multiplicities
    /// - `lookup_elements`: The lookup elements for establishing range check relations
    pub fn gen_interaction_trace<const Q: u32>(
        trace: &CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
        lookup_elements: &RCLookupElements,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Self,
    ) {
        // Get the log size from the trace domain for trace generation
        let log_size = trace.domain.log_size();

        // Initialize the lookup trace generator for the specified log size
        let mut logup_gen = LogupTraceGenerator::new(log_size);
        let mut col_gen = logup_gen.new_col();

        // Generate the preprocessed range check column for lookup validation
        let range_check_col = RangeCheck::<Q>::gen_column_simd();

        // Process each row in the trace to establish lookup relations
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            // Extract the multiplicity value from the range check trace
            // This indicates how many times the corresponding field value appears
            let multiplicity = trace.data[vec_row];

            // Combine the range check column value with lookup elements
            // This creates the denominator for the lookup relation
            let denom: PackedQM31 = lookup_elements.combine(&[range_check_col.data[vec_row]]);

            // Create the numerator for the lookup relation
            // The negative multiplicity ensures the lookup sum equals zero
            let numerator = -PackedQM31::from(multiplicity);

            // Write the fraction (numerator/denominator) to the interaction trace
            col_gen.write_frac(vec_row, numerator, denom);
        }
        // Finalize the column generation process
        col_gen.finalize_col();

        // Extract the final interaction trace and claimed sum from the generator
        // The claimed sum should equal zero for a valid range checking proof
        let (interaction_trace, claimed_sum) = logup_gen.finalize_last();

        // Return the interaction trace and claim for validation
        (interaction_trace, Self { claimed_sum })
    }
}

/// Type alias for the range check component.
///
/// This provides a convenient way to reference the range check component
/// in the STARK proof framework. It combines the evaluation logic with
/// the framework's component system for integration into larger proofs.
///
/// # Type Parameters
///
/// - `Q`: The field size for range checking (e.g., 12289)
pub type Component<const Q: u32> = FrameworkComponent<Eval<Q>>;
