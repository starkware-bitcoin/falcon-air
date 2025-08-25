//! # Euclidean Norm Component
//!
//! This module implements STARK proof components for Euclidean norm computation
//! for polynomial coefficients. The Euclidean norm is used for signature verification
//! in the Falcon signature scheme.
//!
//! # Mathematical Foundation
//!
//! The Euclidean norm computes ||s||² = Σᵢ(sᵢ²) for a polynomial s with coefficients
//! in the range [-q/2, q/2]. This is a regular Euclidean norm computation (not modular)
//! that produces a real number result.
//!
//! # Algorithm Details
//!
//! The Euclidean norm computation involves several steps:
//!
//! 1. **Coefficient Normalization**: Convert coefficients from [0, q) to [-q/2, q/2]
//!    - If sᵢ > q/2: borrow = 1, remainder = q - sᵢ
//!    - If sᵢ ≤ q/2: borrow = 0, remainder = sᵢ
//!
//! 2. **Squared Sum Computation**: Compute Σᵢ(remainderᵢ²) for both polynomials
//!    - Accumulate squared remainders in a cumulative sum
//!    - The result is a regular integer sum (not modular)
//!
//! 3. **Range Checking**: Verify that the final Euclidean norm is within predefined bounds
//!    - Check that the norm is below the signature bound threshold
//!    - Ensure the signature meets the security requirements
//!
//! # Trace Structure
//!
//! The component generates traces with the following columns:
//! - Borrow indicators for coefficient normalization
//! - Normalized remainders for both polynomials
//! - Cumulative sums of squared remainders
//! - Final Euclidean norm values
//!
//! # Usage
//!
//! This component is used in the Falcon signature scheme for signature verification.
//! The Euclidean norm of the signature polynomial must be below a predefined threshold
//! for the signature to be considered valid. This threshold is determined by the
//! security parameters of the signature scheme.

use itertools::chain;
use num_traits::One;
use stwo::{
    core::{
        ColumnVec,
        channel::Channel,
        fields::{m31::M31, qm31::SecureField},
        pcs::TreeVec,
        poly::circle::CanonicCoset,
        utils::bit_reverse_coset_to_circle_domain_order,
    },
    prover::{
        backend::simd::{SimdBackend, column::BaseColumn, m31::LOG_N_LANES, qm31::PackedQM31},
        poly::{BitReversedOrder, circle::CircleEvaluation},
    },
};
use stwo_constraint_framework::{
    FrameworkComponent, FrameworkEval, LogupTraceGenerator, ORIGINAL_TRACE_IDX, Relation,
    RelationEntry,
};

use crate::{
    POLY_SIZE,
    big_air::relation::{RCLookupElements, SubLookupElements},
    zq::Q,
};

/// Claim parameters for the Euclidean norm circuit.
///
/// This struct defines the parameters needed to generate and verify Euclidean norm proofs.
/// The claim contains the logarithmic size of the trace, which determines the number of
/// polynomial coefficients that can be processed.
///
/// # Parameters
///
/// - `log_size`: The log base 2 of the trace size (e.g., 10 for 1024 coefficients)
///   This determines the number of polynomial coefficients and the size of the computation trace.
///
/// # Example
///
/// For a polynomial with 1024 coefficients:
/// ```rust
/// let claim = Claim { log_size: 10 };
/// ```
#[derive(Debug, Clone)]
pub struct Claim {
    /// The log base 2 of the trace size
    pub log_size: u32,
}

impl Claim {
    /// Returns the log sizes for the traces.
    ///
    /// [preprocessed_trace, trace, interaction_trace]
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let trace_log_sizes = vec![self.log_size];
        TreeVec::new(vec![vec![], trace_log_sizes, vec![]])
    }

    /// Mixes the claim parameters into the Fiat-Shamir channel.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    /// Generates the trace for the Euclidean norm component.
    ///
    /// This function creates a trace that represents Euclidean norm computation
    /// for two polynomial signatures. The computation involves coefficient normalization,
    /// squared sum accumulation, and range checking against predefined bounds.
    ///
    /// # Algorithm Details
    ///
    /// For each polynomial signature (s0, s1), the function:
    /// 1. Normalizes coefficients from [0, q) to [-q/2, q/2]
    /// 2. Computes squared remainders for both polynomials
    /// 3. Accumulates the squared sums
    /// 4. Checks that the final norm is within predefined bounds
    ///
    /// # Parameters
    ///
    /// - `s0`: First polynomial signature with coefficients in [0, q)
    /// - `s1`: Second polynomial signature with coefficients in [0, q)
    ///
    /// # Returns
    ///
    /// Returns a tuple containing:
    /// - `ColumnVec<CircleEvaluation<...>>`: The computation trace columns
    /// - `Vec<M31>`: Remainder values for range checking
    /// - `(u32, u32)`: Final Euclidean norm values for both polynomials
    pub fn gen_trace(
        &self,
        s0: &[u32; POLY_SIZE],
        s1: &[u32; POLY_SIZE],
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Vec<M31>,
        (u32, u32),
    ) {
        let mut borrows_s0 = s0
            .iter()
            .map(|a| M31((*a > Q / 2) as u32))
            .collect::<Vec<_>>();
        let mut borrows_s1 = s1
            .iter()
            .map(|a| M31((*a > Q / 2) as u32))
            .collect::<Vec<_>>();
        let remainders_s0 = s0
            .iter()
            .map(|a| if *a > Q / 2 { Q - *a } else { *a })
            .collect::<Vec<_>>();
        let remainders_s1 = s1
            .iter()
            .map(|a| if *a > Q / 2 { Q - *a } else { *a })
            .collect::<Vec<_>>();
        let mut cum_sum = Vec::with_capacity(POLY_SIZE);
        remainders_s0
            .iter()
            .zip(remainders_s1.iter())
            .fold(0, |acc, (x, y)| {
                cum_sum.push(acc + x * x + y * y);
                assert!(acc + x * x + y * y < (1 << 31) - 1);
                acc + x * x + y * y
            });
        let remainders = chain!(remainders_s0.clone(), remainders_s1.clone())
            .map(M31)
            .collect::<Vec<_>>();
        let mut is_not_first = vec![M31(1); POLY_SIZE];
        is_not_first[0] = M31(0);
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        let mut is_last = vec![M31(0); POLY_SIZE];
        is_last[POLY_SIZE - 1] = M31(1);
        let mut s0 = s0
            .iter()
            .map(|a| M31::from_u32_unchecked(*a))
            .collect::<Vec<_>>();
        let mut s1 = s1
            .iter()
            .map(|a| M31::from_u32_unchecked(*a))
            .collect::<Vec<_>>();
        bit_reverse_coset_to_circle_domain_order(&mut s0);
        bit_reverse_coset_to_circle_domain_order(&mut s1);
        bit_reverse_coset_to_circle_domain_order(&mut borrows_s0);
        bit_reverse_coset_to_circle_domain_order(&mut borrows_s1);

        let mut bitrev_remainders_s0 = remainders_s0
            .iter()
            .map(|a| M31::from_u32_unchecked(*a))
            .collect::<Vec<_>>();
        let mut bitrev_remainders_s1 = remainders_s1
            .iter()
            .map(|a| M31::from_u32_unchecked(*a))
            .collect::<Vec<_>>();
        bit_reverse_coset_to_circle_domain_order(&mut bitrev_remainders_s0);
        bit_reverse_coset_to_circle_domain_order(&mut bitrev_remainders_s1);
        let mut cum_sum = cum_sum
            .iter()
            .map(|a| M31::from_u32_unchecked(*a))
            .collect::<Vec<_>>();

        let last_cum_sum = cum_sum.last().unwrap().0;

        let mut cum_sum_low = vec![M31(0); POLY_SIZE];
        cum_sum_low[POLY_SIZE - 1] = M31(last_cum_sum & ((1 << 14) - 1));
        let mut cum_sum_high = vec![M31(0); POLY_SIZE];
        cum_sum_high[POLY_SIZE - 1] = M31(last_cum_sum >> 14);

        bit_reverse_coset_to_circle_domain_order(&mut cum_sum);
        (
            [
                s0,
                borrows_s0,
                bitrev_remainders_s0,
                s1,
                borrows_s1,
                bitrev_remainders_s1,
                cum_sum.clone(),
                is_not_first,
                is_last,
                cum_sum_low,
                cum_sum_high,
            ]
            .into_iter()
            .map(|col| {
                CircleEvaluation::<SimdBackend, _, BitReversedOrder>::new(
                    domain,
                    BaseColumn::from_iter(col),
                )
            })
            .collect::<Vec<_>>(),
            remainders,
            (last_cum_sum & ((1 << 14) - 1), last_cum_sum >> 14),
        )
    }
}

// Actual component that is used in the framework
#[derive(Debug, Clone)]
pub struct Eval {
    /// The claim parameters
    pub claim: Claim,
    /// Lookup elements for range checking
    pub half_rc_lookup_elements: RCLookupElements,
    /// Lookup elements for input
    pub s0_lookup_elements: SubLookupElements,
    pub low_sig_bound_check_lookup_elements: RCLookupElements,
    pub high_sig_bound_check_lookup_elements: RCLookupElements,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.claim.log_size + 1
    }

    fn evaluate<E: stwo_constraint_framework::EvalAtRow>(&self, mut eval: E) -> E {
        // Those values were filled during the trace generation
        let s0 = eval.next_trace_mask();
        let borrow_s0 = eval.next_trace_mask();
        let remainder_s0 = eval.next_trace_mask();
        let s1 = eval.next_trace_mask();
        let borrow_s1 = eval.next_trace_mask();
        let remainder_s1 = eval.next_trace_mask();
        let [cum_sum_prev, cum_sum_current] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [-1, 0]);
        let is_not_first = eval.next_trace_mask();
        let is_last = eval.next_trace_mask();
        let low_cum_sum = eval.next_trace_mask();
        let high_cum_sum = eval.next_trace_mask();

        eval.add_to_relation(RelationEntry::new(
            &self.half_rc_lookup_elements,
            E::EF::one(),
            &[remainder_s0.clone()],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.half_rc_lookup_elements,
            E::EF::one(),
            &[remainder_s1.clone()],
        ));
        // case borrow is 0: coeff - remainder = 0
        // case borrow is 1: coeff + Q - coeff - coeff - remainder = 0 <=> Q - coeff - remainder = 0
        eval.add_constraint(
            s0.clone() + borrow_s0.clone() * (E::F::from(M31(Q)) - s0.clone() - s0.clone())
                - remainder_s0.clone(),
        );
        eval.add_constraint(
            s1.clone() + borrow_s1.clone() * (E::F::from(M31(Q)) - s1.clone() - s1.clone())
                - remainder_s1.clone(),
        );
        eval.add_constraint(is_not_first.clone() * (is_not_first.clone() - E::F::one()));
        eval.add_constraint(borrow_s0.clone() * (borrow_s0.clone() - E::F::one()));
        eval.add_constraint(borrow_s1.clone() * (borrow_s1.clone() - E::F::one()));
        //for the first row, cum_sum_current = remainder^2
        eval.add_constraint(
            (E::F::one() - is_not_first.clone())
                * (remainder_s0.clone() * remainder_s0.clone()
                    + remainder_s1.clone() * remainder_s1.clone()
                    - cum_sum_current.clone()),
        );
        // for all the rows except the first one, cum_sum_prev + remainder^2 = cum_sum_current
        eval.add_constraint(
            is_not_first.clone()
                * (cum_sum_prev
                    + remainder_s0.clone() * remainder_s0.clone()
                    + remainder_s1.clone() * remainder_s1.clone()
                    - cum_sum_current.clone()),
        );

        eval.add_to_relation(RelationEntry::new(
            &self.s0_lookup_elements,
            E::EF::one(),
            &[s0.clone()],
        ));

        // if it's the last row check if the signature is in the range
        eval.add_to_relation(RelationEntry::new(
            &self.low_sig_bound_check_lookup_elements,
            E::EF::from(is_last.clone()),
            &[low_cum_sum],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.high_sig_bound_check_lookup_elements,
            E::EF::from(is_last.clone()),
            &[high_cum_sum],
        ));

        eval.finalize_logup();
        eval
    }
}

#[derive(Debug, Clone)]
pub struct InteractionClaim {
    /// The claimed sum for the interaction
    pub claimed_sum: SecureField,
}

impl InteractionClaim {
    /// Mixes the interaction claim into the Fiat-Shamir channel.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }

    /// Generates the interaction trace for modular multiplication.
    ///
    /// This method creates the interaction trace that connects the multiplication component
    /// with the range check component through the lookup protocol.
    ///
    /// # Parameters
    ///
    /// - `trace`: The trace columns from the multiplication component
    /// - `lookup_elements`: The lookup elements for range checking
    ///
    /// # Returns
    ///
    /// Returns the interaction trace and the interaction claim.
    pub fn gen_interaction_trace(
        trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        half_rc_lookup_elements: &RCLookupElements,
        s0_lookup_elements: &SubLookupElements,
        low_sig_bound_check_lookup_elements: &RCLookupElements,
        high_sig_bound_check_lookup_elements: &RCLookupElements,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        InteractionClaim,
    ) {
        let log_size = trace[0].domain.log_size();
        let is_last = trace[8].clone();

        let mut logup_gen = LogupTraceGenerator::new(log_size);
        // Range check s0
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            // Get the remainder value from the trace (column 3)
            let result_packed = trace[2].data[vec_row];

            // Create the denominator using the lookup elements
            let denom: PackedQM31 = half_rc_lookup_elements.combine(&[result_packed]);

            // The numerator is 1 (we want to check that remainder is in the range)
            let numerator = PackedQM31::one();

            col_gen.write_frac(vec_row, numerator, denom);
        }
        col_gen.finalize_col();
        // Range check s1
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            // Get the remainder value from the trace (column 3)
            let result_packed = trace[5].data[vec_row];

            // Create the denominator using the lookup elements
            let denom: PackedQM31 = half_rc_lookup_elements.combine(&[result_packed]);

            // The numerator is 1 (we want to check that remainder is in the range)
            let numerator = PackedQM31::one();

            col_gen.write_frac(vec_row, numerator, denom);
        }
        col_gen.finalize_col();

        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let result_packed = trace[0].data[vec_row];
            let denom: PackedQM31 = s0_lookup_elements.combine(&[result_packed]);
            let numerator = PackedQM31::one();
            col_gen.write_frac(vec_row, numerator, denom);
        }
        col_gen.finalize_col();
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let result_packed = trace[9].data[vec_row];
            let denom: PackedQM31 = low_sig_bound_check_lookup_elements.combine(&[result_packed]);
            let numerator = PackedQM31::from(is_last.data[vec_row]);
            col_gen.write_frac(vec_row, numerator, denom);
        }
        col_gen.finalize_col();
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let result_packed = trace[10].data[vec_row];
            let denom: PackedQM31 = high_sig_bound_check_lookup_elements.combine(&[result_packed]);
            let numerator = PackedQM31::from(is_last.data[vec_row]);
            col_gen.write_frac(vec_row, numerator, denom);
        }
        col_gen.finalize_col();
        let (interaction_trace, claimed_sum) = logup_gen.finalize_last();
        (interaction_trace, InteractionClaim { claimed_sum })
    }
}

/// Type alias for the modular multiplication component.
pub type Component = FrameworkComponent<Eval>;
