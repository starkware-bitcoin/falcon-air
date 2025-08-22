//! # Modular Multiplication Component
//!
//! This module implements STARK proof components for modular multiplication operations.
//!
//! The modular multiplication operation computes (a * b) mod q, where q = 12289.
//! The operation is decomposed into:
//! - a * b = quotient * q + remainder
//! - where remainder ∈ [0, q)
//!
//! The component generates traces for the operands (a, b), quotient, and remainder,
//! and enforces the constraint that the remainder is within the valid range.

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
    POLY_SIZE, SIGNATURE_BOUND,
    big_air::relation::{RCLookupElements, SubLookupElements},
    zq::Q,
};

// This is a helper function for the prover to generate the trace for the mul component
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

    /// Generates the trace for the mul component
    /// Generates 2 random numbers and creates a trace for the mul component
    /// returns the columns in this order: a, b, quotient, remainder
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

        let base_exp = 14;
        let base = 1 << base_exp;
        let r = (SIGNATURE_BOUND % base) as i32;
        let q = (SIGNATURE_BOUND / base) as i32;
        let last_cum_sum = cum_sum[POLY_SIZE - 1].0;
        let x0 = last_cum_sum % base;
        let b0 = ((r - x0 as i32) < 0) as i32;
        let x1 = ((last_cum_sum >> base_exp) % base) as i32;
        let b1 = ((q - x1 - b0) > 0) as u32;
        debug_assert_eq!(b1, 0);
        let mut x0_col = vec![M31(0); POLY_SIZE];
        x0_col[POLY_SIZE - 1] = M31(x0);
        let mut x1_col = vec![M31(0); POLY_SIZE];
        x1_col[POLY_SIZE - 1] = M31(x1 as u32);
        let mut b0_col = vec![M31(0); POLY_SIZE];
        b0_col[POLY_SIZE - 1] = M31(b0 as u32);
        let mut b1_col = vec![M31(0); POLY_SIZE];
        b1_col[POLY_SIZE - 1] = M31(b1);

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
                x0_col,
                x1_col,
                b0_col,
                b1_col,
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
            (x0, x1 as u32),
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
    pub signature_bound_lookup_elements: RCLookupElements,
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
        let x0 = eval.next_trace_mask();
        let x1 = eval.next_trace_mask();
        let b0 = eval.next_trace_mask();
        let b1 = eval.next_trace_mask();

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
            &self.signature_bound_lookup_elements,
            E::EF::from(is_last.clone()),
            &[x0],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.signature_bound_lookup_elements,
            E::EF::from(is_last.clone()),
            &[x1],
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
        signature_bound_lookup_elements: &RCLookupElements,
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
            let denom: PackedQM31 = signature_bound_lookup_elements.combine(&[result_packed]);
            let numerator = PackedQM31::from(is_last.data[vec_row]);
            col_gen.write_frac(vec_row, numerator, denom);
        }
        col_gen.finalize_col();
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let result_packed = trace[10].data[vec_row];
            let denom: PackedQM31 = signature_bound_lookup_elements.combine(&[result_packed]);
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
