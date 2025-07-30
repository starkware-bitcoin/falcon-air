//! # Modular Addition Component
//!
//! This module implements STARK proof components for modular addition operations.
//!
//! The modular addition operation computes (a + b) mod q, where q = 12289.
//! The operation is decomposed into:
//! - a + b = quotient * q + remainder
//! - where remainder ∈ [0, q)
//!
//! The component generates traces for the operands (a, b), quotient, and remainder,
//! and enforces the constraint that the remainder is within the valid range.
use num_traits::One;
use stwo::core::fields::m31::M31;
use stwo_constraint_framework::RelationEntry;

use crate::{
    ntts::{ROOTS, inverses::INVERSES_MOD_Q},
    zq::{OperationElements, add::AddMod, mul::MulMod, sub::SubMod},
};
pub struct SplitNTTState<E: stwo_constraint_framework::EvalAtRow> {
    f_odd: E::F,
    f_even: E::F,
    f_even_plus_f_odd: OperationElements<E>,
    i2_times_f_even_plus_f_odd: OperationElements<E>,
    f_even_minus_f_odd: OperationElements<E>,
    i2_times_f_even_minus_f_odd: OperationElements<E>,
    root_inv_mul: OperationElements<E>,
}
pub struct SplitNTT<const POLY_LOG_DEGREE: usize>;

impl<const HALF_POLY_DEGREE: usize> SplitNTT<HALF_POLY_DEGREE> {
    #[allow(clippy::type_complexity)]
    pub fn evaluate<E: stwo_constraint_framework::EvalAtRow>(
        &self,
        f: &[SplitNTTState<E>; HALF_POLY_DEGREE],
        lookup_elements: &crate::zq::range_check::LookupElements,
        eval: &mut E,
    ) {
        let root_index = HALF_POLY_DEGREE.ilog2() + 1;
        let root = ROOTS[root_index as usize];
        let inverse_2 = E::F::from(M31::from_u32_unchecked(INVERSES_MOD_Q[2]));

        for (i, elt) in f.iter().enumerate() {
            // f0_ntt[i] = (i2 * (f_ntt[2 * i] + f_ntt[2 * i + 1])) % q

            AddMod::evaluate(
                elt.f_even.clone(),
                elt.f_odd.clone(),
                elt.f_even_plus_f_odd.quotient.clone(),
                elt.f_even_plus_f_odd.remainder.clone(),
                lookup_elements,
                eval,
            );
            MulMod::evaluate(
                inverse_2.clone(),
                elt.f_even_plus_f_odd.remainder.clone(),
                elt.i2_times_f_even_plus_f_odd.quotient.clone(),
                elt.i2_times_f_even_plus_f_odd.remainder.clone(),
                lookup_elements,
                eval,
            );
            // f1_ntt[i] = (i2 * (f_ntt[2 * i] - f_ntt[2 * i + 1]) * inv_mod_q[w[2 * i]]) % q
            SubMod::evaluate(
                elt.f_even.clone(),
                elt.f_odd.clone(),
                elt.f_even_minus_f_odd.quotient.clone(),
                elt.f_even_minus_f_odd.remainder.clone(),
                lookup_elements,
                eval,
            );
            MulMod::evaluate(
                inverse_2.clone(),
                elt.f_even_minus_f_odd.remainder.clone(),
                elt.i2_times_f_even_minus_f_odd.quotient.clone(),
                elt.i2_times_f_even_minus_f_odd.remainder.clone(),
                lookup_elements,
                eval,
            );
            MulMod::evaluate(
                elt.i2_times_f_even_minus_f_odd.remainder.clone(),
                E::F::from(M31(root[2 * i])),
                elt.root_inv_mul.quotient.clone(),
                elt.root_inv_mul.remainder.clone(),
                lookup_elements,
                eval,
            );
        }
    }
}
