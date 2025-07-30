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
use core::borrow;

use num_traits::One;
use stwo::core::fields::m31::M31;
use stwo_constraint_framework::RelationEntry;

use crate::zq::Q;
pub struct SubMod;
impl SubMod {
    pub fn evaluate<E: stwo_constraint_framework::EvalAtRow>(
        a: E::F,
        b: E::F,
        borrow: E::F,
        r: E::F,
        lookup_elements: &super::range_check::LookupElements,
        eval: &mut E,
    ) {
        // this is the constraint for add_mod_12289
        // a - b = remainder + borrow * Q
        eval.add_constraint(
            a - b - r.clone() + borrow.clone() * E::F::from(M31::from_u32_unchecked(Q)),
        );
        eval.add_constraint(borrow.clone() * (borrow - E::F::one()));

        eval.add_to_relation(RelationEntry::new(lookup_elements, E::EF::one(), &[r]));
    }
}
