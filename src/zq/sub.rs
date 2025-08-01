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

use crate::zq::Q;

#[derive(Debug, Clone)]
pub struct SubMod<E: stwo_constraint_framework::EvalAtRow> {
    pub a: E::F,
    pub b: E::F,
    pub borrow: E::F,
    pub r: E::F,
}

impl<E: stwo_constraint_framework::EvalAtRow> SubMod<E> {
    pub fn evaluate(self, lookup_elements: &super::range_check::LookupElements, eval: &mut E) {
        // this is the constraint for add_mod_12289
        // a - b = remainder + borrow * Q
        eval.add_constraint(
            self.a - self.b - self.r.clone()
                + self.borrow.clone() * E::F::from(M31::from_u32_unchecked(Q)),
        );
        eval.add_constraint(self.borrow.clone() * (self.borrow - E::F::one()));

        eval.add_to_relation(RelationEntry::new(lookup_elements, E::EF::one(), &[self.r]));
    }
}
