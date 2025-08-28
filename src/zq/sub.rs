//! # Modular Subtraction Component
//!
//! This module implements STARK proof components for modular subtraction operations.
//!
//! The modular subtraction operation computes (a - b) mod q, where q = 12289.
//! The operation is decomposed into:
//! - a - b = borrow * q + remainder
//! - where remainder ∈ [0, q) and borrow ∈ {0, 1}
//!
//! The component generates traces for the operands (a, b), borrow, and remainder,
//! and enforces the constraint that the remainder is within the valid range.

use num_traits::One;
use stwo::core::fields::m31::M31;
use stwo_constraint_framework::RelationEntry;

use crate::{big_air::relation::RCLookupElements, zq::Q};

pub const SUB_COL: usize = 2;

#[derive(Debug, Clone)]
pub struct SubMod<E: stwo_constraint_framework::EvalAtRow> {
    pub a: E::F,
    pub b: E::F,
    pub borrow: E::F,
    pub r: E::F,
}

impl<E: stwo_constraint_framework::EvalAtRow> SubMod<E> {
    pub fn new(a: E::F, b: E::F, borrow: E::F, r: E::F) -> Self {
        Self { a, b, borrow, r }
    }

    pub fn evaluate(self, lookup_elements: &RCLookupElements, eval: &mut E) {
        eval.add_constraint(
            self.a + self.borrow.clone() * E::F::from(M31(Q)) - self.b - self.r.clone(),
        );
        eval.add_constraint(self.borrow.clone() * (self.borrow - E::F::one()));

        eval.add_to_relation(RelationEntry::new(lookup_elements, E::EF::one(), &[self.r]));
    }
}
