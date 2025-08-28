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
use num_traits::One;
use stwo::core::fields::m31::M31;
use stwo_constraint_framework::RelationEntry;

use crate::{big_air::relation::RCLookupElements, zq::Q};

pub const MUL_COL: usize = 1;

#[derive(Debug, Clone)]
pub struct MulMod<E: stwo_constraint_framework::EvalAtRow> {
    pub a: E::F,
    pub b: E::F,
    pub q: E::F,
    pub r: E::F,
}

impl<E: stwo_constraint_framework::EvalAtRow> MulMod<E> {
    pub fn new(a: E::F, b: E::F, q: E::F, r: E::F) -> Self {
        Self { a, b, q, r }
    }

    pub fn evaluate(self, lookup_elements: &RCLookupElements, eval: &mut E) {
        // Enforce modular arithmetic constraint: a * b = q * Q + r
        eval.add_constraint(self.a * self.b - self.q * E::F::from(M31(Q)) - self.r.clone());

        // Add remainder to range check lookup (increment multiplicity for range checking)
        eval.add_to_relation(RelationEntry::new(lookup_elements, E::EF::one(), &[self.r]));
    }
}
