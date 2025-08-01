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
use stwo_constraint_framework::RelationEntry;

#[derive(Debug, Clone)]
pub struct MulMod<E: stwo_constraint_framework::EvalAtRow> {
    pub a: E::F,
    pub b: E::F,
    pub q: E::F,
    pub r: E::F,
}

impl<E: stwo_constraint_framework::EvalAtRow> MulMod<E> {
    pub fn evaluate(self, lookup_elements: &super::range_check::LookupElements, eval: &mut E) {
        // Extract trace values
        eval.add_constraint(self.a * self.b - self.q * self.r.clone());
        // Now we need to check that the remainder is in the range [0, Q)
        // We do this by using the range check we defined. Here we increment the multiplicity of
        // this value (remainder) by 1 because we want to range check it and the logup sum has to be exactly 0
        // So here we increment and in the range_check we decrements
        eval.add_to_relation(RelationEntry::new(lookup_elements, E::EF::one(), &[self.r]));
    }
}
