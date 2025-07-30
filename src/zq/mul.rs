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
pub struct MulMod;
impl MulMod {
    pub fn evaluate<E: stwo_constraint_framework::EvalAtRow>(
        a: E::F,
        b: E::F,
        q: E::F,
        r: E::F,
        lookup_elements: &super::range_check::LookupElements,
        eval: &mut E,
    ) {
        // Extract trace values
        eval.add_constraint(a * b - q * r.clone());
        // Now we need to check that the remainder is in the range [0, Q)
        // We do this by using the range check we defined. Here we increment the multiplicity of
        // this value (remainder) by 1 because we want to range check it and the logup sum has to be exactly 0
        // So here we increment and in the range_check we decrements
        eval.add_to_relation(RelationEntry::new(lookup_elements, E::EF::one(), &[r]));
    }
}
