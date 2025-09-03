//! # Modular Addition Component
//!
//! This module implements STARK proof components for modular addition operations
//! in the field Z_q where q = 12289.
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

use crate::{big_air::relation::RCLookupElements, zq::Q};

/// STARK proof component for modular addition operations.
///
/// This struct represents the constraint system for modular addition
/// in the field Z_q. It contains the field elements that participate
/// in the addition operation and provides methods for constraint evaluation.
///
/// # Type Parameters
///
/// - `E`: The evaluation context type that implements `EvalAtRow`
/// - `E::F`: The field type for arithmetic operations
///
/// # Fields
///
/// - `a`: First operand for the addition operation
/// - `b`: Second operand for the addition operation  
/// - `q`: Quotient representing how many times q divides (a + b)
/// - `r`: Remainder representing the final result (a + b) mod q
#[derive(Debug, Clone)]
pub struct AddMod<E: stwo_constraint_framework::EvalAtRow> {
    pub a: E::F,
    pub b: E::F,
    pub q: E::F,
    pub r: E::F,
}

impl<E: stwo_constraint_framework::EvalAtRow> AddMod<E> {
    /// Creates a new modular addition constraint component.
    ///
    /// # Parameters
    ///
    /// - `a`: First operand for the addition operation
    /// - `b`: Second operand for the addition operation
    /// - `q`: Quotient representing how many times q divides (a + b)
    /// - `r`: Remainder representing the final result (a + b) mod q
    ///
    /// # Returns
    ///
    /// Returns a new `AddMod` instance with the specified field elements.
    pub fn new(a: E::F, b: E::F, q: E::F, r: E::F) -> Self {
        Self { a, b, q, r }
    }

    /// Evaluates the modular addition constraints and establishes lookup relations.
    ///
    /// This function enforces the mathematical correctness of modular addition
    /// and connects the result to the range checking system through lookup relations.
    ///
    /// # Parameters
    ///
    /// - `lookup_elements`: The range checking lookup elements for validation
    /// - `eval`: The evaluation context for adding constraints and relations
    ///
    /// # Constraints Enforced
    ///
    /// 1. **Modular Arithmetic**: a + b = q * Q + r
    ///    This ensures that the sum equals the quotient times the field size plus the remainder
    ///
    /// 2. **Range Checking**: The remainder r is added to the range check lookup table
    ///    This validates that r ∈ [0, Q) through the lookup protocol
    pub fn evaluate(self, lookup_elements: &RCLookupElements, eval: &mut E) {
        // Enforce the modular arithmetic constraint: a + b = q * Q + r
        // This ensures mathematical correctness of the modular addition
        eval.add_constraint(self.a + self.b - self.q * E::F::from(M31(Q)) - self.r.clone());

        // Add the remainder to the range check lookup table
        // This establishes the lookup relation for range checking validation
        // The multiplicity is set to 1 since each remainder appears once in the trace
        eval.add_to_relation(RelationEntry::new(lookup_elements, E::EF::one(), &[self.r]));
    }
}
