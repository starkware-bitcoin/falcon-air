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
/// STARK proof component for modular subtraction operations.
///
/// This struct represents the constraint system for modular subtraction
/// in the field Z_q. It contains the field elements that participate
/// in the subtraction operation and provides methods for constraint evaluation.
///
/// # Type Parameters
///
/// - `E`: The evaluation context type that implements `EvalAtRow`
/// - `E::F`: The field type for arithmetic operations
///
/// # Fields
///
/// - `a`: First operand (minuend) for the subtraction operation
/// - `b`: Second operand (subtrahend) for the subtraction operation  
/// - `borrow`: Borrow indicator (0 or 1) indicating if q was borrowed
/// - `r`: Remainder representing the final result (a - b) mod q
#[derive(Debug, Clone)]
pub struct SubMod<E: stwo_constraint_framework::EvalAtRow> {
    pub a: E::F,
    pub b: E::F,
    pub borrow: E::F,
    pub r: E::F,
}

impl<E: stwo_constraint_framework::EvalAtRow> SubMod<E> {
    /// Creates a new modular subtraction constraint component.
    ///
    /// # Parameters
    ///
    /// - `a`: First operand (minuend) for the subtraction operation
    /// - `b`: Second operand (subtrahend) for the subtraction operation
    /// - `borrow`: Borrow indicator (0 or 1) indicating if q was borrowed
    /// - `r`: Remainder representing the final result (a - b) mod q
    ///
    /// # Returns
    ///
    /// Returns a new `SubMod` instance with the specified field elements.
    pub fn new(a: E::F, b: E::F, borrow: E::F, r: E::F) -> Self {
        Self { a, b, borrow, r }
    }

    /// Evaluates the modular subtraction constraints and establishes lookup relations.
    ///
    /// This function enforces the mathematical correctness of modular subtraction
    /// and connects the result to the range checking system through lookup relations.
    ///
    /// # Parameters
    ///
    /// - `lookup_elements`: The range checking lookup elements for validation
    /// - `eval`: The evaluation context for adding constraints and relations
    ///
    /// # Constraints Enforced
    ///
    /// 1. **Modular Arithmetic**: a + borrow * q - b = remainder
    ///    This ensures that the difference equals the remainder when properly reduced modulo q
    ///
    /// 2. **Borrow Validation**: borrow * (borrow - 1) = 0
    ///    This constraint ensures that borrow can only be 0 or 1
    ///
    /// 3. **Range Checking**: The remainder r is added to the range check lookup table
    ///    This validates that r ∈ [0, Q) through the lookup protocol
    pub fn evaluate(self, lookup_elements: &RCLookupElements, eval: &mut E) {
        // Enforce the modular arithmetic constraint: a + borrow * q - b = remainder
        // This ensures mathematical correctness of the modular subtraction
        eval.add_constraint(
            self.a + self.borrow.clone() * E::F::from(M31(Q)) - self.b - self.r.clone(),
        );

        // Enforce the borrow constraint: borrow * (borrow - 1) = 0
        // This ensures that borrow can only be 0 or 1 (binary constraint)
        eval.add_constraint(self.borrow.clone() * (self.borrow - E::F::one()));

        // Add the remainder to the range check lookup table
        // This establishes the lookup relation for range checking validation
        // The multiplicity is set to 1 since each remainder appears once in the trace
        eval.add_to_relation(RelationEntry::new(lookup_elements, E::EF::one(), &[self.r]));
    }
}
