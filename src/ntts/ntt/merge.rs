//! NTT Merge Operations Module
//!
//! This module implements the merging operations used in the Number Theoretic Transform (NTT).
//! The merge operations combine results from smaller subproblems into larger polynomial
//! evaluations using roots of unity.
//!
//! The merge process is a key component of the NTT algorithm that:
//! 1. Takes two polynomials (f0_ntt, f1_ntt) from previous NTT levels
//! 2. Combines them using roots of unity to produce larger polynomial evaluations
//! 3. Performs modular arithmetic operations with range checking
//! 4. Returns the merged polynomial coefficients
//!
//! Each merge operation implements the butterfly pattern:
//!   f_ntt[2*i] = (f0_ntt[i] + root[i] * f1_ntt[i]) % q
//!   f_ntt[2*i+1] = (f0_ntt[i] - root[i] * f1_ntt[i]) % q
//!
//! where root[i] is the appropriate root of unity for the current merge level.
//!
//! # Mathematical Foundation
//!
//! The merge operation implements the Cooley-Tukey butterfly pattern used in FFT/NTT algorithms.
//! Given two polynomials f0_ntt and f1_ntt of size n/2, and a root of unity ω, the merge
//! produces a polynomial of size n by computing:
//!
//! f_ntt[2*i] = f0_ntt[i] + ω^i * f1_ntt[i]
//! f_ntt[2*i+1] = f0_ntt[i] - ω^i * f1_ntt[i]
//!
//! This operation preserves the NTT property and allows recursive construction
//! of larger polynomial evaluations from smaller ones.
use crate::{
    big_air::relation::RCLookupElements,
    zq::{add::AddMod, mul::MulMod, sub::SubMod},
};

/// Single merge operation for NTT polynomial combination.
///
/// This struct represents one merge operation that combines two coefficients
/// from different NTT subproblems using a root of unity. The merge operation
/// implements the butterfly pattern used in the NTT algorithm.
///
/// The merge operation performs:
/// 1. Multiplication of f1_ntt by root of unity
/// 2. Addition of f0_ntt and the multiplied result
/// 3. Subtraction of the multiplied result from f0_ntt
///
/// Each operation includes modular arithmetic components for range checking
/// to ensure all intermediate values remain within field bounds [0, Q).
#[derive(Clone, Debug)]
pub struct Merge<E: stwo_constraint_framework::EvalAtRow> {
    /// Multiplication operation: f1_ntt[i] * root[i] with modular arithmetic components
    pub root_times_f1: MulMod<E>,
    /// Addition operation: f0_ntt[i] + root[i] * f1_ntt[i] with modular arithmetic components
    pub f0_plus_root_times_f1: AddMod<E>,
    /// Subtraction operation: f0_ntt[i] - root[i] * f1_ntt[i] with modular arithmetic components
    pub f0_minus_root_times_f1: SubMod<E>,
}
impl<E: stwo_constraint_framework::EvalAtRow> Merge<E> {
    /// Creates a new merge operation for NTT polynomial combination.
    ///
    /// This constructor creates a merge operation that combines two coefficients
    /// using a root of unity. The operation includes all three arithmetic steps:
    /// multiplication, addition, and subtraction with modular arithmetic components.
    ///
    /// # Arguments
    ///
    /// * `root_times_f1` - Multiplication operation: f1_ntt[i] * root[i]
    /// * `f0_plus_root_times_f1` - Addition operation: f0_ntt[i] + root[i] * f1_ntt[i]
    /// * `f0_minus_root_times_f1` - Subtraction operation: f0_ntt[i] - root[i] * f1_ntt[i]
    ///
    /// # Returns
    ///
    /// Returns a new `Merge` instance ready for evaluation.
    pub fn new(
        root_times_f1: MulMod<E>,
        f0_plus_root_times_f1: AddMod<E>,
        f0_minus_root_times_f1: SubMod<E>,
    ) -> Self {
        Self {
            root_times_f1,
            f0_plus_root_times_f1,
            f0_minus_root_times_f1,
        }
    }
}

impl<E: stwo_constraint_framework::EvalAtRow> Merge<E> {
    /// Evaluates merge operations for NTT polynomial combination.
    ///
    /// This function performs the merge operations that combine NTT results from smaller
    /// subproblems into larger polynomial evaluations. The merge process uses roots of unity
    /// to properly combine coefficients from different levels of the NTT tree.
    ///
    /// The evaluation process:
    /// 1. Evaluates each merge operation in sequence
    /// 2. Performs modular multiplication with root of unity
    /// 3. Performs modular addition and subtraction for butterfly operations
    /// 4. Returns the merged polynomial coefficients
    ///
    /// # Arguments
    ///
    /// * `lookup_elements` - Lookup table elements for modular arithmetic operations and range checking
    /// * `eval` - Evaluation context for constraint framework operations
    ///
    /// # Returns
    ///
    /// Returns a vector of merged polynomial coefficients from the NTT computation.
    /// The coefficients are in evaluation form and ready for the next NTT level.
    pub fn evaluate(self, lookup_elements: &RCLookupElements, eval: &mut E) -> [E::F; 2] {
        // Perform merge butterfly operations on each pair of coefficients

        let result = [
            self.f0_plus_root_times_f1.r.clone(),
            self.f0_minus_root_times_f1.r.clone(),
        ];
        // Step 1: Compute f1_ntt[i] * root[i] using modular multiplication
        // where root[i] is the i-th root of unity for this merge level
        MulMod::evaluate(self.root_times_f1, lookup_elements, eval);

        // Step 2a: Merge butterfly operation - compute f_ntt[2*i] = (f0_ntt[i] + root[i]*f1_ntt[i]) % q
        AddMod::evaluate(self.f0_plus_root_times_f1, lookup_elements, eval);

        // Step 2b: Merge butterfly operation - compute f_ntt[2*i+1] = (f0_ntt[i] - root[i]*f1_ntt[i]) % q

        SubMod::evaluate(self.f0_minus_root_times_f1, lookup_elements, eval);

        result
    }
}
