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
use crate::zq::{add::AddMod, mul::MulMod, range_check, sub::SubMod};

/// Collection of merge operations for NTT polynomial combination.
///
/// This struct holds a vector of merge operations that will be evaluated
/// together to combine NTT results from smaller subproblems into larger
/// polynomial evaluations.
#[derive(Clone, Debug)]
pub struct MergeNTT<E: stwo_constraint_framework::EvalAtRow>(pub Vec<Merge<E>>);

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
/// Each operation includes modular arithmetic components for range checking.
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
impl<E: stwo_constraint_framework::EvalAtRow> Default for MergeNTT<E> {
    /// Creates an empty collection of merge operations.
    ///
    /// Returns a new `MergeNTT` instance with an empty vector of merge operations.
    /// This is typically used as a starting point for building up merge operations
    /// during the NTT computation.
    fn default() -> Self {
        Self(vec![])
    }
}

impl<E: stwo_constraint_framework::EvalAtRow> MergeNTT<E> {
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
    /// Returns a vector of merged polynomial coefficients from the NTT computation
    pub fn evaluate(
        self,
        lookup_elements: &range_check::LookupElements,
        eval: &mut E,
    ) -> Vec<E::F> {
        // Perform merge butterfly operations on each pair of coefficients
        let mut result = vec![];
        for merge in self.0.into_iter() {
            // Step 1: Compute f1_ntt[i] * root[i] using modular multiplication
            // where root[i] is the i-th root of unity for this merge level
            MulMod::evaluate(merge.root_times_f1, lookup_elements, eval);

            result.push(merge.f0_plus_root_times_f1.r.clone());
            // Step 2a: Merge butterfly operation - compute f_ntt[2*i] = (f0_ntt[i] + root[i]*f1_ntt[i]) % q
            AddMod::evaluate(merge.f0_plus_root_times_f1, lookup_elements, eval);

            // Step 2b: Merge butterfly operation - compute f_ntt[2*i+1] = (f0_ntt[i] - root[i]*f1_ntt[i]) % q
            result.push(merge.f0_minus_root_times_f1.r.clone());
            SubMod::evaluate(merge.f0_minus_root_times_f1, lookup_elements, eval);
        }
        result
    }

    /// Adds a merge operation to the collection.
    ///
    /// This method adds a single merge operation to the collection of merge operations.
    /// The merge operation will be evaluated when `evaluate()` is called.
    ///
    /// # Arguments
    ///
    /// * `merge` - The merge operation to add to the collection
    pub fn push(&mut self, merge: Merge<E>) {
        self.0.push(merge);
    }
}
