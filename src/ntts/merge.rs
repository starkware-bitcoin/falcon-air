use stwo::core::fields::m31::M31;

use crate::{
    ntts::ROOTS,
    zq::{OperationElements, add::AddMod, mul::MulMod, sub::SubMod},
};

/// State structure for NTT merge operations containing polynomial coefficients and intermediate values.
///
/// This struct holds the state during NTT merge operations, which combine results from
/// smaller subproblems in the NTT tree structure. The merge operations use roots of unity
/// to properly combine the transformed polynomial coefficients.
///
/// # Fields
///
/// * `f0` - First polynomial coefficient from the left subproblem
/// * `f1` - Second polynomial coefficient from the right subproblem  
/// * `root_times_f1` - Intermediate result of f1 multiplied by the appropriate root of unity
/// * `f0_plus_root_times_f1` - Result of addition in the merge butterfly operation
/// * `f0_minus_root_times_f1` - Result of subtraction in the merge butterfly operation
#[derive(Clone)]
pub struct MergeNTTState<E: stwo_constraint_framework::EvalAtRow> {
    /// First polynomial coefficient from the left subproblem
    pub f0: E::F,
    /// Second polynomial coefficient from the right subproblem
    pub f1: E::F,
    /// Intermediate result: f1 multiplied by the appropriate root of unity with modular arithmetic components
    pub root_times_f1: OperationElements<E>,
    /// Merge butterfly result: f0 + root * f1 with modular arithmetic components
    pub f0_plus_root_times_f1: OperationElements<E>,
    /// Merge butterfly result: f0 - root * f1 with modular arithmetic components
    pub f0_minus_root_times_f1: OperationElements<E>,
}

/// Merge operations for Number Theoretic Transform (NTT).
///
/// This struct provides functionality for merging NTT results from smaller subproblems
/// into larger polynomial evaluations. The merge operations are essential for building
/// the complete NTT evaluation from the bottom-up approach used in the NTT algorithm.
///
/// The merge process uses roots of unity to properly combine polynomial coefficients
/// from different levels of the NTT tree structure.
pub struct MergeNTT;

impl MergeNTT {
    /// Evaluates merge operations for NTT polynomial combination.
    ///
    /// This function performs the merge operations that combine NTT results from smaller
    /// subproblems into larger polynomial evaluations. The merge process uses roots of unity
    /// to properly combine coefficients from different levels of the NTT tree.
    ///
    /// # Arguments
    ///
    /// * `f` - Array of merge state elements containing polynomial coefficients and intermediate values.
    ///   Expected to be in natural order with corresponding left and right polynomial indices.
    /// * `lookup_elements` - Lookup table elements for modular arithmetic operations.
    /// * `eval` - Evaluation context for constraint framework operations.
    #[allow(clippy::type_complexity)]
    pub fn evaluate<E: stwo_constraint_framework::EvalAtRow>(
        f: &[MergeNTTState<E>],
        lookup_elements: &crate::zq::range_check::LookupElements,
        eval: &mut E,
    ) {
        // Determine the appropriate root of unity based on the size of the input array
        // The root index is calculated as log2(len) + 1 to ensure proper scaling
        let root_index = f.len().ilog2() + 1;
        let root = ROOTS[root_index as usize];

        // Perform merge butterfly operations on each pair of coefficients
        for (i, elt) in f.iter().enumerate() {
            // Step 1: Compute f1 * root[i] using modular multiplication
            // where root[i] is the i-th root of unity for this merge level
            MulMod::evaluate(
                elt.f1.clone(),
                E::F::from(M31(root[2 * i])),
                elt.root_times_f1.quotient.clone(),
                elt.root_times_f1.remainder.clone(),
                lookup_elements,
                eval,
            );

            // Step 2a: Merge butterfly operation - compute f_ntt[2*i] = (f0 + root[i]*f1) % q
            AddMod::evaluate(
                elt.f0.clone(),
                elt.root_times_f1.remainder.clone(),
                elt.f0_plus_root_times_f1.quotient.clone(),
                elt.f0_plus_root_times_f1.remainder.clone(),
                lookup_elements,
                eval,
            );

            // Step 2b: Merge butterfly operation - compute f_ntt[2*i+1] = (f0 - root[i]*f1) % q
            SubMod::evaluate(
                elt.f0.clone(),
                elt.root_times_f1.remainder.clone(),
                elt.f0_minus_root_times_f1.quotient.clone(),
                elt.f0_minus_root_times_f1.remainder.clone(),
                lookup_elements,
                eval,
            );
        }
    }
}
