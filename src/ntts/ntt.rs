use stwo::core::fields::m31::M31;

use crate::{
    ntts::{
        ROOTS,
        merge::{MergeNTT, MergeNTTState},
    },
    zq::{OperationElements, add::AddMod, mul::MulMod, sub::SubMod},
};

/// Number Theoretic Transform (NTT) implementation for polynomial evaluation.
///
/// This struct provides functionality for performing NTT operations on polynomials
/// over finite fields. The NTT is a generalization of the Fast Fourier Transform
/// that works over finite fields and is commonly used in cryptographic protocols
/// like STARKs and SNARKs.
///
/// The `HALF_POLY_DEGREE` parameter represents half the degree of the polynomial
/// being transformed, as NTT operations typically work with power-of-2 degrees.
pub struct NTT<const HALF_POLY_DEGREE: usize>;

/// State structure for NTT evaluation containing polynomial coefficients and intermediate values.
///
/// This struct holds the current state during NTT evaluation, including:
/// - `f0`, `f1`: The two polynomial coefficients being processed
/// - `f1_times_sq1_elts`: Intermediate result of f1 multiplied by sqrt(-1)
/// - `f0_plus_f1_times_sq1_elts`: Result of the addition in the butterfly operation
/// - `f0_minus_f1_times_sq1_elts`: Result of the subtraction in the butterfly operation
///
/// The `OperationElements<E>` type contains both quotient and remainder values
/// for modular arithmetic operations.
#[derive(Clone, Debug)]
pub struct NTTState<E: stwo_constraint_framework::EvalAtRow> {
    /// First polynomial coefficient
    pub f0: E::F,
    /// Second polynomial coefficient  
    pub f1: E::F,
    /// Intermediate result: f1 * sqrt(-1) with modular arithmetic components
    pub f1_times_sq1_elts: OperationElements<E>,
    /// Butterfly operation result: f0 + f1 * sqrt(-1) with modular arithmetic components
    pub f0_plus_f1_times_sq1_elts: OperationElements<E>,
    /// Butterfly operation result: f0 - f1 * sqrt(-1) with modular arithmetic components
    pub f0_minus_f1_times_sq1_elts: OperationElements<E>,
}

impl<const HALF_POLY_DEGREE: usize> NTT<HALF_POLY_DEGREE> {
    #[allow(clippy::type_complexity)]
    /// Evaluates the Number Theoretic Transform on a polynomial.
    ///
    /// This function performs the NTT evaluation using a butterfly network structure.
    /// The input polynomial coefficients are expected to be in bit-reversed order.
    ///
    /// # Arguments
    ///
    /// * `f` - Array of NTT state elements containing polynomial coefficients and intermediate values.
    ///   Expected to be in bit-reversed order.
    /// * `to_merge` - Array of merge operations to be performed after the butterfly operations.
    ///   Each element contains states for merging at different levels of the NTT tree.
    /// * `lookup_elements` - Lookup table elements for modular arithmetic operations.
    /// * `eval` - Evaluation context for constraint framework operations.
    pub fn evaluate<E: stwo_constraint_framework::EvalAtRow>(
        f: &[NTTState<E>; HALF_POLY_DEGREE],
        to_merge: &[&[MergeNTTState<E>; HALF_POLY_DEGREE]],
        lookup_elements: &crate::zq::range_check::LookupElements,
        eval: &mut E,
    ) {
        // sqrt(-1) % q
        let sq1 = E::F::from(M31(ROOTS[0][0]));

        // Perform butterfly operations on each pair of coefficients
        for elt in f {
            // Step 1: Compute f1 * sqrt(-1) using modular multiplication
            MulMod::evaluate(
                sq1.clone(),
                elt.f1.clone(),
                elt.f1_times_sq1_elts.quotient.clone(),
                elt.f1_times_sq1_elts.remainder.clone(),
                lookup_elements,
                eval,
            );

            // Step 2a: Butterfly operation - compute f_ntt[0] = (f[0] + sqrt(-1) * f[1]) % q
            AddMod::evaluate(
                elt.f0.clone(),
                elt.f1_times_sq1_elts.remainder.clone(),
                elt.f0_plus_f1_times_sq1_elts.quotient.clone(),
                elt.f0_plus_f1_times_sq1_elts.remainder.clone(),
                lookup_elements,
                eval,
            );

            // Step 2b: Butterfly operation - compute f_ntt[1] = (f[0] - sqrt(-1) * f[1]) % q
            SubMod::evaluate(
                elt.f0.clone(),
                elt.f1_times_sq1_elts.remainder.clone(),
                elt.f0_minus_f1_times_sq1_elts.quotient.clone(),
                elt.f0_minus_f1_times_sq1_elts.remainder.clone(),
                lookup_elements,
                eval,
            );
        }

        // Step 3: Perform merge operations to combine results from butterfly operations
        // The to_merge array contains all the merging steps for different levels of the NTT tree
        for merge in to_merge {
            // Perform the merge operation for this chunk
            MergeNTT::evaluate(*merge, lookup_elements, eval);
        }
    }
}
