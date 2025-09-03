//! INTT Split Operations Module
//!
//! This module implements the splitting operations used in the Inverse Number Theoretic Transform (INTT).
//! The split operations decompose polynomial evaluations into smaller subproblems using inverse roots
//! of unity and scaling factors.
//!
//! The split process is a key component of the INTT algorithm that:
//! 1. Takes polynomial evaluations from the previous INTT level
//! 2. Splits them into even and odd coefficients
//! 3. Applies scaling factor I2 (1/2) and inverse roots of unity
//! 4. Returns two smaller polynomials for recursive INTT computation
//!
//! Each split operation implements the inverse butterfly pattern:
//!   f0_ntt[i] = I2 * (f_even[i] + f_odd[i]) % q
//!   f1_ntt[i] = I2 * (f_even[i] - f_odd[i]) * inv_root[i] % q
//!
//! where I2 = 1/2 and inv_root[i] is the inverse of the appropriate root of unity.

use crate::{
    big_air::relation::RCLookupElements,
    zq::{add::AddMod, mul::MulMod, sub::SubMod},
};

/// Single split operation for INTT polynomial decomposition.
///
/// This struct represents one split operation that decomposes two coefficients
/// from a larger polynomial into smaller subproblems using inverse roots of unity
/// and scaling factors. The split operation implements the inverse butterfly pattern
/// used in the INTT algorithm.
///
/// The split operation performs:
/// 1. Addition of even and odd coefficients
/// 2. Scaling by I2 (1/2) for the sum
/// 3. Subtraction of odd from even coefficients
/// 4. Scaling by I2 (1/2) for the difference
/// 5. Multiplication by inverse root of unity
///
/// Each operation includes modular arithmetic components for range checking.
#[derive(Clone, Debug)]
pub struct Split<E: stwo_constraint_framework::EvalAtRow> {
    /// Addition operation: f_even[i] + f_odd[i] with modular arithmetic components
    pub f_even_plus_f_odd: AddMod<E>,
    /// Scaling operation: I2 * (f_even[i] + f_odd[i]) with modular arithmetic components
    pub i2_times_f_even_plus_f_odd: MulMod<E>,
    /// Subtraction operation: f_even[i] - f_odd[i] with modular arithmetic components
    pub f_even_minus_f_odd: SubMod<E>,
    /// Scaling operation: I2 * (f_even[i] - f_odd[i]) with modular arithmetic components
    pub i2_times_f_even_minus_f_odd: MulMod<E>,
    /// Inverse root multiplication: I2 * (f_even[i] - f_odd[i]) * inv_root[i] with modular arithmetic components
    pub i2_times_f_even_minus_f_odd_times_root_inv: MulMod<E>,
}
impl<E: stwo_constraint_framework::EvalAtRow> Split<E> {
    /// Creates a new split operation for INTT polynomial decomposition.
    ///
    /// This constructor creates a split operation that decomposes two coefficients
    /// using inverse roots of unity and scaling factors. The operation includes all
    /// five arithmetic steps: addition, scaling, subtraction, scaling, and inverse
    /// root multiplication with modular arithmetic components.
    ///
    /// # Arguments
    ///
    /// * `f_even_plus_f_odd` - Addition operation: f_even[i] + f_odd[i]
    /// * `i2_times_f_even_plus_f_odd` - Scaling operation: I2 * (f_even[i] + f_odd[i])
    /// * `f_even_minus_f_odd` - Subtraction operation: f_even[i] - f_odd[i]
    /// * `i2_times_f_even_minus_f_odd` - Scaling operation: I2 * (f_even[i] - f_odd[i])
    /// * `i2_times_f_even_minus_f_odd_times_root_inv` - Inverse root multiplication: I2 * (f_even[i] - f_odd[i]) * inv_root[i]
    ///
    /// # Returns
    ///
    /// Returns a new `Split` instance ready for evaluation.
    pub fn new(
        f_even_plus_f_odd: AddMod<E>,
        i2_times_f_even_plus_f_odd: MulMod<E>,
        f_even_minus_f_odd: SubMod<E>,
        i2_times_f_even_minus_f_odd: MulMod<E>,
        i2_times_f_even_minus_f_odd_times_root_inv: MulMod<E>,
    ) -> Self {
        Self {
            f_even_plus_f_odd,
            i2_times_f_even_plus_f_odd,
            f_even_minus_f_odd,
            i2_times_f_even_minus_f_odd,
            i2_times_f_even_minus_f_odd_times_root_inv,
        }
    }
}

impl<E: stwo_constraint_framework::EvalAtRow> Split<E> {
    /// Evaluates split operations for INTT polynomial decomposition.
    ///
    /// This function performs the split operations that decompose INTT results from larger
    /// polynomials into smaller subproblems for recursive computation. The split process uses
    /// inverse roots of unity and scaling factors to properly decompose coefficients.
    ///
    /// The evaluation process:
    /// 1. Evaluates each split operation in sequence
    /// 2. Performs addition and scaling for the first polynomial (f0)
    /// 3. Performs subtraction, scaling, and inverse root multiplication for the second polynomial (f1)
    /// 4. Returns two smaller polynomials for recursive INTT computation
    ///
    /// # Arguments
    ///
    /// * `lookup_elements` - Lookup table elements for modular arithmetic operations and range checking
    /// * `eval` - Evaluation context for constraint framework operations
    ///
    /// # Returns
    ///
    /// Returns a tuple containing two vectors of polynomial coefficients:
    /// - `f0`: Coefficients for the first smaller polynomial
    /// - `f1`: Coefficients for the second smaller polynomial
    pub fn evaluate(self, lookup_elements: &RCLookupElements, eval: &mut E) -> [E::F; 2] {
        // Perform split butterfly operations on each pair of coefficients
        let f = [
            self.i2_times_f_even_plus_f_odd.r.clone(),
            self.i2_times_f_even_minus_f_odd_times_root_inv.r.clone(),
        ];

        // Step 1: Add even and odd coefficients and scale by I2
        AddMod::evaluate(self.f_even_plus_f_odd, lookup_elements, eval);

        MulMod::evaluate(self.i2_times_f_even_plus_f_odd, lookup_elements, eval);

        // Step 2: Subtract odd from even coefficients, scale by I2, and multiply by inverse root
        SubMod::evaluate(self.f_even_minus_f_odd, lookup_elements, eval);
        MulMod::evaluate(self.i2_times_f_even_minus_f_odd, lookup_elements, eval);

        MulMod::evaluate(
            self.i2_times_f_even_minus_f_odd_times_root_inv,
            lookup_elements,
            eval,
        );

        f
    }
}
