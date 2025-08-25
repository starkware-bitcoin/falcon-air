//! # Number Theoretic Transform (NTT) Components
//!
//! This module provides implementations for polynomial evaluation and interpolation
//! using Number Theoretic Transforms over the finite field Z_q where q = 12289.
//!
//! The NTT is a generalization of the Fast Fourier Transform (FFT) that works over
//! finite fields. It provides efficient algorithms for converting polynomials between
//! coefficient form and evaluation form, which is essential for many cryptographic
//! applications including the Falcon signature scheme.
//!
//! # Mathematical Foundation
//!
//! The NTT transforms a polynomial f(x) = Σᵢ₌₀ⁿ⁻¹ aᵢxⁱ from coefficient form to
//! evaluation form by computing f(ωⁱ) for i = 0, 1, ..., n-1, where ω is a primitive
//! n-th root of unity in Z_q.
//!
//! # Algorithm Overview
//!
//! - **NTT (Forward)**: Converts polynomial from coefficient form to evaluation form
//! - **INTT (Inverse)**: Converts polynomial from evaluation form back to coefficient form
//!
//! Both transforms use the Cooley-Tukey butterfly pattern with precomputed roots of unity
//! for efficient computation.
//!
//! ## Modules
//!
//! - [`ntt`]: Forward NTT implementation (coefficient → evaluation form)
//! - [`intt`]: Inverse NTT implementation (evaluation → coefficient form)  
//! - [`roots`]: Precomputed roots of unity for all polynomial sizes
//!
//! ## Key Constants
//!
//! - `ROOTS`: Precomputed roots of unity for sizes 2, 4, 8, ..., 1024
//! - `SQ1`: Square root of 1 in the field Z_q
//! - `I2`: Modular inverse of 2 (6145) used as scaling factor for INTT
//!
//! # Field Parameters
//!
//! - Field size: q = 12289 (12 * 1024 + 1)
//! - Polynomial sizes: 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024
//! - Primitive root: g = 7 (generator of Z_q*)
//!
//! # Usage
//!
//! The NTT components are used in the Falcon signature scheme for efficient
//! polynomial multiplication and evaluation. They provide O(n log n) complexity
//! for polynomial operations over the finite field Z_q.

use crate::{ntts::roots::*, zq::inverses::INVERSES_MOD_Q};

pub mod intt;
pub mod ntt;
pub mod roots;

/// Precomputed roots of unity for all polynomial sizes used in NTT operations.
///
/// This array contains roots of unity for polynomial sizes 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024.
/// Each subarray contains the roots needed for one level of the NTT computation.
/// The roots are computed as powers of the primitive root g = 7 in the field Z_q.
pub const ROOTS: [&[u32]; 10] = [
    ROOTS_2, ROOTS_4, ROOTS_8, ROOTS_16, ROOTS_32, ROOTS_64, ROOTS_128, ROOTS_256, ROOTS_512,
    ROOTS_1024,
];

/// Square root of 1 in the field Z_q.
pub const SQ1: u32 = ROOTS_2[0];

/// Modular inverse of 2 in the field Z_q.
///
/// This constant (value: 6145) is used as a scaling factor in the inverse NTT (INTT)
/// to normalize the polynomial coefficients after the transform.
pub const I2: u32 = INVERSES_MOD_Q[2];
