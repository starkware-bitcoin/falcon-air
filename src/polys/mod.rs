//! # Polynomial Operations Module
//!
//! This module provides STARK proof components for fundamental polynomial operations
//! over the finite field Z_q where q = 12289. These operations are essential building
//! blocks for cryptographic applications including the Falcon signature scheme.
//!
//! # Overview
//!
//! The polys module implements efficient polynomial operations with modular arithmetic
//! and range checking to ensure all computations remain within field bounds. Each
//! operation is decomposed into quotient and remainder parts for efficient verification.
//!
//! # Mathematical Foundation
//!
//! All operations are performed in the finite field Z_q where q = 12289. This field
//! size is chosen to be compatible with the Falcon signature scheme requirements.
//! Each arithmetic operation is decomposed as:
//!
//! - **Multiplication**: a * b = quotient * q + remainder, where remainder ∈ [0, q)
//!   (operates on polynomial evaluations)
//! - **Subtraction**: a - b = borrow * q + remainder, where remainder ∈ [0, q) and borrow ∈ {0, 1}
//!   (operates on polynomial coefficients)
//! - **Euclidean Norm**: ||s||² = Σᵢ(sᵢ²), computed as regular integer arithmetic
//!   (operates on polynomial coefficients, checks against predefined bounds)
//!
//! # Modules
//!
//! - [`mul`]: Modular multiplication operations for polynomial evaluations
//! - [`sub`]: Modular subtraction operations for polynomial coefficients
//! - [`euclidean_norm`]: Euclidean norm computation for signature verification
//!
//! # Key Features
//!
//! - **Modular Arithmetic**: All operations use modular arithmetic with field size q = 12289
//! - **Range Checking**: Comprehensive range checking ensures values remain within appropriate bounds
//! - **STARK Proofs**: Each operation generates STARK proofs for cryptographic verification
//! - **Efficient Implementation**: Optimized for polynomial sizes up to 1024 coefficients
//! - **Lookup Protocols**: Uses lookup tables for efficient range checking and verification
//!
//! # Usage
//!
//! These polynomial operations are used in the Falcon signature scheme for:
//! - Polynomial multiplication in NTT domain (evaluation form)
//! - Coefficient-wise arithmetic operations (coefficient form)
//! - Signature verification through Euclidean norm computation
//! - Range checking and modular arithmetic verification
//!
//! # Field Parameters
//!
//! - Field size: q = 12289 (12 * 1024 + 1) for modular operations
//! - Polynomial sizes: Up to 1024 coefficients
//! - Arithmetic: Modular arithmetic for mul/sub, regular arithmetic for Euclidean norm
//! - Security: Compatible with Falcon signature scheme requirements

pub mod euclidean_norm;
pub mod mul;
pub mod sub;
