//! # Falcon-AIR
//!
//! A STARK proof system implementation for modular arithmetic operations in the field Z_q
//! where q = 12 * 1024 + 1 = 12289.
//!
//! This crate provides components for:
//! - Modular addition (a + b mod q)
//! - Modular multiplication (a * b mod q)
//! - Modular subtraction (a - b mod q)
//! - Range checking (ensuring values are in [0, q))
//!
//! The implementation uses the STWO framework for generating STARK proofs with
//! efficient constraint evaluation and polynomial commitment schemes.

pub mod big_air;
pub mod debug;
pub mod ntts;
pub mod relation_tracker;
pub mod zq;

pub const POLY_LOG_SIZE: u32 = 5;
pub const POLY_SIZE: usize = 1 << POLY_LOG_SIZE;
