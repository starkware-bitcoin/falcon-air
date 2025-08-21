//! # Number Theoretic Transform (NTT) Components
//!
//! This module provides implementations for polynomial evaluation and interpolation
//! using Number Theoretic Transforms over the finite field Z_q where q = 12289.
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
//! - `SQ1`: First root of unity (used in initial butterfly operations)
//! - `I2`: Modular inverse of 2 (scaling factor for INTT)

use crate::{ntts::roots::*, zq::inverses::INVERSES_MOD_Q};

pub mod intt;
pub mod ntt;
pub mod roots;

pub const ROOTS: [&[u32]; 10] = [
    ROOTS_2, ROOTS_4, ROOTS_8, ROOTS_16, ROOTS_32, ROOTS_64, ROOTS_128, ROOTS_256, ROOTS_512,
    ROOTS_1024,
];
pub const SQ1: u32 = ROOTS_2[0];
pub const I2: u32 = INVERSES_MOD_Q[2];
