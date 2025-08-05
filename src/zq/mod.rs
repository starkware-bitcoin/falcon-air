//! # Z_q Field Operations
//!
//! This module implements STARK proof components for arithmetic operations in the field Z_q
//! where q = 12 * 1024 + 1 = 12289.
//!
//! The field size q is chosen to be compatible with the Falcon signature scheme requirements.
//! All arithmetic operations are performed modulo q, and range checking ensures values
//! remain within the valid range [0, q).

pub mod add;
pub mod inverses;
pub mod mul;
pub mod range_check;
pub mod sub;

/// The field size for Z_q arithmetic operations.
///
/// This value (12 * 1024 + 1 = 12289) is chosen to be compatible with
/// the Falcon signature scheme requirements.
pub const Q: u32 = 12 * 1024 + 1;

pub enum Operation<E: stwo_constraint_framework::EvalAtRow> {
    Add(add::AddMod<E>),
    Sub(sub::SubMod<E>),
    Mul(mul::MulMod<E>),
}
