#![allow(non_camel_case_types)]
use stwo_constraint_framework::relation;

use crate::constants::{N_BYTES_IN_MESSAGE, N_BYTES_IN_OUTPUT, N_BYTES_IN_STATE, N_BYTES_IN_U64};
use crate::preprocessed::chi_8_8_8::N_TRACE_COLUMNS as CHI_8_8_8_N_TRACE_COLUMNS;
use crate::preprocessed::rc_7_7_7::N_TRACE_COLUMNS as rc_7_7_7_N_TRACE_COLUMNS;
use crate::preprocessed::xor_8_8::N_TRACE_COLUMNS as XOR_8_8_N_TRACE_COLUMNS;
use crate::preprocessed::xor_8_8_8::N_TRACE_COLUMNS as XOR_8_8_8_N_TRACE_COLUMNS;

pub const RELATION_SIZE_SHAKE256: usize = if N_BYTES_IN_MESSAGE > N_BYTES_IN_OUTPUT {
    N_BYTES_IN_MESSAGE
} else {
    N_BYTES_IN_OUTPUT
};
pub const RELATION_SIZE_KECCAK_ROUND: usize = N_BYTES_IN_STATE + N_BYTES_IN_U64;

relation!(Shake256, RELATION_SIZE_SHAKE256);
relation!(Keccak, N_BYTES_IN_STATE);
relation!(KeccakRound, RELATION_SIZE_KECCAK_ROUND);
relation!(Chi_8_8_8, CHI_8_8_8_N_TRACE_COLUMNS);
relation!(Xor_8_8, XOR_8_8_N_TRACE_COLUMNS);
relation!(Xor_8_8_8, XOR_8_8_8_N_TRACE_COLUMNS);
relation!(rc_7_7_7, rc_7_7_7_N_TRACE_COLUMNS);
