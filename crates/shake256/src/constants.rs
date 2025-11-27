// u64 constants
pub const N_BYTES_IN_U64: usize = 8;
pub const N_U12_IN_U64: usize = 6;

// Keccak Permutation constants
pub const N_ROUNDS: usize = 24;
pub const N_LANES_SHAKE256: usize = 25;
pub const SQRT_N_LANES_SHAKE256: usize = 5;
pub const DELIMITED_SUFFIX: u32 = 0x1F;
pub const FINAL_BIT: u32 = 0x80;

// Keccak State constants
pub const N_BYTES_IN_RATE: usize = 136;
pub const N_BYTES_IN_CAPACITY: usize = 64;
pub const N_BYTES_IN_STATE: usize = N_BYTES_IN_RATE + N_BYTES_IN_CAPACITY;

// SHAKE256 input/output constants
pub const N_BYTES_IN_MESSAGE: usize = 72;
pub const N_BYTES_IN_OUTPUT: usize = N_SQUEEZING * N_BYTES_IN_RATE;

// SHAKE256 constants
pub const N_SQUEEZING: usize = 10;
