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
