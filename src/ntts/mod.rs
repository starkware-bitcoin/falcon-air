use crate::ntts::roots::*;

pub mod inverses;
pub mod merge;
pub mod ntt;
pub mod roots;
pub mod split;

pub const ROOTS: [&[u32]; 10] = [
    ROOTS_2, ROOTS_4, ROOTS_8, ROOTS_16, ROOTS_32, ROOTS_64, ROOTS_128, ROOTS_256, ROOTS_512,
    ROOTS_1024,
];
