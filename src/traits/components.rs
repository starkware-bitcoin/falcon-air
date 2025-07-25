use stwo::{
    core::fields::m31::M31,
    prover::{
        backend::simd::SimdBackend,
        poly::{BitReversedOrder, circle::CircleEvaluation},
    },
};

pub trait Component {
    fn gen_trace(&self) -> CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
    fn gen_interaction_trace(&self) -> CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
}
