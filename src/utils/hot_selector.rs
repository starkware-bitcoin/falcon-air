use stwo::{
    core::{fields::m31::M31, poly::circle::CanonicCoset, utils::bit_reverse_index},
    prover::backend::simd::{SimdBackend, column::BaseColumn},
    prover::poly::{BitReversedOrder, circle::CircleEvaluation},
};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

pub struct HotSelector;

impl HotSelector {
    pub fn id() -> PreProcessedColumnId {
        PreProcessedColumnId {
            id: "hot_selector".into(),
        }
    }

    pub fn gen_column_simd(log_size: u32) -> CircleEvaluation<SimdBackend, M31, BitReversedOrder> {
        let domain = CanonicCoset::new(log_size).circle_domain();
        let mut col = vec![M31::from_u32_unchecked(0); 1 << log_size];
        let hot = bit_reverse_index(0, log_size);
        col[hot] = M31::from_u32_unchecked(1);
        CircleEvaluation::new(domain, BaseColumn::from_iter(col))
    }
}
