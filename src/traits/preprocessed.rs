use stwo::{
    core::{
        ColumnVec,
        channel::Channel,
        fields::m31::{BaseField, M31},
        pcs::TreeVec,
    },
    prover::{
        backend::simd::SimdBackend,
        poly::{BitReversedOrder, circle::CircleEvaluation},
    },
};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

pub enum PreprocessedLookupElements {
    RangeCheck(crate::zq::range_check::LookupElements),
}

pub trait PreprocessedColumnInteractionClaim<L: DrawRelation> {
    fn mix_into(&self, channel: &mut impl Channel);
    fn gen_interaction_trace(
        trace: &CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
        lookup_elements: &L,
    ) -> (
        ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Self,
    );
}
pub trait DrawRelation {
    fn draw(channel: &mut impl Channel) -> PreprocessedLookupElements;
}

pub trait PreprocessedColumn {
    fn id(&self) -> PreProcessedColumnId;
    fn log_size(&self) -> u32;
    fn gen_column_simd(&self) -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>;
    fn draw(&self) -> PreprocessedLookupElements;
    fn gen_trace(&self) -> CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
    fn gen_interaction_trace(&self) -> CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
}

pub trait PreprocessedColumnClaim {
    fn log_sizes(&self) -> TreeVec<Vec<u32>>;
    fn mix_into(&self, channel: &mut impl Channel);
    fn gen_trace(
        &self,
        values_used: &[&[M31]],
    ) -> CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
}

pub struct PreprocessedColumns(Vec<Box<dyn PreprocessedColumn>>);

impl PreprocessedColumns {
    pub fn new(columns: Vec<Box<dyn PreprocessedColumn>>) -> Self {
        Self(columns)
    }
    pub fn gen_columns_simd(
        &self,
    ) -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
        self.0.iter().map(|col| col.gen_column_simd()).collect()
    }
    pub fn log_sizes(&self) -> Vec<u32> {
        self.0.iter().map(|col| col.log_size()).collect()
    }
    pub fn ids(&self) -> Vec<PreProcessedColumnId> {
        self.0.iter().map(|col| col.id()).collect()
    }
}
#[derive(Default)]
pub struct PreprocessedColumnBuilder(Vec<Box<dyn PreprocessedColumn>>);

impl PreprocessedColumnBuilder {
    pub fn new() -> Self {
        Self(vec![])
    }
    pub fn add_column(&mut self, column: Box<dyn PreprocessedColumn>) {
        self.0.push(column);
    }
}
