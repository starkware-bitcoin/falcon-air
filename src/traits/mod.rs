use stwo::{
    core::fields::m31::M31,
    prover::{
        backend::simd::{SimdBackend, m31::PackedM31, qm31::PackedQM31},
        poly::{BitReversedOrder, circle::CircleEvaluation},
    },
};
use stwo_constraint_framework::Relation;

use crate::traits::{
    components::Component,
    preprocessed::{
        DrawRelation, PreprocessedColumn, PreprocessedColumnClaim, PreprocessedLookupElements,
    },
};

pub mod components;
pub mod preprocessed;

pub struct Prover {
    pub components: Vec<Box<dyn Component>>,
    pub preprocessed_columns: Vec<Box<dyn PreprocessedColumn>>,
}

impl Prover {
    pub fn new(
        components: Vec<Box<dyn Component>>,
        preprocessed_columns: Vec<Box<dyn PreprocessedColumn>>,
    ) -> Self {
        Self {
            components,
            preprocessed_columns,
        }
    }
    pub fn gen_preprocessed_columns(
        &self,
    ) -> Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>> {
        self.preprocessed_columns
            .iter()
            .map(|col| col.gen_column_simd())
            .collect()
    }
    pub fn gen_traces(&self) -> Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>> {
        self.components
            .iter()
            .map(|comp| comp.gen_trace())
            .collect()
    }
    pub fn draw_relations(&self) -> Vec<PreprocessedLookupElements> {
        self.preprocessed_columns
            .iter()
            .map(|col| col.draw())
            .collect()
    }

    pub fn gen_interaction_trace(
        &self,
    ) -> Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>> {
        self.components
            .iter()
            .map(|comp| comp.gen_interaction_trace())
            .chain(
                self.preprocessed_columns
                    .iter()
                    .map(|preprocessed| preprocessed.gen_interaction_trace()),
            )
            .collect()
    }
}
