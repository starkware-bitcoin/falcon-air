use stwo_constraint_framework::{
    preprocessed_columns::PreProcessedColumnId, EvalAtRow, FrameworkComponent, FrameworkEval,
    RelationEntry,
};

use crate::trace::rc_7_7_7::Claim;

#[derive(Clone)]
pub struct Eval {
    pub claim: Claim,
    pub interaction_elements: crate::interaction::InteractionElements,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let a = eval.get_preprocessed_column(PreProcessedColumnId {
            id: "rc_7_7_7_a".to_string(),
        });
        let b = eval.get_preprocessed_column(PreProcessedColumnId {
            id: "rc_7_7_7_b".to_string(),
        });
        let c = eval.get_preprocessed_column(PreProcessedColumnId {
            id: "rc_7_7_7_c".to_string(),
        });
        let multiplicity = eval.next_trace_mask();

        eval.add_to_relation(RelationEntry::new(
            &self.interaction_elements.rc_7_7_7,
            -E::EF::from(multiplicity),
            &[a, b, c],
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type Component = FrameworkComponent<Eval>;
