use num_traits::Zero;
use stwo::{
    core::{
        ColumnVec,
        channel::Channel,
        fields::{m31::M31, qm31::QM31},
        pcs::TreeVec,
        proof::StarkProof,
        vcs::blake2_merkle::Blake2sMerkleHasher,
    },
    prover::{
        ProvingError,
        backend::simd::SimdBackend,
        poly::{BitReversedOrder, circle::CircleEvaluation},
    },
};
use stwo::{
    core::{
        channel::Blake2sChannel, pcs::PcsConfig, poly::circle::CanonicCoset,
        proof_of_work::GrindOps, vcs::blake2_merkle::Blake2sMerkleChannel,
    },
    prover::{CommitmentSchemeProver, poly::circle::PolyOps, prove},
};
use stwo_constraint_framework::TraceLocationAllocator;

pub mod add;
pub mod range_check;
pub const Q: u32 = 12 * 1024 + 1;

pub struct BigClaim {
    pub add: add::Claim,
    pub range_check: range_check::Claim,
}

impl BigClaim {
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let trees = vec![self.add.log_sizes(), self.range_check.log_sizes()];
        TreeVec::concat_cols(trees.into_iter())
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.add.mix_into(channel);
        self.range_check.mix_into(channel);
    }

    pub fn gen_trace(
        &self,
    ) -> (
        Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        (
            Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
            Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        ),
    ) {
        let (add_trace, remainders) = self.add.gen_trace();
        let range_check_trace = self.range_check.gen_trace(&remainders);
        (
            add_trace
                .clone()
                .into_iter()
                .chain(range_check_trace.clone())
                .collect::<Vec<_>>(),
            (add_trace, range_check_trace),
        )
    }
}

pub struct BigInteractionClaim {
    pub add: add::InteractionClaim,
    pub range_check: range_check::InteractionClaim,
}

impl BigInteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.add.mix_into(channel);
        self.range_check.mix_into(channel);
    }
    pub fn claimed_sum(&self) -> QM31 {
        self.add.claimed_sum + self.range_check.claimed_sum
    }
    pub fn gen_interaction_trace(
        lookup_elements: &range_check::LookupElements,
        add_trace: &ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        range_check_trace: &ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    ) -> (
        Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Self,
    ) {
        let (add_interaction_trace, add_interaction_claim) =
            add::InteractionClaim::gen_interaction_trace(add_trace, lookup_elements);
        let (range_check_interaction_trace, range_check_interaction_claim) =
            range_check::InteractionClaim::gen_interaction_trace(
                range_check_trace,
                lookup_elements,
            );
        (
            add_interaction_trace
                .into_iter()
                .chain(range_check_interaction_trace)
                .collect(),
            Self {
                add: add_interaction_claim,
                range_check: range_check_interaction_claim,
            },
        )
    }
}

pub fn prove_falcon() -> Result<StarkProof<Blake2sMerkleHasher>, ProvingError> {
    // for now work with the same trace size everywhere
    let log_size = Q.ilog2() + 1;

    let channel = &mut Blake2sChannel::default();
    let pcs_config = PcsConfig::default();
    pcs_config.mix_into(channel);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_size + pcs_config.fri_config.log_blowup_factor + 1)
            .circle_domain()
            .half_coset,
    );

    // preprocessed columns
    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(pcs_config, &twiddles);
    let mut tree_builder = commitment_scheme.tree_builder();
    let range_check_preprocessed = range_check::RangeCheck12289::gen_column_simd();
    tree_builder.extend_evals([range_check_preprocessed]);
    // commit to the range check preprocessed column
    tree_builder.commit(channel);

    let claim = BigClaim {
        add: add::Claim { log_size },
        range_check: range_check::Claim { log_size },
    };
    let (trace, traces) = claim.gen_trace();
    claim.mix_into(channel);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace.clone());
    tree_builder.commit(channel);

    let interaction_pow = SimdBackend::grind(channel, 2);
    channel.mix_u64(interaction_pow);

    let relations = range_check::LookupElements::draw(channel);

    let (interaction_trace, interaction_claim) =
        BigInteractionClaim::gen_interaction_trace(&relations, &traces.0, &traces.1);
    interaction_claim.mix_into(channel);
    assert_eq!(
        interaction_claim.claimed_sum(),
        QM31::zero(),
        "invalid logup sum"
    );

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction_trace);
    tree_builder.commit(channel);

    let mut tree_span_provider = TraceLocationAllocator::new_with_preproccessed_columns(&[
        range_check::RangeCheck12289::id(),
    ]);

    prove::<SimdBackend, _>(
        &[
            &add::Component::new(
                &mut tree_span_provider,
                add::Eval {
                    claim: add::Claim { log_size },
                    lookup_elements: relations.clone(),
                },
                interaction_claim.add.claimed_sum,
            ),
            &range_check::Component::new(
                &mut tree_span_provider,
                range_check::Eval {
                    claim: range_check::Claim { log_size },
                    lookup_elements: relations.clone(),
                },
                interaction_claim.range_check.claimed_sum,
            ),
        ],
        channel,
        commitment_scheme,
    )
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_prove_falcon() {
        assert!(prove_falcon().is_ok());
    }
}
