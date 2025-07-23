pub mod add;
pub mod range_check;
pub const Q: u32 = 12 * 1024 + 1;

#[cfg(test)]
mod tests {
    use stwo::{
        core::{
            channel::{Blake2sChannel, Channel},
            fields::qm31::SecureField,
            pcs::PcsConfig,
            poly::circle::CanonicCoset,
            proof_of_work::GrindOps,
            vcs::blake2_merkle::Blake2sMerkleChannel,
        },
        prover::{
            CommitmentSchemeProver, backend::simd::SimdBackend, poly::circle::PolyOps, prove,
        },
    };
    use stwo_constraint_framework::TraceLocationAllocator;

    use super::*;

    #[test]
    fn test_add() {
        let log_size = Q.ilog2() + 1;
        let channel = &mut Blake2sChannel::default();
        let pcs_config = PcsConfig::default();
        pcs_config.mix_into(channel);
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(log_size + pcs_config.fri_config.log_blowup_factor + 1)
                .circle_domain()
                .half_coset,
        );
        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(pcs_config, &twiddles);
        let mut tree_builder = commitment_scheme.tree_builder();
        let range_check_trace = range_check::RangeCheck12289::gen_column_simd();
        tree_builder.extend_evals([range_check_trace]);
        tree_builder.commit(channel);

        let add_trace = add::gen_trace(log_size);
        channel.mix_u64(log_size as u64);
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(add_trace.clone());
        tree_builder.commit(channel);

        let interaction_pow = SimdBackend::grind(channel, 2);
        channel.mix_u64(interaction_pow);

        let relations = range_check::LookupElements::draw(channel);

        let (interaction_trace, claimed_sum) = add::gen_interaction_trace(&add_trace, &relations);
        channel.mix_u64(log_size as u64);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(interaction_trace);
        tree_builder.commit(channel);

        let mut tree_span_provider = TraceLocationAllocator::new_with_preproccessed_columns(&[
            range_check::RangeCheck12289::id(),
        ]);
        let stark_proof = prove::<SimdBackend, _>(
            &[
                &add::Component::new(
                    &mut tree_span_provider,
                    add::Eval {
                        log_size,
                        lookup_elements: relations.clone(),
                    },
                    claimed_sum,
                ),
                &range_check::Component::new(
                    &mut tree_span_provider,
                    range_check::Eval {
                        log_size,
                        lookup_elements: relations,
                    },
                    SecureField::default(),
                ),
            ],
            channel,
            commitment_scheme,
        );
        println!("stark_proof: {:?}", stark_proof);
    }
}
