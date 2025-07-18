use num_traits::{One, Zero};
use stwo::{
    core::{
        fields::{
            m31::{BaseField, M31},
            qm31::SecureField,
        },
        poly::circle::CanonicCoset,
    },
    prover::{
        backend::simd::{
            SimdBackend, column::BaseColumn, m31::LOG_N_LANES, qm31::PackedSecureField,
        },
        poly::{BitReversedOrder, circle::CircleEvaluation},
    },
};
use stwo_constraint_framework::{
    EvalAtRow, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    preprocessed_columns::PreProcessedColumnId, relation,
};

use crate::zq::Q;

pub struct RangeCheck12289;

impl RangeCheck12289 {
    pub fn log_size() -> u32 {
        Q.ilog2() + 1
    }

    pub fn gen_column_simd() -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
        CircleEvaluation::new(
            CanonicCoset::new(Self::log_size()).circle_domain(),
            BaseColumn::from_iter(
                (0..Q)
                    .map(M31)
                    .chain((Q..Q.next_power_of_two()).map(|_| M31::zero())),
            ),
        )
    }

    pub fn id() -> PreProcessedColumnId {
        PreProcessedColumnId {
            id: format!("range_check_{}", Q),
        }
    }
}
relation!(LookupElements, 1);

pub struct Eval {
    range_check_id: PreProcessedColumnId,
    log_size: u32,
    lookup_elements: LookupElements,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let range_check_col = eval.get_preprocessed_column(self.range_check_id.clone());

        let lookup_col_1 = eval.next_trace_mask();
        let multiplicity_col = eval.next_trace_mask();

        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            -E::EF::from(multiplicity_col),
            &[range_check_col],
        ));

        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            E::EF::one(),
            &[lookup_col_1],
        ));

        eval.finalize_logup_batched(&vec![0, 1]);

        eval
    }
}

fn gen_logup_trace(
    log_size: u32,
    range_check_col: &BaseColumn,
    lookup_col_1: &BaseColumn,
    multiplicity_col: &BaseColumn,
    lookup_elements: &LookupElements,
) -> (
    Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    SecureField,
) {
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    let mut col_gen = logup_gen.new_col();
    for simd_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let numerator: PackedSecureField = PackedSecureField::from(multiplicity_col.data[simd_row]);
        let denom: PackedSecureField = lookup_elements.combine(&[range_check_col.data[simd_row]]);
        col_gen.write_frac(simd_row, -numerator, denom);
    }
    col_gen.finalize_col();

    let mut col_gen = logup_gen.new_col();
    for simd_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let lookup_col_1_val: PackedSecureField =
            lookup_elements.combine(&[lookup_col_1.data[simd_row]]);
        // 1 / denom1 + 1 / denom2 = (denom1 + denom2) / (denom1 * denom2)
        let numerator = PackedSecureField::one();
        let denom = lookup_col_1_val;
        col_gen.write_frac(simd_row, numerator, denom);
    }
    col_gen.finalize_col();

    logup_gen.finalize_last()
}

#[cfg(test)]
mod tests {
    use rand::Rng;
    use stwo::core::air::Component;
    use stwo::{
        core::{
            channel::{Blake2sChannel, Channel},
            pcs::{CommitmentSchemeVerifier, PcsConfig},
            vcs::blake2_merkle::Blake2sMerkleChannel,
            verifier::verify,
        },
        prover::{CommitmentSchemeProver, backend::Column, poly::circle::PolyOps, prove},
    };
    use stwo_constraint_framework::{FrameworkComponent, TraceLocationAllocator};

    use super::*;

    fn gen_trace(
        log_size: u32,
        range: u32,
    ) -> Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>> {
        // Create a table with random values
        let mut rng = rand::thread_rng();
        let mut lookup_col_1 =
            BaseColumn::from_iter((0..(1 << log_size)).map(|_| M31::from(rng.gen_range(0..range))));

        let mut multiplicity_col = BaseColumn::zeros(1 << log_size);
        lookup_col_1.as_mut_slice().iter().for_each(|value| {
            let index = value.0 as usize;
            if index < 1 << log_size {
                multiplicity_col.set(index, multiplicity_col.at(index) + M31::from(1));
            }
        });

        // Convert table to trace polynomials
        let domain = CanonicCoset::new(log_size).circle_domain();
        vec![lookup_col_1.clone(), multiplicity_col.clone()]
            .into_iter()
            .map(|col| CircleEvaluation::new(domain, col))
            .collect()
    }

    #[test]
    fn test_range_check_12289_works() {
        test_range_check(Q - 1);
    }

    #[test]
    #[should_panic(expected = "Invalid logup sum")]
    fn test_range_check_12289_fails() {
        test_range_check(2 * Q);
    }

    fn test_range_check(range: u32) {
        // ANCHOR_END: main_start
        let log_size = Q.ilog2() + 1;

        // Config for FRI and PoW
        let config = PcsConfig::default();

        // Precompute twiddles for evaluating and interpolating the trace
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(log_size + 1 + config.fri_config.log_blowup_factor)
                .circle_domain()
                .half_coset,
        );

        // Create the channel and commitment scheme
        let channel = &mut Blake2sChannel::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

        // Create and commit to the preprocessed columns
        let range_check_col = RangeCheck12289::gen_column_simd();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(vec![range_check_col.clone()]);
        tree_builder.commit(channel);

        // Commit to the size of the trace
        channel.mix_u64(log_size as u64);

        // Create and commit to the trace columns
        let trace = gen_trace(log_size, range);
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(trace.clone());
        tree_builder.commit(channel);

        // ANCHOR: logup_start
        // Draw random elements to use when creating the random linear combination of lookup values in the LogUp columns
        let lookup_elements = LookupElements::draw(channel);

        // Create and commit to the LogUp columns
        let (logup_cols, claimed_sum) = gen_logup_trace(
            log_size,
            &range_check_col,
            &trace[0],
            &trace[1],
            &lookup_elements,
        );
        // ANCHOR_END: logup_start
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(logup_cols);
        tree_builder.commit(channel);

        // Create a component
        let component = FrameworkComponent::<Eval>::new(
            &mut TraceLocationAllocator::default(),
            Eval {
                range_check_id: RangeCheck12289::id(),
                log_size,
                lookup_elements,
            },
            claimed_sum,
        );

        // Prove
        let proof = prove(&[&component], channel, commitment_scheme).unwrap();

        // ANCHOR: verify
        // Verify
        assert_eq!(claimed_sum, SecureField::zero(), "Invalid logup sum");

        let channel = &mut Blake2sChannel::default();
        let commitment_scheme = &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);
        let sizes = component.trace_log_degree_bounds();

        commitment_scheme.commit(proof.commitments[0], &sizes[0], channel);
        channel.mix_u64(log_size as u64);
        commitment_scheme.commit(proof.commitments[1], &sizes[1], channel);
        commitment_scheme.commit(proof.commitments[2], &sizes[2], channel);

        verify(&[&component], channel, commitment_scheme, proof).unwrap();
    }
}
