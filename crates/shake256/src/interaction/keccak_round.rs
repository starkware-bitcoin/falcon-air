use crate::{
    trace::keccak_round::{
        N_CHI_8_8_8_LOOKUPS, N_RC_7_7_7_LOOKUPS_1, N_RC_7_7_7_LOOKUPS_2, N_XOR_8_8_8_LOOKUPS,
        N_XOR_8_8_LOOKUPS1, N_XOR_8_8_LOOKUPS2,
    },
    utils::Enabler,
};
use num_traits::One;
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};
use serde::{Deserialize, Serialize};
use stwo_constraint_framework::{logup::LogupTraceGenerator, Relation};
use stwo_prover::core::{
    backend::simd::{m31::LOG_N_LANES, qm31::PackedQM31, SimdBackend},
    channel::Channel,
    fields::{m31::BaseField, qm31::SecureField},
    poly::{circle::CircleEvaluation, BitReversedOrder},
};

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct InteractionClaim {
    pub claimed_sum: SecureField,
}

impl InteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }

    pub fn generate_interaction_trace(
        interaction_elements: &crate::interaction::InteractionElements,
        interaction_claim_data: &crate::interaction::InteractionClaimData,
    ) -> (
        Self,
        impl IntoIterator<Item = CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    ) {
        let log_size = std::cmp::max(
            interaction_claim_data
                .keccak_round
                .non_padded_length
                .next_power_of_two()
                .ilog2() as u32,
            LOG_N_LANES,
        );
        let mut interaction_trace = LogupTraceGenerator::new(log_size);
        let enabler_col = Enabler::new(interaction_claim_data.keccak_round.non_padded_length);

        macro_rules! interaction_trace_macro {
            // Sign helper
            (@sgn +, $e:expr) => { $e };
            (@sgn -, $e:expr) => { -$e };
            // Factor helper: 'e' -> enabler, '1' -> one
            (@fac e, $en:expr, $one:expr) => { $en };
            (@fac 1, $en:expr, $one:expr) => { $one };

            // Main rule: pass sign and factor per side
            // usage: (rel1, idx1, +, e, rel2, idx2, -, 1)
            ($relation_name_1:ident, $i_1:expr, $s0:tt, $f0:tt,
             $relation_name_2:ident, $i_2:expr, $s1:tt, $f1:tt) => {{
                let mut col = interaction_trace.new_col();
                (
                    col.par_iter_mut(),
                    &interaction_claim_data.keccak_round.lookup_data.$relation_name_1[$i_1],
                    &interaction_claim_data.keccak_round.lookup_data.$relation_name_2[$i_2],
                )
                    .into_par_iter()
                    .enumerate()
                    .for_each(|(i, (writer, value0, value1))| {
                        let _enabler: PackedQM31 = PackedQM31::from(enabler_col.packed_at(i));
                        let _one: PackedQM31 = PackedQM31::one();
                        let denom0: PackedQM31 = interaction_elements.$relation_name_1.combine(value0);
                        let denom1: PackedQM31 = interaction_elements.$relation_name_2.combine(value1);

                        let f0 = interaction_trace_macro!(@fac $f0, _enabler, _one);
                        let f1 = interaction_trace_macro!(@fac $f1, _enabler, _one);

                        let numerator = interaction_trace_macro!(@sgn $s0, denom1 * f0)
                            + interaction_trace_macro!(@sgn $s1, denom0 * f1);
                        let denom = denom0 * denom1;

                        writer.write_frac(numerator, denom);
                    });
                col.finalize_col();
            }};
        }

        // Generate the interaction trace
        interaction_trace_macro!(keccak_round, 0, -, e, xor_8_8_8, 0, +, 1);

        // XOR_8_8_8
        for j in 0..N_XOR_8_8_8_LOOKUPS / 2 - 1 {
            interaction_trace_macro!(
                xor_8_8_8,
                1 + 2 * j,
                +, 1,
                xor_8_8_8,
                1 + 2 * j + 1,
                +, 1
            );
        }
        interaction_trace_macro!(
            xor_8_8_8,
            N_XOR_8_8_8_LOOKUPS - 1,
            +, 1,
            rc_7_7_7,
            0,
            +, 1
        );

        // RC_7_7_7_1 (odd !)
        for j in 0..N_RC_7_7_7_LOOKUPS_1 / 2 {
            interaction_trace_macro!(
                rc_7_7_7,
                1 + 2 * j,
                +, 1,
                rc_7_7_7,
                1 + 2 * j + 1,
                +, 1
            );
        }

        // XOR_8_8_1
        for j in 0..N_XOR_8_8_LOOKUPS1 / 2 {
            interaction_trace_macro!(
                xor_8_8,
                2 * j,
                +, 1,
                xor_8_8,
                2 * j + 1,
                +, 1
            );
        }

        // RC_7_7_7_2
        for j in 0..N_RC_7_7_7_LOOKUPS_2 / 2 {
            interaction_trace_macro!(
                rc_7_7_7,
                N_RC_7_7_7_LOOKUPS_1 + 2 * j,
                +, 1,
                rc_7_7_7,
                N_RC_7_7_7_LOOKUPS_1 + 2 * j + 1,
                +, 1
            );
        }

        // CHI_8_8_8
        for j in 0..N_CHI_8_8_8_LOOKUPS / 2 {
            interaction_trace_macro!(
                chi_8_8_8,
                2 * j,
                +, 1,
                chi_8_8_8,
                2 * j + 1,
                +, 1
            );
        }

        // XOR_8_8
        for j in 0..N_XOR_8_8_LOOKUPS2 / 2 {
            interaction_trace_macro!(
                xor_8_8,
                N_XOR_8_8_LOOKUPS1 + 2 * j,
                +, 1,
                xor_8_8,
                N_XOR_8_8_LOOKUPS1 + 2 * j + 1,
                +, 1
            );
        }

        let mut col = interaction_trace.new_col();
        (
            col.par_iter_mut(),
            &interaction_claim_data.keccak_round.lookup_data.keccak_round[1],
        )
            .into_par_iter()
            .enumerate()
            .for_each(|(i, (writer, value0))| {
                let num: PackedQM31 = PackedQM31::from(enabler_col.packed_at(i));
                let denom: PackedQM31 = interaction_elements.keccak_round.combine(value0);

                writer.write_frac(num, denom);
            });
        col.finalize_col();

        let (trace, claimed_sum) = interaction_trace.finalize_last();
        let interaction_claim = Self { claimed_sum };
        (interaction_claim, trace)
    }
}
