use crate::{constants::N_SQUEEZING, utils::Enabler};
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
                .shake256
                .non_padded_length
                .next_power_of_two()
                .ilog2() as u32,
            LOG_N_LANES,
        );
        let mut interaction_trace = LogupTraceGenerator::new(log_size);
        let enabler_col = Enabler::new(interaction_claim_data.shake256.non_padded_length);

        macro_rules! interaction_trace_macro {
            (@sgn +, $e:expr) => { $e };
            (@sgn -, $e:expr) => { -$e };

            ($relation_name_1:ident, $i_1:expr, $s0:tt, $relation_name_2:ident, $i_2:expr, $s1:tt) => {{
                let mut col = interaction_trace.new_col();
                (
                    col.par_iter_mut(),
                    &interaction_claim_data.shake256.lookup_data.$relation_name_1[$i_1],
                    &interaction_claim_data.shake256.lookup_data.$relation_name_2[$i_2],
                )
                    .into_par_iter()
                    .enumerate()
                    .for_each(|(i, (writer, value0, value1))| {
                        let enabler: PackedQM31 = PackedQM31::from(enabler_col.packed_at(i));
                        let denom0: PackedQM31 =
                            interaction_elements.$relation_name_1.combine(value0);
                        let denom1: PackedQM31 =
                            interaction_elements.$relation_name_2.combine(value1);
                        let numerator = interaction_trace_macro!(@sgn $s0, denom1)
                            + interaction_trace_macro!(@sgn $s1, denom0);
                        let denom = denom0 * denom1;

                        writer.write_frac(enabler * numerator, denom);
                    });
                col.finalize_col();
            }};
        }

        // Generate the interaction trace
        interaction_trace_macro!(shake256, 0, -, keccak, 0, +);
        for i in 0..(N_SQUEEZING - 1) {
            interaction_trace_macro!(keccak, 2*i + 1, -, keccak, 2*i + 2, +);
        }
        interaction_trace_macro!(keccak, 2*N_SQUEEZING - 1, -, shake256, 1, +);

        let (trace, claimed_sum) = interaction_trace.finalize_last();
        let interaction_claim = Self { claimed_sum };
        (interaction_claim, trace)
    }
}
