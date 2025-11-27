mod chi_8_8_8;
mod keccak;
mod keccak_round;
mod rc_7_7_7;
pub mod relations;
mod shake256;
mod xor_8_8;
mod xor_8_8_8;

use serde::{Deserialize, Serialize};
use stwo_prover::core::{
    backend::simd::SimdBackend,
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    poly::{circle::CircleEvaluation, BitReversedOrder},
};

use crate::{
    trace::{
        chi_8_8_8 as chi_8_8_8_trace, keccak as keccak_trace, keccak_round as keccak_round_trace,
        rc_7_7_7 as rc_7_7_7_trace, shake256 as shake256_trace, xor_8_8 as xor_8_8_trace,
        xor_8_8_8 as xor_8_8_8_trace,
    },
    PublicData,
};

pub struct InteractionClaimData {
    pub shake256: shake256_trace::InteractionClaimData,
    pub keccak: keccak_trace::InteractionClaimData,
    pub keccak_round: keccak_round_trace::InteractionClaimData,
    pub xor_8_8_8: xor_8_8_8_trace::InteractionClaimData,
    pub chi_8_8_8: chi_8_8_8_trace::InteractionClaimData,
    pub xor_8_8: xor_8_8_trace::InteractionClaimData,
    pub rc_7_7_7: rc_7_7_7_trace::InteractionClaimData,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct InteractionClaim {
    pub shake256: shake256::InteractionClaim,
    pub keccak: keccak::InteractionClaim,
    pub keccak_round: keccak_round::InteractionClaim,
    pub xor_8_8_8: xor_8_8_8::InteractionClaim,
    pub chi_8_8_8: chi_8_8_8::InteractionClaim,
    pub xor_8_8: xor_8_8::InteractionClaim,
    pub rc_7_7_7: rc_7_7_7::InteractionClaim,
}

#[derive(Debug, Clone)]
pub struct InteractionElements {
    pub shake256: relations::Shake256,
    pub keccak: relations::Keccak,
    pub keccak_round: relations::KeccakRound,
    pub xor_8_8_8: relations::Xor_8_8_8,
    pub chi_8_8_8: relations::Chi_8_8_8,
    pub xor_8_8: relations::Xor_8_8,
    pub rc_7_7_7: relations::rc_7_7_7,
}

impl InteractionElements {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            shake256: relations::Shake256::draw(channel),
            keccak: relations::Keccak::draw(channel),
            keccak_round: relations::KeccakRound::draw(channel),
            xor_8_8_8: relations::Xor_8_8_8::draw(channel),
            chi_8_8_8: relations::Chi_8_8_8::draw(channel),
            xor_8_8: relations::Xor_8_8::draw(channel),
            rc_7_7_7: relations::rc_7_7_7::draw(channel),
        }
    }
}

impl InteractionClaim {
    pub fn generate_interaction_trace(
        interaction_elements: &InteractionElements,
        interaction_claim_data: &InteractionClaimData,
    ) -> (
        Self,
        impl IntoIterator<Item = CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    ) {
        let (shake256_interaction_claim, shake256_trace) =
            shake256::InteractionClaim::generate_interaction_trace(
                &interaction_elements,
                interaction_claim_data,
            );
        let (keccak_interaction_claim, keccak_trace) =
            keccak::InteractionClaim::generate_interaction_trace(
                &interaction_elements,
                interaction_claim_data,
            );
        let (keccak_round_interaction_claim, keccak_round_trace) =
            keccak_round::InteractionClaim::generate_interaction_trace(
                &interaction_elements,
                interaction_claim_data,
            );
        let (xor_8_8_8_interaction_claim, xor_8_8_8_trace) =
            xor_8_8_8::InteractionClaim::generate_interaction_trace(
                &interaction_elements,
                interaction_claim_data,
            );
        let (chi_8_8_8_interaction_claim, chi_8_8_8_trace) =
            chi_8_8_8::InteractionClaim::generate_interaction_trace(
                &interaction_elements,
                interaction_claim_data,
            );
        let (xor_8_8_interaction_claim, xor_8_8_trace) =
            xor_8_8::InteractionClaim::generate_interaction_trace(
                &interaction_elements,
                interaction_claim_data,
            );
        let (rc_7_7_7_interaction_claim, rc_7_7_7_trace) =
            rc_7_7_7::InteractionClaim::generate_interaction_trace(
                &interaction_elements,
                interaction_claim_data,
            );

        let trace = shake256_trace
            .into_iter()
            .chain(keccak_trace)
            .chain(keccak_round_trace)
            .chain(xor_8_8_8_trace)
            .chain(chi_8_8_8_trace)
            .chain(xor_8_8_trace)
            .chain(rc_7_7_7_trace)
            .collect::<Vec<_>>();

        (
            Self {
                shake256: shake256_interaction_claim,
                keccak: keccak_interaction_claim,
                keccak_round: keccak_round_interaction_claim,
                xor_8_8_8: xor_8_8_8_interaction_claim,
                chi_8_8_8: chi_8_8_8_interaction_claim,
                xor_8_8: xor_8_8_interaction_claim,
                rc_7_7_7: rc_7_7_7_interaction_claim,
            },
            trace,
        )
    }

    pub fn claimed_sum(
        &self,
        interaction_elements: &InteractionElements,
        public_data: PublicData,
    ) -> SecureField {
        let mut sum = public_data.initial_logup_sum(interaction_elements);
        sum += self.shake256.claimed_sum;
        sum += self.keccak.claimed_sum;
        sum += self.keccak_round.claimed_sum;
        sum += self.xor_8_8_8.claimed_sum;
        sum += self.chi_8_8_8.claimed_sum;
        sum += self.xor_8_8.claimed_sum;
        sum += self.rc_7_7_7.claimed_sum;
        sum
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.shake256.mix_into(channel);
        self.keccak.mix_into(channel);
        self.keccak_round.mix_into(channel);
        self.xor_8_8_8.mix_into(channel);
        self.chi_8_8_8.mix_into(channel);
        self.xor_8_8.mix_into(channel);
        self.rc_7_7_7.mix_into(channel);
    }
}
