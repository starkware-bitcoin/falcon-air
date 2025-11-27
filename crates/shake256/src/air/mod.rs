mod chi_8_8_8;
mod keccak;
mod keccak_round;
mod rc_7_7_7;
mod shake256;
mod xor_8_8;
mod xor_8_8_8;

use stwo_constraint_framework::TraceLocationAllocator;
use stwo_prover::core::air::{Component as ComponentVerifier, ComponentProver};
use stwo_prover::core::backend::simd::SimdBackend;

use crate::interaction::{InteractionClaim, InteractionElements};
use crate::trace::Claim;

pub struct Components {
    pub shake256: shake256::Component,
    pub keccak: keccak::Component,
    pub keccak_round: keccak_round::Component,
    pub xor_8_8_8: xor_8_8_8::Component,
    pub rc_7_7_7: rc_7_7_7::Component,
    pub chi_8_8_8: chi_8_8_8::Component,
    pub xor_8_8: xor_8_8::Component,
}

impl Components {
    pub fn new(
        location_allocator: &mut TraceLocationAllocator,
        claim: &Claim,
        interaction_claim: &InteractionClaim,
        interaction_elements: &InteractionElements,
    ) -> Self {
        Self {
            shake256: shake256::Component::new(
                location_allocator,
                shake256::Eval {
                    claim: claim.shake256.clone(),
                    interaction_elements: interaction_elements.clone(),
                },
                interaction_claim.shake256.claimed_sum,
            ),
            keccak: keccak::Component::new(
                location_allocator,
                keccak::Eval {
                    claim: claim.keccak.clone(),
                    interaction_elements: interaction_elements.clone(),
                },
                interaction_claim.keccak.claimed_sum,
            ),
            keccak_round: keccak_round::Component::new(
                location_allocator,
                keccak_round::Eval {
                    claim: claim.keccak_round.clone(),
                    interaction_elements: interaction_elements.clone(),
                },
                interaction_claim.keccak_round.claimed_sum,
            ),
            xor_8_8_8: xor_8_8_8::Component::new(
                location_allocator,
                xor_8_8_8::Eval {
                    claim: claim.xor_8_8_8.clone(),
                    interaction_elements: interaction_elements.clone(),
                },
                interaction_claim.xor_8_8_8.claimed_sum,
            ),
            chi_8_8_8: chi_8_8_8::Component::new(
                location_allocator,
                chi_8_8_8::Eval {
                    claim: claim.chi_8_8_8.clone(),
                    interaction_elements: interaction_elements.clone(),
                },
                interaction_claim.chi_8_8_8.claimed_sum,
            ),
            xor_8_8: xor_8_8::Component::new(
                location_allocator,
                xor_8_8::Eval {
                    claim: claim.xor_8_8.clone(),
                    interaction_elements: interaction_elements.clone(),
                },
                interaction_claim.xor_8_8.claimed_sum,
            ),
            rc_7_7_7: rc_7_7_7::Component::new(
                location_allocator,
                rc_7_7_7::Eval {
                    claim: claim.rc_7_7_7.clone(),
                    interaction_elements: interaction_elements.clone(),
                },
                interaction_claim.rc_7_7_7.claimed_sum,
            ),
        }
    }

    pub fn provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            &self.shake256,
            &self.keccak,
            &self.keccak_round,
            &self.xor_8_8_8,
            &self.chi_8_8_8,
            &self.xor_8_8,
            &self.rc_7_7_7,
        ]
    }

    pub fn verifiers(&self) -> Vec<&dyn ComponentVerifier> {
        vec![
            &self.shake256,
            &self.keccak,
            &self.keccak_round,
            &self.xor_8_8_8,
            &self.chi_8_8_8,
            &self.xor_8_8,
            &self.rc_7_7_7,
        ]
    }
}
