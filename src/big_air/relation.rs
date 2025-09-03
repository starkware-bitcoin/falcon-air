//! # Big AIR Relations
//!
//! This module defines the lookup relation structures used in the Big AIR STARK proof system.
//! It contains the various lookup elements needed for range checking, NTT operations,
//! and arithmetic operations across all proof components.
//!
//! # Components
//!
//! - **Lookup Elements**: Various lookup element types for different operations
//! - **Relation Types**: Enum types that combine related lookup elements
//! - **Relation Implementation**: Standard relation trait implementations
//!
//! This module provides the foundation for all lookup-based verification in the
//! Falcon signature scheme implementation.

use stwo::core::channel::Channel;
use stwo_constraint_framework::relation;

use crate::enum_relation;

relation!(RCLookupElements, 1);
relation!(FNTTLookupElements, 1);
relation!(GNTTLookupElements, 1);
relation!(ButterflyLookupElements, 1);
relation!(MulLookupElements, 1);
relation!(INTTLookupElements, 1);
relation!(IButterflyLookupElements, 1);
relation!(SubLookupElements, 1);
relation!(RootsLookupElements, 2);
relation!(InvRootsLookupElements, 2);

enum_relation!(
    #[derive(Debug, Clone)]
    pub enum NTTLookupElements {
        F(FNTTLookupElements),
        G(GNTTLookupElements),
    }
);
impl NTTLookupElements {
    pub fn f_draw(channel: &mut impl Channel) -> Self {
        Self::F(FNTTLookupElements::draw(channel))
    }

    pub fn g_draw(channel: &mut impl Channel) -> Self {
        Self::G(GNTTLookupElements::draw(channel))
    }
}

enum_relation!(
    #[derive(Debug, Clone)]
    pub enum INTTInputLookupElements {
        Mul(MulLookupElements),
        INTTOutput(INTTLookupElements),
    }
);

enum_relation!(
    #[derive(Debug, Clone)]
    pub enum InputLookupElements {
        NTT(NTTLookupElements),
        Butterfly(ButterflyLookupElements),
    }
);

#[derive(Debug, Clone)]
pub struct LookupElements {
    pub rc: RCLookupElements,
    pub f_ntt_butterfly: ButterflyLookupElements,
    pub f_ntt: NTTLookupElements,
    pub g_ntt_butterfly: ButterflyLookupElements,
    pub g_ntt: NTTLookupElements,
    pub mul: MulLookupElements,
    pub intt: INTTLookupElements,
    pub ibutterfly: IButterflyLookupElements,
    pub sub: SubLookupElements,
    pub half_range_check: RCLookupElements,
    pub low_sig_bound_check: RCLookupElements,
    pub high_sig_bound_check: RCLookupElements,
    pub roots: RootsLookupElements,
    pub inv_roots: InvRootsLookupElements,
}

impl LookupElements {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            rc: RCLookupElements::draw(channel),
            f_ntt_butterfly: ButterflyLookupElements::draw(channel),
            f_ntt: NTTLookupElements::f_draw(channel),
            g_ntt_butterfly: ButterflyLookupElements::draw(channel),
            g_ntt: NTTLookupElements::g_draw(channel),
            mul: MulLookupElements::draw(channel),
            intt: INTTLookupElements::draw(channel),
            ibutterfly: IButterflyLookupElements::draw(channel),
            sub: SubLookupElements::draw(channel),
            half_range_check: RCLookupElements::draw(channel),
            low_sig_bound_check: RCLookupElements::draw(channel),
            high_sig_bound_check: RCLookupElements::draw(channel),
            roots: RootsLookupElements::draw(channel),
            inv_roots: InvRootsLookupElements::draw(channel),
        }
    }
}
