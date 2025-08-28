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
use stwo_constraint_framework::{Relation, RelationEFTraitBound, relation};

relation!(RCLookupElements, 1);
relation!(FNTTLookupElements, 1);
relation!(GNTTLookupElements, 1);
relation!(ButterflyLookupElements, 1);
relation!(MulLookupElements, 1);
relation!(INTTLookupElements, 1);
relation!(IButterflyLookupElements, 1);
relation!(SubLookupElements, 1);

#[derive(Debug, Clone)]
pub enum NTTLookupElements {
    F(FNTTLookupElements),
    G(GNTTLookupElements),
}

impl NTTLookupElements {
    pub fn f_draw(channel: &mut impl Channel) -> Self {
        Self::F(FNTTLookupElements::draw(channel))
    }

    pub fn g_draw(channel: &mut impl Channel) -> Self {
        Self::G(GNTTLookupElements::draw(channel))
    }
}
impl<F, EF> Relation<F, EF> for NTTLookupElements
where
    F: Clone,
    EF: RelationEFTraitBound<F>,
{
    fn combine(&self, values: &[F]) -> EF {
        match self {
            NTTLookupElements::F(lookup_elements) => lookup_elements.combine(values),
            NTTLookupElements::G(lookup_elements) => lookup_elements.combine(values),
        }
    }

    fn get_name(&self) -> &str {
        match self {
            NTTLookupElements::F(lookup_elements) => {
                <FNTTLookupElements as Relation<F, EF>>::get_name(lookup_elements)
            }
            NTTLookupElements::G(lookup_elements) => {
                <GNTTLookupElements as Relation<F, EF>>::get_name(lookup_elements)
            }
        }
    }

    fn get_size(&self) -> usize {
        match self {
            NTTLookupElements::F(lookup_elements) => {
                <FNTTLookupElements as Relation<F, EF>>::get_size(lookup_elements)
            }
            NTTLookupElements::G(lookup_elements) => {
                <GNTTLookupElements as Relation<F, EF>>::get_size(lookup_elements)
            }
        }
    }
}
#[derive(Debug, Clone)]
pub enum INTTInputLookupElements {
    Mul(MulLookupElements),
    INTTOutput(INTTLookupElements),
}

impl INTTInputLookupElements {
    pub fn ibutterfly_draw(channel: &mut impl Channel) -> Self {
        Self::Mul(MulLookupElements::draw(channel))
    }

    pub fn mul_draw(channel: &mut impl Channel) -> Self {
        Self::INTTOutput(INTTLookupElements::draw(channel))
    }
}
impl<F, EF> Relation<F, EF> for INTTInputLookupElements
where
    F: Clone,
    EF: RelationEFTraitBound<F>,
{
    fn combine(&self, values: &[F]) -> EF {
        match self {
            INTTInputLookupElements::Mul(lookup_elements) => lookup_elements.combine(values),
            INTTInputLookupElements::INTTOutput(lookup_elements) => lookup_elements.combine(values),
        }
    }

    fn get_name(&self) -> &str {
        match self {
            INTTInputLookupElements::Mul(lookup_elements) => {
                <MulLookupElements as Relation<F, EF>>::get_name(lookup_elements)
            }
            INTTInputLookupElements::INTTOutput(lookup_elements) => {
                <INTTLookupElements as Relation<F, EF>>::get_name(lookup_elements)
            }
        }
    }

    fn get_size(&self) -> usize {
        match self {
            INTTInputLookupElements::Mul(lookup_elements) => {
                <MulLookupElements as Relation<F, EF>>::get_size(lookup_elements)
            }
            INTTInputLookupElements::INTTOutput(lookup_elements) => {
                <INTTLookupElements as Relation<F, EF>>::get_size(lookup_elements)
            }
        }
    }
}

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
        }
    }
}
