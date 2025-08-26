use stwo::core::channel::Channel;
use stwo_constraint_framework::{Relation, RelationEFTraitBound, relation};

relation!(RCLookupElements, 1);
relation!(FNTTLookupElements, 1);
relation!(GNTTLookupElements, 1);
relation!(ButterflyLookupElements, 1);
relation!(MulLookupElements, 1);
relation!(INTTLookupElements, 1);
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
pub struct LookupElements {
    pub rc: RCLookupElements,
    pub f_ntt_butterfly: ButterflyLookupElements,
    pub f_ntt: NTTLookupElements,
    pub g_ntt_butterfly: ButterflyLookupElements,
    pub g_ntt: NTTLookupElements,
    pub mul: MulLookupElements,
    pub intt: INTTLookupElements,
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
            sub: SubLookupElements::draw(channel),
            half_range_check: RCLookupElements::draw(channel),
            low_sig_bound_check: RCLookupElements::draw(channel),
            high_sig_bound_check: RCLookupElements::draw(channel),
        }
    }
}
