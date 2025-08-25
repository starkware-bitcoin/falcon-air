use stwo::core::channel::Channel;
use stwo_constraint_framework::relation;

relation!(RCLookupElements, 1);
relation!(NTTLookupElements, 1);
relation!(ButterflyLookupElements, 1);
relation!(MulLookupElements, 1);
relation!(INTTLookupElements, 1);
relation!(SubLookupElements, 1);
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
            f_ntt: NTTLookupElements::draw(channel),
            g_ntt_butterfly: ButterflyLookupElements::draw(channel),
            g_ntt: NTTLookupElements::draw(channel),
            mul: MulLookupElements::draw(channel),
            intt: INTTLookupElements::draw(channel),
            sub: SubLookupElements::draw(channel),
            half_range_check: RCLookupElements::draw(channel),
            low_sig_bound_check: RCLookupElements::draw(channel),
            high_sig_bound_check: RCLookupElements::draw(channel),
        }
    }
}
