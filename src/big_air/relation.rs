use stwo::core::channel::Channel;
use stwo_constraint_framework::relation;

relation!(RCLookupElements, 1);
relation!(NTTLookupElements, 1);
relation!(MulLookupElements, 1);
relation!(INTTLookupElements, 1);
#[derive(Debug, Clone)]
pub struct LookupElements {
    pub rc: RCLookupElements,
    pub f_ntt: NTTLookupElements,
    pub g_ntt: NTTLookupElements,
    pub mul: MulLookupElements,
    pub intt: INTTLookupElements,
}

impl LookupElements {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            rc: RCLookupElements::draw(channel),
            f_ntt: NTTLookupElements::draw(channel),
            g_ntt: NTTLookupElements::draw(channel),
            mul: MulLookupElements::draw(channel),
            intt: INTTLookupElements::draw(channel),
        }
    }
}
