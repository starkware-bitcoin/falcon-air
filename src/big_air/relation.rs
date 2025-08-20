use stwo::core::channel::Channel;

use crate::{
    ntts::{mul, ntt},
    zq::range_check,
};

#[derive(Debug, Clone)]
pub struct LookupElements {
    pub rc: range_check::RCLookupElements,
    pub f_ntt: ntt::NTTLookupElements,
    pub g_ntt: ntt::NTTLookupElements,
    pub mul: mul::MulLookupElements,
}

impl LookupElements {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            rc: range_check::RCLookupElements::draw(channel),
            f_ntt: ntt::NTTLookupElements::draw(channel),
            g_ntt: ntt::NTTLookupElements::draw(channel),
            mul: mul::MulLookupElements::draw(channel),
        }
    }
}
