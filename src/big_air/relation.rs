use stwo::core::channel::Channel;

use crate::{
    ntts::{intt, ntt},
    poly::mul,
    zq::range_check,
};

#[derive(Debug, Clone)]
pub struct LookupElements {
    pub full_rc: range_check::LookupElements,
    pub f_ntt: ntt::LookupElements,
    pub g_ntt: ntt::LookupElements,
    pub mul: mul::LookupElements,
    pub intt: intt::LookupElements,
}

impl LookupElements {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            full_rc: range_check::LookupElements::draw(channel),
            f_ntt: ntt::LookupElements::draw(channel),
            g_ntt: ntt::LookupElements::draw(channel),
            mul: mul::LookupElements::draw(channel),
            intt: intt::LookupElements::draw(channel),
        }
    }
}
