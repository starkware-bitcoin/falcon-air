use crate::{
    POLY_SIZE,
    ntts::{intt, ntt},
    polys::{euclidean_norm, mul, sub},
    zq::range_check,
};
use itertools::{Itertools, chain};
use stwo::{
    core::{channel::Channel, fields::m31::M31},
    prover::{
        backend::simd::SimdBackend,
        poly::{BitReversedOrder, circle::CircleEvaluation},
    },
};

#[derive(Debug, Clone)]
pub struct BigClaim {
    /// Claim for butterfly operations
    pub f_ntt_butterfly: ntt::butterfly::Claim,
    /// Claim for NTT operations
    pub f_ntt: ntt::Claim,
    /// Claim for butterfly operations
    pub g_ntt_butterfly: ntt::butterfly::Claim,
    /// Claim for NTT operations
    pub g_ntt: ntt::Claim,
    /// Claim for multiplication operations
    pub mul: mul::Claim,
    /// Claim for INTT operations
    pub intt: intt::Claim,
    /// Claim for subtraction operations
    pub sub: sub::Claim,
    /// Claim for euclidean norm operations
    pub euclidean_norm: euclidean_norm::Claim,
    /// Claim for half range checking operations
    pub half_range_check: range_check::Claim,
    /// Claim for signature bound checking operations
    pub low_sig_bound_check: range_check::Claim,
    /// Claim for signature bound checking operations
    pub high_sig_bound_check: range_check::Claim,
    /// Claim for range checking operations
    pub range_check: range_check::Claim,
}

#[derive(Debug, Clone)]
pub struct AllTraces {
    /// Trace columns from butterfly operations
    pub f_ntt_butterfly: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from NTT operations
    pub f_ntt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from butterfly operations
    pub g_ntt_butterfly: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from NTT operations
    pub g_ntt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from multiplication operations
    pub mul: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from INTT operations
    pub intt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from subtraction operations
    pub sub: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from euclidean norm operations
    pub euclidean_norm: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace column from half range checking: multiplicities
    pub half_range_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
    /// Trace column from signature bound checking: multiplicities
    pub low_sig_bound_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
    /// Trace column from signature bound checking: multiplicities
    pub high_sig_bound_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
    /// Trace column from range checking: multiplicities
    pub range_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
}

impl AllTraces {
    /// Creates a new AllTraces instance with the provided traces.
    pub fn new(
        f_ntt_butterfly: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        f_ntt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        g_ntt_butterfly: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        g_ntt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        mul: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        intt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        sub: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        euclidean_norm: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        half_range_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
        low_sig_bound_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
        high_sig_bound_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
        range_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
    ) -> Self {
        Self {
            f_ntt_butterfly,
            f_ntt,
            g_ntt_butterfly,
            g_ntt,
            mul,
            intt,
            sub,
            euclidean_norm,
            half_range_check,
            low_sig_bound_check,
            high_sig_bound_check,
            range_check,
        }
    }
}

impl BigClaim {
    /// Mixes all claim parameters into the Fiat-Shamir channel.
    ///
    /// This ensures that the proof is deterministic and all components
    /// contribute to the randomness.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.f_ntt_butterfly.mix_into(channel);
        self.f_ntt.mix_into(channel);
        self.g_ntt_butterfly.mix_into(channel);
        self.g_ntt.mix_into(channel);
        self.mul.mix_into(channel);
        self.intt.mix_into(channel);
        self.sub.mix_into(channel);
        self.euclidean_norm.mix_into(channel);
        self.half_range_check.mix_into(channel);
        self.low_sig_bound_check.mix_into(channel);
        self.high_sig_bound_check.mix_into(channel);
        self.range_check.mix_into(channel);
    }

    /// Generates traces for all arithmetic operations.
    ///
    /// # Returns
    ///
    /// Returns a tuple containing:
    /// - A vector of all trace columns concatenated in order
    /// - An AllTraces struct containing the individual traces
    ///
    /// # Algorithm
    ///
    /// 1. Generates traces for addition, multiplication, and subtraction
    /// 2. Collects all remainder values for range checking
    /// 3. Generates the range check trace using all remainders
    /// 4. Concatenates all traces in the correct order
    pub fn gen_trace(
        &self,
        s1: &[u32; POLY_SIZE],
        pk: &[u32; POLY_SIZE],
        msg_point: &[u32; POLY_SIZE],
    ) -> (
        Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        AllTraces,
    ) {
        let (f_ntt_butterfly_trace, f_ntt_butterfly_remainders, f_ntt_butterfly_output) =
            self.f_ntt_butterfly.gen_trace(s1);
        let (f_ntt_trace, f_ntt_remainders, f_ntt_output) =
            self.f_ntt.gen_trace(&f_ntt_butterfly_output);

        let (g_ntt_butterfly_trace, g_ntt_butterfly_remainders, g_ntt_butterfly_output) =
            self.g_ntt_butterfly.gen_trace(pk);
        let (g_ntt_trace, g_ntt_remainders, g_ntt_output) =
            self.g_ntt.gen_trace(&g_ntt_butterfly_output);
        let (mul_trace, mul_remainders) = self.mul.gen_trace(&f_ntt_output, &g_ntt_output);
        let (intt_trace, intt_remainders, intt_output) = self
            .intt
            .gen_trace(mul_remainders.iter().map(|r| r.0).collect_vec());
        let (sub_trace, sub_remainders) = self.sub.gen_trace(msg_point, &intt_output);
        let (
            euclidean_norm_trace,
            euclidean_norm_remainders,
            (euclidean_norm_output_low, euclidean_norm_output_high),
        ) = self.euclidean_norm.gen_trace(
            &sub_remainders
                .iter()
                .map(|r| r.0)
                .collect_vec()
                .try_into()
                .unwrap(),
            s1,
        );
        let half_range_check_trace = self
            .half_range_check
            .gen_trace(&chain!([euclidean_norm_remainders]).collect_vec());

        let low_sig_bound_check_trace = self
            .low_sig_bound_check
            .gen_trace(&[vec![M31(euclidean_norm_output_low)]]);
        let high_sig_bound_check_trace = self
            .high_sig_bound_check
            .gen_trace(&[vec![M31(euclidean_norm_output_high)]]);
        let range_check_trace = self.range_check.gen_trace(
            &chain!(
                f_ntt_butterfly_remainders,
                f_ntt_remainders,
                g_ntt_butterfly_remainders,
                g_ntt_remainders,
                intt_remainders,
                [mul_remainders],
                [sub_remainders],
            )
            .collect_vec(),
        );
        (
            chain!(
                f_ntt_butterfly_trace.clone(),
                f_ntt_trace.clone(),
                g_ntt_butterfly_trace.clone(),
                g_ntt_trace.clone(),
                mul_trace.clone(),
                intt_trace.clone(),
                sub_trace.clone(),
                euclidean_norm_trace.clone(),
                [half_range_check_trace.clone()],
                [low_sig_bound_check_trace.clone()],
                [high_sig_bound_check_trace.clone()],
                [range_check_trace.clone()]
            )
            .collect_vec(),
            AllTraces::new(
                f_ntt_butterfly_trace,
                f_ntt_trace,
                g_ntt_butterfly_trace,
                g_ntt_trace,
                mul_trace,
                intt_trace,
                sub_trace,
                euclidean_norm_trace,
                half_range_check_trace,
                low_sig_bound_check_trace,
                high_sig_bound_check_trace,
                range_check_trace,
            ),
        )
    }
}
