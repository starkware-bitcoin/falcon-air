use crate::{
    ntts::{intt, mul, ntt},
    zq::range_check,
};
use itertools::{Itertools, chain};
use stwo::{
    core::{channel::Channel, fields::m31::M31, pcs::TreeVec},
    prover::{
        backend::simd::SimdBackend,
        poly::{BitReversedOrder, circle::CircleEvaluation},
    },
};

#[derive(Debug, Clone)]
pub struct BigClaim {
    /// Claim for NTT operations
    pub f_ntt: ntt::Claim,
    /// Claim for NTT operations
    pub g_ntt: ntt::Claim,
    /// Claim for multiplication operations
    pub mul: mul::Claim,
    /// Claim for INTT operations
    pub intt: intt::Claim,
    /// Claim for range checking operations
    pub range_check: range_check::Claim,
}

#[derive(Debug, Clone)]
pub struct AllTraces {
    /// Trace columns from NTT operations
    pub f_ntt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from NTT operations
    pub g_ntt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from multiplication operations
    pub mul: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace columns from INTT operations
    pub intt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
    /// Trace column from range checking: multiplicities
    pub range_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
}

impl AllTraces {
    /// Creates a new AllTraces instance with the provided traces.
    pub fn new(
        f_ntt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        g_ntt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        mul: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        intt: Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        range_check: CircleEvaluation<SimdBackend, M31, BitReversedOrder>,
    ) -> Self {
        Self {
            f_ntt,
            g_ntt,
            mul,
            intt,
            range_check,
        }
    }
}

impl BigClaim {
    /// Returns the combined log sizes for all trace columns.
    ///
    /// Concatenates the log sizes from all four components to determine
    /// the total trace structure.
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let trees = vec![
            self.f_ntt.log_sizes(),
            self.g_ntt.log_sizes(),
            self.mul.log_sizes(),
            self.intt.log_sizes(),
            self.range_check.log_sizes(),
        ];
        TreeVec::concat_cols(trees.into_iter())
    }

    /// Mixes all claim parameters into the Fiat-Shamir channel.
    ///
    /// This ensures that the proof is deterministic and all components
    /// contribute to the randomness.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.f_ntt.mix_into(channel);
        self.g_ntt.mix_into(channel);
        self.mul.mix_into(channel);
        self.intt.mix_into(channel);
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
    ) -> (
        Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        AllTraces,
    ) {
        let (f_ntt_trace, f_ntt_remainders, f_ntt_output) = self.f_ntt.gen_trace();
        let (g_ntt_trace, g_ntt_remainders, g_ntt_output) = self.g_ntt.gen_trace();
        let (mul_trace, mul_remainders) = self.mul.gen_trace(&f_ntt_output, &g_ntt_output);
        let (intt_trace, intt_remainders) = self
            .intt
            .gen_trace(mul_remainders.iter().map(|r| r.0).collect_vec());
        let range_check_trace = self.range_check.gen_trace(
            &chain!(
                f_ntt_remainders,
                g_ntt_remainders,
                intt_remainders,
                [mul_remainders]
            )
            .collect_vec(),
        );
        (
            chain!(
                f_ntt_trace.clone(),
                g_ntt_trace.clone(),
                mul_trace.clone(),
                intt_trace.clone(),
                [range_check_trace.clone()]
            )
            .collect_vec(),
            AllTraces::new(
                f_ntt_trace,
                g_ntt_trace,
                mul_trace,
                intt_trace,
                range_check_trace,
            ),
        )
    }
}
