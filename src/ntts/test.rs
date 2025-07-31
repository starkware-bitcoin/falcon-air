use crate::{
    ntts::ntt::NTTState,
    zq::{OperationElements, Q, range_check},
};
use num_traits::{One, Zero};
use stwo::{
    core::{
        channel::Channel,
        fields::{m31::M31, qm31::QM31},
        pcs::TreeVec,
        poly::circle::CanonicCoset,
    },
    prover::{
        backend::simd::{SimdBackend, column::BaseColumn, m31::LOG_N_LANES, qm31::PackedQM31},
        poly::{BitReversedOrder, circle::CircleEvaluation},
    },
};
use stwo_constraint_framework::{FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation};

use super::*;

pub fn ntt(
    trace: &mut Vec<NTTTrace>,
    merge_trace: &mut Vec<Vec<MergeNTTTrace>>,
    f: &[u32],
) -> Vec<u32> {
    let n = f.len();
    if n > 2 {
        let (f0, f1) = split(f);
        let f0_ntt = ntt(trace, merge_trace, &f0);

        let f1_ntt = ntt(trace, merge_trace, &f1);

        merge_ntt(&f0_ntt, &f1_ntt)
    } else if n == 2 {
        let f1_j = (SQ1 * f[1]) % Q;
        let even = (f[0] + f1_j) % Q;
        let odd = (f[0] + Q - f1_j) % Q;

        let res = vec![even, odd];
        trace.push(NTTTrace {
            f0: f[0],
            f1: f[1],
            f1_times_sq1_elts: NTTOperationElements {
                quotient: (f[1] * SQ1) / Q,
                remainder: f1_j,
            },
            f0_plus_f1_times_sq1_elts: NTTOperationElements {
                quotient: (f[0] + f1_j) / Q,
                remainder: even,
            },
            f0_minus_f1_times_sq1_elts: NTTOperationElements {
                quotient: (f[0] < f1_j) as u32,
                remainder: odd,
            },
        });
        res
    } else {
        panic!("n is not a power of 2");
    }
}
pub fn split(f: &[u32]) -> (Vec<u32>, Vec<u32>) {
    let mut f0 = vec![];
    let mut f1 = vec![];

    for (i, coef) in f.iter().enumerate() {
        if i % 2 == 0 {
            f0.push(*coef);
        } else {
            f1.push(*coef);
        }
    }
    (f0, f1)
}

pub fn merge_ntt(f0_ntt: &[u32], f1_ntt: &[u32]) -> Vec<u32> {
    assert_eq!(f0_ntt.len(), f1_ntt.len(), "f0_ntt.len() != f1_ntt.len()");
    let n = 2 * f0_ntt.len();
    let roots = ROOTS[n.ilog2() as usize];
    let mut f_ntt = vec![0; n];

    for i in 0..n / 2 {
        f_ntt[2 * i] = (f0_ntt[i] + roots[2 * i] * f1_ntt[i]) % Q;
        f_ntt[2 * i + 1] = (f0_ntt[i] + Q - (roots[2 * i] * f1_ntt[i]) % Q) % Q;
    }
    f_ntt
}

#[derive(Debug, Clone)]
pub struct NTTClaim {
    pub log_size: u32,
}
#[derive(Debug, Clone)]
pub struct NTTOperationElements {
    pub quotient: u32,
    pub remainder: u32,
}
#[derive(Debug, Clone)]
pub struct NTTTrace {
    f0: u32,
    f1: u32,
    f1_times_sq1_elts: NTTOperationElements,
    f0_plus_f1_times_sq1_elts: NTTOperationElements,
    f0_minus_f1_times_sq1_elts: NTTOperationElements,
}
#[derive(Debug, Clone)]
pub struct MergeNTTTrace {
    pub f0: u32,
    pub f1: u32,
    pub root_times_f1: NTTOperationElements,
    pub f0_plus_root_times_f1: NTTOperationElements,
    pub f0_minus_root_times_f1: NTTOperationElements,
}
impl NTTClaim {
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let trace_log_sizes = vec![self.log_size; 64]; // 64 columns, each with log_size
        TreeVec::new(vec![vec![], trace_log_sizes, vec![]])
    }
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    pub fn gen_trace(
        &self,
        poly: &[u32],
    ) -> (
        Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Vec<M31>,
    ) {
        let mut trace = vec![];
        let mut merge_trace = vec![];
        ntt(&mut trace, &mut merge_trace, poly);

        let mut actual_trace = vec![];
        let mut remainders = vec![];
        for cols in trace {
            let mut f0 = vec![M31::zero(); 1 << self.log_size];
            let mut f1 = vec![M31::zero(); 1 << self.log_size];
            let mut f1_times_sq1_q = vec![M31::zero(); 1 << self.log_size];
            let mut f1_times_sq1_r = vec![M31::zero(); 1 << self.log_size];
            let mut f0_plus_f1_times_sq1_q = vec![M31::zero(); 1 << self.log_size];
            let mut f0_plus_f1_times_sq1_r = vec![M31::zero(); 1 << self.log_size];
            let mut f0_minus_f1_times_sq1_q = vec![M31::zero(); 1 << self.log_size];
            let mut f0_minus_f1_times_sq1_r = vec![M31::zero(); 1 << self.log_size];
            // let i = bit_reverse_index(0, self.log_size);
            let i = 0;
            f0[i] = M31(cols.f0);
            f1[i] = M31(cols.f1);
            f1_times_sq1_q[i] = M31(cols.f1_times_sq1_elts.quotient);
            f1_times_sq1_r[i] = M31(cols.f1_times_sq1_elts.remainder);
            f0_plus_f1_times_sq1_q[i] = M31(cols.f0_plus_f1_times_sq1_elts.quotient);
            f0_plus_f1_times_sq1_r[i] = M31(cols.f0_plus_f1_times_sq1_elts.remainder);
            f0_minus_f1_times_sq1_q[i] = M31(cols.f0_minus_f1_times_sq1_elts.quotient);
            f0_minus_f1_times_sq1_r[i] = M31(cols.f0_minus_f1_times_sq1_elts.remainder);
            println!("trace {:?}", cols);
            println!("f0.len: {:?}", f0.len());
            actual_trace.push(CircleEvaluation::new(
                CanonicCoset::new(self.log_size).circle_domain(),
                BaseColumn::from_iter(f0),
            ));
            actual_trace.push(CircleEvaluation::new(
                CanonicCoset::new(self.log_size).circle_domain(),
                BaseColumn::from_iter(f1),
            ));
            actual_trace.push(CircleEvaluation::new(
                CanonicCoset::new(self.log_size).circle_domain(),
                BaseColumn::from_iter(f1_times_sq1_q),
            ));
            actual_trace.push(CircleEvaluation::new(
                CanonicCoset::new(self.log_size).circle_domain(),
                BaseColumn::from_iter(f1_times_sq1_r),
            ));
            actual_trace.push(CircleEvaluation::new(
                CanonicCoset::new(self.log_size).circle_domain(),
                BaseColumn::from_iter(f0_plus_f1_times_sq1_q),
            ));
            actual_trace.push(CircleEvaluation::new(
                CanonicCoset::new(self.log_size).circle_domain(),
                BaseColumn::from_iter(f0_plus_f1_times_sq1_r),
            ));
            actual_trace.push(CircleEvaluation::new(
                CanonicCoset::new(self.log_size).circle_domain(),
                BaseColumn::from_iter(f0_minus_f1_times_sq1_q),
            ));
            actual_trace.push(CircleEvaluation::new(
                CanonicCoset::new(self.log_size).circle_domain(),
                BaseColumn::from_iter(f0_minus_f1_times_sq1_r),
            ));
            remainders.push(M31(cols.f1_times_sq1_elts.remainder));
            remainders.push(M31(cols.f0_plus_f1_times_sq1_elts.remainder));
            remainders.push(M31(cols.f0_minus_f1_times_sq1_elts.remainder));
        }
        (actual_trace, remainders)
    }
}

#[derive(Debug, Clone)]
pub struct NTTInteractionClaim {
    pub claimed_sum: QM31,
}

impl NTTInteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
    pub fn gen_interaction_trace(
        trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
        lookup_elements: &range_check::LookupElements,
    ) -> (
        Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>,
        Self,
    ) {
        let log_size = trace[0].domain.log_size();
        let mut logup_gen = LogupTraceGenerator::new(log_size);

        // We have three separate remainder columns (at indices 3,5,7) to range-check.
        for &col_idx in &[3, 5, 7] {
            let mut col_gen = logup_gen.new_col();
            for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                let value = trace[col_idx].data[vec_row];
                let denom = lookup_elements.combine(&[value]);
                col_gen.write_frac(vec_row, PackedQM31::one(), denom);
            }
            col_gen.finalize_col();
        }

        // Now close out the log-up and grab the claimed sum
        let (interaction_trace, claimed_sum) = logup_gen.finalize_last();
        (interaction_trace, Self { claimed_sum })
    }
}

pub struct NTTEval {
    pub claim: NTTClaim,
    pub lookup_elements: range_check::LookupElements,
}

impl FrameworkEval for NTTEval {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.claim.log_size + 1
    }

    /// Evaluates the modular addition constraints.
    ///
    /// # Constraints
    ///
    /// 1. **Arithmetic constraint**: a + b = quotient * Q + remainder
    /// 2. **Range check**: remainder ∈ [0, Q) via lookup table
    fn evaluate<E: stwo_constraint_framework::EvalAtRow>(&self, mut eval: E) -> E {
        // Extract trace values
        let mut f = vec![];
        for _ in 0..8 {
            let f0 = eval.next_trace_mask();
            let f1 = eval.next_trace_mask();
            let f1_times_sq1_q = eval.next_trace_mask();
            let f1_times_sq1_r = eval.next_trace_mask();
            let f0_plus_f1_times_sq1_q = eval.next_trace_mask();
            let f0_plus_f1_times_sq1_r = eval.next_trace_mask();
            let f0_minus_f1_times_sq1_q = eval.next_trace_mask();
            let f0_minus_f1_times_sq1_r = eval.next_trace_mask();
            let state = NTTState::<E> {
                f0,
                f1,
                f1_times_sq1_elts: OperationElements {
                    quotient: f1_times_sq1_q,
                    remainder: f1_times_sq1_r,
                },
                f0_plus_f1_times_sq1_elts: OperationElements {
                    quotient: f0_plus_f1_times_sq1_q,
                    remainder: f0_plus_f1_times_sq1_r,
                },
                f0_minus_f1_times_sq1_elts: OperationElements {
                    quotient: f0_minus_f1_times_sq1_q,
                    remainder: f0_minus_f1_times_sq1_r,
                },
            };
            f.push(state);
        }
        println!("f: {:?}", f.len());
        let f: [NTTState<E>; 8] = match f.try_into() {
            Ok(f) => f,
            Err(_) => panic!("fuck"),
        };

        super::ntt::NTT::evaluate(&f, &[], &self.lookup_elements, &mut eval);
        // Now we need to check that the remainder is in the range [0, Q)
        // We do this by using the range check we defined. Here we increment the multiplicity of
        // this value (remainder) by 1 because we want to range check it and the logup sum has to be exactly 0
        // So here we increment and in the range_check we decrements

        eval.finalize_logup_in_pairs();
        eval
    }
}
pub type Component = FrameworkComponent<NTTEval>;
