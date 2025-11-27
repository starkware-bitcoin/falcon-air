use std::sync::Once;
use std::thread;
use std::time::Instant;

use rayon::ThreadPoolBuilder;
use shake_256::constants::{N_BYTES_IN_MESSAGE, N_SQUEEZING};
use shake_256::prove_shake256;
use stwo_prover::core::backend::simd::m31::N_LANES;
use stwo_prover::core::pcs::PcsConfig;
use tracing::info;
use tracing_subscriber::{fmt, EnvFilter};

static INIT_LOG: Once = Once::new();

fn init_logging() {
    INIT_LOG.call_once(|| {
        let _ = fmt()
            .with_env_filter(
                EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info")),
            )
            .try_init();
    });
}

fn main() {
    init_logging();

    let n_messages: usize = 1024;
    let stack_mb: usize = 128;
    let rayon_stack_mb: usize = 64;
    let n_iterations: usize = 5;

    let handle = thread::Builder::new()
        .name("prove".into())
        .stack_size(stack_mb * 1024 * 1024)
        .spawn(move || {
            let pool = ThreadPoolBuilder::new()
                .stack_size(rayon_stack_mb * 1024 * 1024)
                .build()
                .expect("build rayon pool");

            pool.install(|| {
                let start = Instant::now();
                for _ in 0..n_iterations {
                    prove_shake256(
                        vec![[0u8; N_BYTES_IN_MESSAGE]; n_messages],
                        PcsConfig::default(),
                    )
                    .expect("Proving failed");
                }
                let duration = start.elapsed();

                // Average frequency based on average duration
                let avg_secs = (duration.as_secs_f64()) / n_iterations as f64;
                let computed_shake256_instances =
                    std::cmp::max(n_messages.next_power_of_two(), N_LANES);
                let computed_keccak_permutations =
                    std::cmp::max((n_messages * N_SQUEEZING).next_power_of_two(), N_LANES);
                let proving_frequency_shake256 = (computed_shake256_instances as f64) / avg_secs;
                let proving_frequency_keccak = (computed_keccak_permutations as f64) / avg_secs;

                info!("Average Witness+Proving generation time: {:.3}s", avg_secs);
                info!("SHAKE-256 instances: {:?}", computed_shake256_instances);
                info!("Keccak permutations: {:?}", computed_keccak_permutations);
                info!(
                    "Average Witness+Proving generation frequency for SHAKE-256: {:.2} Hz",
                    proving_frequency_shake256
                );
                info!(
                    "Average Witness+Proving generation frequency for Keccak: {:.2} Hz",
                    proving_frequency_keccak
                );
            })
        })
        .expect("failed to spawn proving thread");

    handle.join().expect("proving thread panicked");
}
