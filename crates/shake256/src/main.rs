use std::thread;

use rayon::ThreadPoolBuilder;
use shake_256::{prove_shake256, verify_shake256};
use shake_256::constants::N_BYTES_IN_MESSAGE;
use stwo_prover::core::pcs::PcsConfig;
use tracing_subscriber::{fmt, EnvFilter};

fn main() {
    // In case of stack overflow, increase these values.
    let stack_mb: usize = 256;
    let rayon_stack_mb: usize = 128;

    // Initialize logging
    let _ = fmt()
        .with_env_filter(
            EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info")),
        )
        .try_init();

    // Number of messages: from CLI arg or default to 1.
    let n_messages: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(1);

    // Run proving on a thread with a larger stack to avoid main-thread overflow (due to large number of columns)
    let stack_size_bytes = stack_mb * 1024 * 1024;
    thread::Builder::new()
        .name("prove".into())
        .stack_size(stack_size_bytes)
        .spawn(move || {
            // Ensure Rayon workers have sufficiently large stacks too (due to large number of columns)
            let _ = ThreadPoolBuilder::new()
                .stack_size(rayon_stack_mb * 1024 * 1024)
                .build_global();

            let messages = vec![[0u8; N_BYTES_IN_MESSAGE]; n_messages];
            let proof =
                prove_shake256(messages, PcsConfig::default()).expect("Proving failed");
            verify_shake256(proof, PcsConfig::default()).expect("Verification failed");
        })
        .expect("failed to spawn proving thread")
        .join()
        .expect("proving thread panicked");
}
