use std::thread;

use rayon::ThreadPoolBuilder;
use shake_256::{prove_shake256, verify_shake256};
use shake_256::constants::N_BYTES_IN_MESSAGE;
use stwo_prover::core::pcs::PcsConfig;

use shake_256::debug_tools::assert_constraints::assert_constraints;
use std::sync::Once;
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

#[test]
fn e2e_test() {
    init_logging();

    let n_messages: usize = 1;
    let stack_mb: usize = 32;
    let rayon_stack_mb: usize = 16;

    thread::Builder::new()
        .name("prove".into())
        .stack_size(stack_mb * 1024 * 1024)
        .spawn(move || {
            let pool = ThreadPoolBuilder::new()
                .stack_size(rayon_stack_mb * 1024 * 1024)
                .build()
                .expect("build rayon pool");

            pool.install(|| {
                let messages = vec![[0u8; N_BYTES_IN_MESSAGE]; n_messages];
                let proof = prove_shake256(messages, PcsConfig::default()).expect("Proving failed");
                verify_shake256(proof, PcsConfig::default()).expect("Verification failed");
            });
        })
        .expect("failed to spawn proving thread")
        .join()
        .expect("proving thread panicked");
}

#[test]
fn test_constraints() {
    init_logging();
    assert_constraints(vec![[42u8; N_BYTES_IN_MESSAGE]; 1]);
}
