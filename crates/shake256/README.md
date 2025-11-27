# SHAKE-256

SHAKE-256 AIR and Keccak-f[1600] components built on Starkware’s Stwo prover.

## Run

Run the small CLI to prove+verify for N messages (defaults to 1):

- `RUST_LOG=info cargo run -p shake-256 -- 8`

## Benchmark

Measures witness generation + proving throughput for SHAKE-256 and underlying Keccak permutations.

- Run: `cargo bench -p shake-256 --bench prover_bench`

What it does:

- Proves `n_messages = 1024` instances per iteration for `n_iterations = 5`.
- Reports average seconds/iteration and effective frequencies (Hz) for:
  - SHAKE-256 instances (rounded up to SIMD lane width), and
  - Keccak-f[1600] permutations implied by the squeezing budget.

## E2E Test

Run the end-to-end test and constraint assertions (using larger stack):

- `RUST_MIN_STACK=67108864 cargo test -p shake-256 e2e_test --release -- --nocapture`
- `RUST_MIN_STACK=67108864 cargo test -p shake-256 test_constraints -- --nocapture`

What it does:

- Spawns a proving thread with a larger stack and a Rayon pool.
- Generates a proof for `n_messages = 1` (all-zero message) and verifies it.
- Asserts that component constraints hold.

## Reference Checks

- Keccak-f[1600]: the `keccak_compare_to_reference` unit test compares the final Keccak state produced by the trace generator to a reference implementation (tiny-keccak) on a per-byte, per-lane basis. See `src/trace/keccak.rs`.
- SHAKE-256: instead of byte-by-byte equality tests, the lookup (logup) sum is compensated using an external SHAKE-256 implementation. `PublicData::new` computes SHAKE-256 outputs with tiny-keccak, and `PublicData::initial_logup_sum` adds those outputs so that the logup sum is zero when constraints are satisfied. See `src/public_data.rs`.

## Performances

Overall number of columns: 9 437.

On a MBP M4 Pro:

- 52 Shake256 hashes per second
- 850 Keccak computations per second

Note that the number of Keccak per second is impacted by the Shake256 component that introduces 2000 extra columns needed for external use of the Shake hash.
