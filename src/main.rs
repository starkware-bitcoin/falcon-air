//! # Falcon-AIR Main Binary
//!
//! This is the main entry point for the Falcon-AIR STARK proof system.
//! It demonstrates how to generate a complete STARK proof for all modular
//! arithmetic operations in the field Z_q where q = 12289.
//!
//! # Usage
//!
//! The binary generates a STARK proof for the Falcon signature scheme operations
//! and saves it to a compressed file for later verification.
//!
//! # Output
//!
//! - Generates a STARK proof for all arithmetic operations
//! - Saves the proof to `proof.bin` in compressed format
//! - Uses bzip2 compression for efficient storage
//!
//! # Example
//!
//! ```bash
//! cargo run --release
//! # This will generate proof.bin containing the compressed STARK proof
//! ```

use std::io::Write;

use bzip2::Compression;
use bzip2::write::BzEncoder;
use falcon_air::big_air::prove_falcon;
use falcon_air::input::{MSG_POINT, PK, TEST_S1};

/// Main function that generates a complete STARK proof for Falcon signature operations.
///
/// This function demonstrates the complete workflow:
/// 1. Generates a STARK proof for all modular arithmetic operations
/// 2. Serializes the proof using bincode for efficient binary representation
/// 3. Compresses the proof using bzip2 for storage efficiency
/// 4. Saves the compressed proof to `proof.bin`
///
/// # Returns
///
/// Returns `()` on success, or panics with an error message on failure.
///
/// # Panics
///
/// This function will panic if:
/// - Proof generation fails
/// - File creation fails
/// - Serialization fails
/// - Compression fails
fn main() {
    // Generate a complete STARK proof for all arithmetic operations
    // This includes modular addition, multiplication, subtraction, and range checking
    let proof = prove_falcon(TEST_S1, PK, MSG_POINT).unwrap();

    // Create a file to store the compressed proof
    let proof_file = std::fs::File::create("proof.bin").unwrap();

    // Serialize the proof to binary format using bincode
    // This provides efficient binary representation of the proof data
    let serialized_bytes = bincode::serialize(&proof).unwrap();

    // Compress the proof using bzip2 with best compression level
    // This significantly reduces the file size for storage and transmission
    let mut bz_encoder = BzEncoder::new(proof_file, Compression::best());
    bz_encoder.write_all(&serialized_bytes).unwrap();
    bz_encoder.finish().unwrap();

    // The compressed proof is now saved to proof.bin
    // This file can be used for later verification or transmission
}
