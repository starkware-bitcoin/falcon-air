use std::io::Write;

use bzip2::Compression;
use bzip2::write::BzEncoder;
use falcon_air::big_air::prove_falcon;
use falcon_air::input::{MSG_POINT, PK, TEST_S1};

fn main() {
    // --- your program here ---
    let proof = prove_falcon(TEST_S1, PK, MSG_POINT).unwrap();
    let proof_file = std::fs::File::create("proof.bin").unwrap();
    let serialized_bytes = bincode::serialize(&proof).unwrap();
    let mut bz_encoder = BzEncoder::new(proof_file, Compression::best());
    bz_encoder.write_all(&serialized_bytes).unwrap();
    bz_encoder.finish().unwrap();
}
