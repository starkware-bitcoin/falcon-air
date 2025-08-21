use falcon_air::big_air::prove_falcon;
use falcon_air::input::{MSG_POINT, PK, TEST_S1};

fn main() {
    // --- your program here ---
    prove_falcon(TEST_S1, PK, MSG_POINT).unwrap();
}
