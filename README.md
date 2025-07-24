# Falcon-AIR

A STARK proof system implementation for modular arithmetic operations in the field Z_q where q = 12 * 1024 + 1 = 12289.

## Overview

Falcon-AIR provides a complete STARK proof system for modular arithmetic operations that are compatible with the Falcon signature scheme. The system generates proofs for:

- **Modular Addition**: (a + b) mod q
- **Modular Multiplication**: (a * b) mod q  
- **Modular Subtraction**: (a - b) mod q
- **Range Checking**: Ensuring all results are in [0, q)

All operations are performed in the field Z_q where q = 12289, which is specifically chosen to be compatible with the Falcon signature scheme requirements.

## Features

- **Complete STARK Proof System**: Generates cryptographic proofs for arithmetic operations
- **Modular Arithmetic**: Supports addition, multiplication, and subtraction modulo q
- **Range Checking**: Ensures all values remain within the valid field range
- **Efficient Implementation**: Uses the STWO framework for optimized proof generation
- **Comprehensive Testing**: Includes test suites for all components

## Architecture

The system is organized into several key components:

### Core Modules

- **`zq/add.rs`**: Modular addition operations
- **`zq/mul.rs`**: Modular multiplication operations  
- **`zq/sub.rs`**: Modular subtraction operations
- **`zq/range_check.rs`**: Range checking for field values
- **`big_air.rs`**: Combined proof system orchestrating all components

### Key Concepts

1. **Trace Generation**: Each operation generates execution traces that encode the computation
2. **Constraint Evaluation**: Constraints ensure mathematical correctness of operations
3. **Lookup Relations**: Range checking uses lookup tables to validate field membership
4. **Interaction Claims**: Connect arithmetic operations with range checking through lookup protocols

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
falcon-air = { git = "https://github.com/your-username/falcon-air" }
```

## Usage

### Basic Usage

```rust
use falcon_air::big_air::prove_falcon;

// Generate a STARK proof for all arithmetic operations
match prove_falcon() {
    Ok(proof) => {
        println!("Proof generated successfully!");
        // The proof can now be verified by a verifier
    }
    Err(e) => {
        eprintln!("Proof generation failed: {:?}", e);
    }
}
```

### Individual Components

You can also use individual components for specific operations:

```rust
use falcon_air::zq::{add, mul, sub, range_check};

// Create claims for specific operations
let add_claim = add::Claim { log_size: 14 };
let mul_claim = mul::Claim { log_size: 14 };
let sub_claim = sub::Claim { log_size: 14 };

// Generate traces
let (add_trace, add_remainders) = add_claim.gen_trace();
let (mul_trace, mul_remainders) = mul_claim.gen_trace();
let (sub_trace, sub_remainders) = sub_claim.gen_trace();
```

## Field Specification

The system operates in the field Z_q where:

- **q = 12289** = 12 * 1024 + 1
- **Field Size**: 2^13.585 bits
- **Compatibility**: Chosen for Falcon signature scheme compatibility

### Mathematical Properties

- q is a prime number
- q - 1 = 2^13 * 3 * 641
- Supports efficient modular arithmetic operations
- Compatible with STARK proof systems

## Proof System Details

### Trace Structure

Each arithmetic operation generates traces with the following structure:

- **Addition**: [a, b, quotient, remainder] (4 columns)
- **Multiplication**: [a, b, quotient, remainder] (4 columns)  
- **Subtraction**: [a, b, remainder] (3 columns)
- **Range Check**: [multiplicities] (1 column)

### Constraints

The system enforces several types of constraints:

1. **Arithmetic Constraints**: Ensure mathematical correctness
   - Addition: a + b = quotient * q + remainder
   - Multiplication: a * b = quotient * q + remainder
   - Subtraction: a - b = remainder (mod q)

2. **Range Constraints**: Ensure values are in [0, q)
   - Uses lookup tables for efficient range checking
   - Validates all operation results

3. **Lookup Relations**: Connect arithmetic operations with range checking
   - Ensures consistency across all components
   - Provides cryptographic security

## Testing

Run the test suite:

```bash
cargo test
```

Run specific tests:

```bash
# Test the complete proof system
cargo test big_air::tests::test_prove_falcon

# Test individual components
cargo test zq::add
cargo test zq::mul
cargo test zq::sub
cargo test zq::range_check
```

## Performance

The system is optimized for:

- **Efficient Trace Generation**: Uses SIMD operations where possible
- **Fast Constraint Evaluation**: Leverages the STWO framework optimizations
- **Compact Proofs**: Generates minimal-size STARK proofs
- **Parallel Processing**: Supports parallel execution for large traces

## Security

The system provides cryptographic security through:

- **STARK Proofs**: Zero-knowledge proofs of computational integrity
- **Fiat-Shamir Transform**: Converts interactive proofs to non-interactive
- **Merkle Tree Commitments**: Efficient commitment schemes for large data
- **Lookup Protocols**: Secure range checking without revealing values

## Dependencies

- **STWO**: STARK proof framework
- **STWO Constraint Framework**: Circuit building framework
- **num-traits**: Mathematical trait implementations
- **rand**: Random number generation
- **itertools**: Iterator utilities

## Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests for new functionality
5. Ensure all tests pass
6. Submit a pull request

## License

This project is licensed under the MIT License - see the LICENSE file for details.

## References

- [STARK Proofs](https://eprint.iacr.org/2018/046.pdf)
- [Falcon Signature Scheme](https://falcon-sign.info/)
- [STWO Framework](https://github.com/starkware-libs/stwo)

## Acknowledgments

- Built on the STWO framework by StarkWare
- Inspired by the Falcon signature scheme requirements
- Uses modern Rust cryptography practices 