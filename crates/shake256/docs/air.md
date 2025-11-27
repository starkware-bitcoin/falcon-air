# AIR DESIGN

This document presents the AIR for Shake256.

## I. SHAKE-256

This component handles padding, initialization, absorbing, and squeezing by calling `Keccak` instances.
Here “calling” `Keccak` means emitting the input and using the output via lookups. This is the only
way for components to interact between each other. Was considered to have a single trace for both `Shake256` and
`Keccak`, but that would have required approximately `10 * N_COLUMNS_KECCAK ≈ 500,000` columns which leads to an important decrease in performance. The same logic was applied to the `Keccak` component that calls the `Keccak_round` sub-routine to apply a keccak round on the state. This makes the trace longer but thiner leading to better performance (we mesured a x2 improvement as the number of columns is divided by 5).

### 1. Trace Layout (NB of columns)

Main trace:

- Enabler: 1
- Initial State: `N_BYTES_IN_MESSAGE` (72)
- States on which Keccak was applied: `N_BYTES_IN_MESSAGE * N_SQUEEZING` (2000)

Interaction columns (detailed in AIR):
`SECURE_EXTENSION_DEGREE * (N_SHAKE256_LOOKUPS + N_KECCAK_LOOKUPS).div_ceil(2)` (44)

TOTAL: 2117 T

### 2. AIR

The AIR works with messages up to 135 bytes (as explained in `input.md`). We perform padding and
initialization knowing that absorption will only require a single Keccak permutation.

Use the message (for inter-component operability):

```
- enabler * Shake256(message)`
```

Absorb the state:

```
+ enabler * Keccak(state)
- enabler * Keccak(state)
```

Squeeze `N_SQUEEZING - 1` times:

```
+ enabler * Keccak(state)
- enabler * Keccak(state)
```

At each iteration, add the rate to the output buffer `Z`.

Emit the output:

```
+ enabler * Shake256(Z)
```

## II. KECCAK-F[1600]

This component implements an AIR for the Keccak permutation. We opted for an 8-byte representation
of `u64`s as it yields more efficient arithmetic for rotations (compared to `6 × u12`, for instance).
Also, `4 × u16` makes lookups impractical, as a simple XOR would require a preprocessed column of
`log_size = 32`.

Note: consider all indices taken modulo their range (`SQRT_N_LANES_SHAKE256`, 8 for rotations, etc.).

### 1. Trace Layout (NB of columns)

- Enabler: 1
- Initial state: `N_BYTES_IN_STATE` (200)
- State after each round: `N_ROUNDS * N_BYTES_IN_STATE` (4800)

### 2. AIR

As for Shake, use the initial state:

```
- enabler * Keccak(S)
```

Then for each round "apply" a keccak round by imposing the round constant used in the lookup:

```
+ enabler * Keccak_round(RC[round], S)
- enabler * Keccak_round(RC[round+1], new_S)
S = new_S
```

Emit the final state:

```
+ enabler * Keccak(S)
```

## III. KECCAK ROUND

### 1. Trace Layout (NB of columns)

- Enabler: 1
- Initial state: `N_BYTES_IN_STATE` (200)
- Round constants: `2 * N_BYTES_IN_U64` (16)
- `C` and `C_inter`: `2 * SQRT_N_LANES_SHAKE256 * N_BYTES_IN_U64 * (T + L)` (240)
- `C_rot`: `SQRT_N_LANES_SHAKE256 * (N_BYTES_IN_U64 * T + 3 * L)` (70)
- `D`: `SQRT_N_LANES_SHAKE256 * N_BYTES_IN_U64 * (T + L)` (120)
- `S THETA`: `N_LANES_SHAKE256 * N_BYTES_IN_U64 * (T + L)` (600)
- `B`: `(N_LANES_SHAKE256 - 3) * (N_BYTES_IN_U64 * T + 3 * L)` (308)
- `S CHI`: `N_LANES_SHAKE256 * N_BYTES_IN_U64 * (T + L)` (600)
- `S IOTA`: `N_BYTES_IN_U64 * (T + L)` (24)

TOTAL: 2185 T

### 2. AIR

Use the `keccak_round` input:

```
- enabler * Keccak_round(S)
```

Compute `C` (using `C_inter`), for `x` in `0..SQRT_N_LANES_SHAKE256`:

```
+ Xor_8_8_8(S[x], S[x, 1], S[x, 2], C_inter[x])
+ Xor_8_8_8(C_inter[x], S[x, 3], S[x, 4], C[x])
```

Rotate `C[x+1]` by 1 to the left (see Rotation AIRs).

Compute `D`, for `x` in `0..SQRT_N_LANES_SHAKE256`:

```
+ Xor_8_8(C[x-1], C_rot[x+1], D[x])
```

Update `S` using `D` (THETA), for `x, y` in `0..N_LANES_SHAKE256`:

```
+ Xor_8_8(S[x,y], D[x], res_S[x,y])
```

Compute `B` by applying rotations on `S[x,y]` (RHO and PI) (see Rotation AIRs).

Update `S` using `D` (CHI), for `x, y` in `0..N_LANES_SHAKE256`:

```
+ Chi_8_8_8(B[x,y], B[x+1,y], B[x+2,y], S[x,y])
```

Update `S[0]` using round constants (IOTA):

```
+ Xor_8_8(S[0], RC, res_S_xor_RC)
```

Emit the final round state:

```
+ enabler * Keccak_round(S)
```

### 3. Rotation AIRs

Take `rotr(A, n)` where `A` is represented as 8 limbs of 8 bits (one byte) each.

First compute `q, r = divmod(n, 8)`.

Then rotate by `8*q` bits (i.e., `q` bytes) to the right — a simple array re-ordering:
`A[i] = A[(i + q) % 8]`.

Then rotate `r` bits to the right (note that `1 <= r <= 7`):

- guess `a_hi_limbs[i] = (A[i] >> r) & (2**r - 1)` (the high parts of the 8-bit words)
- compute the low part: `a_lo_limbs[i] = A[i] - a_hi_limbs[i] * 2 ** r`
- finally, range-check the low parts by grouping them by 3:
  `+ rc_7_7_7(a_lo_limbs[0], a_lo_limbs[1], a_lo_limbs[2])`, etc.

The final rotated result is given by:
`A[i + 1] = a_hi_limbs[i+1] + a_lo_limbs[i] * 2 ** (8 - r)`
