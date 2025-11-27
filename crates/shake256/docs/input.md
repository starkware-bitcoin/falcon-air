# SHAKE-256 Input Specification (Falcon)

- Summary: fixed 72-byte input `M = salt (40 B) || sighash (32 B)` fits in a
  single SHAKE-256 rate block (136 bytes). Absorption completes with one
  permutation after padding/domain separation, so cost is identical for any
  message up to 135 bytes. Targeted for Falcon signature hashing in a Bitcoin
  context.

## Context

- Keccak is a sponge construction, so SHAKE-256 accepts variable-length inputs.
- In an AIR (Algebraic Intermediate Representation), it is simpler and more
  efficient to use a fixed-size input.
- This SHAKE-256 AIR targets Falcon signature hashing for a Bitcoin context.

## Input layout

- We fix the absorbed message to 72 bytes:
  - `salt` — 40 bytes
  - `sighash` — 32 bytes (transaction’s sighash digest; 32-byte SHA-256 output)
- Concatenation:
  - `M = salt || sighash` (length `|M| = 72` bytes)

## Rate considerations

- SHAKE-256 uses Keccak-f[1600] with capacity `c = 512` bits and rate `r = 1088`
  bits (`r/8 = 136` bytes).
- Because `|M| = 72 < 136`, absorption fits in a single rate block with domain
  separation and padding applied in-place. In particular, one byte is reserved
  for the SHAKE-256 domain-separation suffix `d` (as used in the AIR), and the
  final bit `0x80` is applied at the end of the rate block.
- Practical implication: any message up to 135 bytes has the same absorption
  cost (one permutation after padding), so the 72-byte choice is optimal for
  this use case.
