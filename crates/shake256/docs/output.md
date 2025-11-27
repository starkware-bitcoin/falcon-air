# SHAKE-256 Output Specification (Falcon)

- Summary: 10 squeezing rounds (1360 bytes) make the failure
  probability to obtain fewer than 512 accepted coefficients smaller
  than 1e−52. This comfortably simulates an XOF stream for Falcon and is
  far cheaper than a constant-time 64-bit-per-coefficient variant.

## Context

- SHAKE-256 is an XOF, so its output length is application-chosen.
- Falcon defines two ways to derive polynomial coefficients from an XOF
  [Falcon spec: https://falcon-sign.info/falcon.pdf]:
  - Hash-to-Point (stream + rejection sampling)
  - Constant-time variant (use wider draws, no rejection)

## Hash-to-Point (rejection sampling)

```
absorb_shake256(message)
i = 0
while i < n:
    t = next_16_bits()
    if t < k*q:            # accept with prob. p = k*q / 2^16
        c[i] = t mod q
        i += 1
```

- Builds the n coefficients via accept/reject on 16-bit draws.
- For Falcon-512: n = 512, q = 12289, and k = 5, so the acceptance rate is
  p = k·q / 2^16 ≈ 0.938.

## Constant-time variant

- Draw 64 bits per coefficient and skip the conditional. Cost: 64·n bits.
- For Falcon-512: 64·512 = 32,768 bits = 4,096 bytes.
- With SHAKE-256’s rate r = 1088 bits (136 bytes) per permutation,
  this requires ceil(4096 / 136) = 31 Keccak-f[1600] permutations.

We prefer the rejection-sampling approach with a fixed squeezing budget
that keeps failure probability negligible.

## Squeezing budget

- Let N denote the number of SHAKE-256 “squeezing rounds” (each is one
  Keccak-f[1600] permutation after absorption).
- SHAKE-256 rate: r = 1088 bits = 136 bytes per round.
- Total bytes produced: B(N) = 136 · N.
- Number of 16-bit draws available: T(N) = 136 / 2 · N = 68 · N.

For N = 10:

- B(10) = 1360 bytes, T(10) = 680 draws.

## Probability of running out

- Let X be the number of accepted extractions.
- Then X ~ Binomial(T(N), p) with p = k·q / 2^16.
- Goal for Falcon-512: ensure X ≥ 512 with overwhelming probability.

Using the Chernoff bound (see [Sinclair CS271, Lecture 13](https://web.archive.org/web/20141031035717/http://www.cs.berkeley.edu/~sinclair/cs271/n13.pdf)),
for 0 < $\lambda < \mu$ with $\mu = T\,p$:

$$
\Pr[X \le \mu - \lambda] \le \exp\{ -T\,H_{1-p}(1-p + \lambda/T) \}.
$$

Here $H_a(b)$ is given by

$$
H_a(b) = b\,\ln\!\left(\frac{b}{a}\right) + (1-b)\,\ln\!\left(\frac{1-b}{1-a}\right),
$$

with natural logarithms.

For Falcon-512 (q = 12289, k = 5 ⇒ p ≈ 0.938) the following bounds hold
for various N when we require at least 512 acceptances:

| N (rounds) | Upper bound for Pr[X ≤ 511] |
| ---------- | --------------------------- |
| 9          | 1e-16                       |
| 10         | 1e-52                       |
| 11         | 1e-97                       |
| 12         | 1e-147                      |

So with N = 10, the chance of not obtaining 512 accepted
coefficients is below 10^-52, which is negligible for practice.
