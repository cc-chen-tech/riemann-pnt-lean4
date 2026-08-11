# Actual cubic Carlson diagonal-tail bridge

## Purpose

The fixed-scale actual Carlson theorem had the quantifier shape

`for each x, eventually in n`.

That shape is insufficient when the explicit-formula scale and dyadic cut move
together. This slice proves the stronger shape already justified by the
underlying estimates:

`eventually in n, for every x >= 1, every tau, and every finite S`.

No new density estimate or multiplicity hypothesis is introduced.

## Uniform theorem chain

1. Carlson's certificate threshold depends only on the dyadic upper endpoint.
2. The analytic multiplicity constant `B` is global: it is chosen before
   `x`, `sigma`, `tau`, `n`, and `S`.
3. The block comparison is therefore uniform in `x`, `tau`, and `S`.
4. The moving cut `floor(log(m^gamma)/log 2)` tends to infinity, so every
   shifted tail block eventually lies beyond the common threshold.
5. Summable pointwise comparison yields an actual-zeta `tsum` bound.
6. Multiplying by `m^(-2*beta)` identifies the bound exactly with the
   quantitative model tail from the preceding slice.

The normalized actual tail is

`m^(-2*beta) * sum_{n > N_gamma(m)} actualSquareCapacity(m,n,S)`.

It tends to zero whenever

`2*(tau-beta) + gamma*(q(sigma)-6) < 0`.

The result holds after deleting any finite zero set `S`; deletion uses only
nonnegative-mass monotonicity inherited from the actual capacity theorem.

## Joint two-height output

For every `2/3 < beta < 1`, one joint parameter package gives actual diagonal
tail decay at three distinct heights:

- `gammaLow`: low probing height,
- `gammaHigh`: Carlson balanced split,
- `alpha`: outer contour height.

This is an actual zeta coefficient-square result conditional only on the
existing genuine `CarlsonEventualMajorant sigma` certificate interface. It
does not use Sharp lower bounds or half-isolated Gram/Schur estimates.

## Exact ledger

- denominator power: `6`;
- Carlson loss: `log^4`;
- multiplicity-square loss: one extra `log`;
- total logarithmic loss: exactly `log^5`;
- polynomial dyadic contribution: at most `-5` because `q(sigma) <= 1`;
- strict negative total exponent: decay;
- equality: critical, with no decay claim.

## Remaining explicit-formula gap

This slice controls the genuine cubic coefficient-square tail. It does not yet
turn that L2 capacity into a bound for the smoothed explicit-formula remainder.
The next theorem must supply the kernel-side Cauchy-Schwarz or orthogonality
factor at heights between `m^gammaLow` and `m^alpha`, while preserving the
reciprocal-cubic gain and avoiding the known unsmoothed contour factor
`m^(1-beta) * (1+log m)^2`.

No unconditional Omega theorem or RH consequence is claimed.

## Audit surface

The production module exposes three definitions and nine theorems. Contract
contains twelve exact typed examples; AxiomAudit prints all nine theorem axiom
sets; the allowlist registers all nine theorem names.
