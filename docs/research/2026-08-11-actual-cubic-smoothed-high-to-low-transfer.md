# Actual cubic smoothed high-to-low transfer

## Scope

This slice proves the actual-zeta zero-energy component required by a
third-order smoothed explicit formula. It does not modify Sharp oscillation,
half-isolated Gram/Schur arguments, VK-edge modules, or complementary-bound
files.

The repository's currently constructed smoothed Perron formula is second order
and has zero kernel `1 / rho^2`. The cubic Carlson capacity instead matches
the coefficient-square scale of a third-order kernel:

`multiplicity(rho)^2 * x^(2 Re rho) / |rho|^6`.

Accordingly, this PR does not relabel the second-order formula as cubic. It
closes the zero-energy high-to-low theorem needed before a genuine third-order
Perron/contour construction can consume the capacity.

## Exact decomposition

For the dyadic cut

`N_gamma(m) = floor(log(m^gamma) / log 2)`,

define the finite strip energy through that cut by summing the actual cubic
capacity over blocks `0, ..., N_gamma(m)`. For two ordered cuts,

`N_from(m) <= N_to(m)`,

the formal identity is

`E_to(m) = E_from(m) + E_(from,to](m)`.

The boundary block belongs to the low layer; the intervening range starts at
`N_from(m) + 1`, exactly as in the diagonal tail from PR #436.

## Tail domination and normalization

For `m >= 1`, Carlson summability gives

`E_(from,to](m) <= sum_{n > N_from(m)} actualCapacity(m,n,S)`.

This remains valid after deleting any finite zero set `S`; no new density
estimate is proved for `S`. Multiplication by the nonnegative target factor
`m^(-2 beta)` preserves the inequality. Therefore every diagonal-tail limit
from PR #436 yields

`m^(-2 beta) * E_(from,to](m) -> 0`.

No extra logarithmic or multiplicity loss is introduced here. The inherited
ledger remains:

- denominator power `6`;
- Carlson loss `log^4`;
- multiplicity-square loss one additional `log`;
- total loss exactly `log^5`;
- exponent `2*(tau-beta) + gamma*(q(sigma)-6)`;
- strict negativity gives decay;
- equality is critical and no decay is claimed.

## Joint two-height output

For each `2/3 < beta < 1`, one parameter package supplies two simultaneous
actual high-to-low decompositions at outer height `alpha`:

- low detector `gammaLow -> alpha`;
- Carlson balance cut `gammaHigh -> alpha`.

In both cases the intervening normalized energy tends to zero. The result is
an actual-zeta, finite-deletion-stable L2 capacity theorem, not an abstract
kernel facade.

## Remaining analytic gap

The next independent slice must construct or expose a genuine third-order
smoothed Perron/explicit-formula kernel and prove that its zero coefficients
are measured by this cubic energy. Its contour estimate must preserve the
reciprocal-cubic gain; the known unsmoothed normalized factor

`m^(1-beta) * (1 + log m)^2`

cannot be reused. This PR alone does not prove a full PNT remainder transfer,
an Omega theorem, or RH.

## Audit surface

Production exposes four definitions and eleven theorems. Contract contains
fifteen exact typed examples. AxiomAudit prints all eleven theorem axiom sets,
and the allowlist registers all eleven names.
