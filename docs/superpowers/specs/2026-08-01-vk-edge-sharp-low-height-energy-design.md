# VK-Edge Sharp Low-Height Energy Design

## Scope

This branch supplies only the genuine-zeta analytic lower-bound input on the
Sharp side. It does not modify Carlson estimates, zero-set growth, witness
extraction, or final contradiction code.

The first milestone is a cofinal theorem for one fixed off-line zeta zero with
real part greater than `2 / 3` and the empty recorded set. The selected
finite-zero height is

\[
T_{\mathrm{low}} \asymp \exp(\gamma_{\mathrm{low}} a),
\]

while the outer explicit-formula height is recorded separately as

\[
H = \exp(\alpha a), \qquad \gamma_{\mathrm{low}} < \alpha.
\]

## Analytic decomposition

The existing all-real-sample explicit formula gives a raw error at every
sample `exp y` after selecting a good height in `[A, A + 1]`. Set
`A = exp (gammaLow * a)` and normalize by `exp (-beta * y)` on
`y in [a, (1 + epsilon) * a]`. The three relevant exponential rates are:

- finite-height term: `(1 - beta) * (1 + epsilon) - gammaLow`;
- interpolation term: `gammaLow - beta`;
- closed and logarithmic terms: `-beta`.

Thus the normalized remainder tends to zero under

```text
0 < gammaLow,
(1 - beta) * (1 + epsilon) < gammaLow,
gammaLow < beta.
```

The existing empty-cluster residual lower bound is uniform in the truncation
height. Combining it with this generalized remainder estimate and the existing
full-complement transfer yields positive Gaussian energy for the actual finite
zeta-zero complement at the selected low height.

## Public endpoints

1. `eventually_exists_uniform_goodHeight_normalized_powerHeight_proportional_window_remainder_lt`
   selects the genuine good height near `exp (gammaLow * a)` and controls the
   normalized explicit-formula error uniformly on the proportional window.

2. `exists_eventually_emptyClusterLowHeightFullMovingGaussianSecondMoment_gt`
   applies that selector to one actual off-line zeta zero with `2 / 3 < rho.re`,
   proves a fixed positive energy lower bound cofinally in `Y`, and records
   `Tlow <= exp (alpha * log Y)` separately from the low-height localization.

## Finite recorded sets

No arbitrary-`S` theorem is claimed in this milestone. If `Told >= rho.im`,
`rightHigherExclusionSet S Told sigma Tlow` removes the original zero pair that
supplies the known lower bound. A repeatable `S`-relative theorem therefore
requires a new genuine-zeta input showing that another right/high zero signal
remains after each deletion. This cannot be obtained by renaming the existing
empty-cluster theorem.

## Verification

Contracts lock exact public types. Dedicated and central axiom audits must
permit only standard Lean/Mathlib axioms. Focused builds run with one global
Lean process before any broader baseline check.
