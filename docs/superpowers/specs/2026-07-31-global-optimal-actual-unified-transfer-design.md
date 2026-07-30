# Global Optimal Actual Unified Transfer Design

## Goal

Run the actual Pintz-Carlson-explicit-formula transfer at a height exponent
arbitrarily close to the ceiling obtained by globally optimizing the density
threshold and strip endpoint.

## Inputs

- `2 / 3 < beta < 1`;
- `1 / 2 < theta < beta`;
- `0 < eta < globalCeiling(beta, theta) - (1 - beta)`;
- a conjugation-invariant base cluster;
- a global positive nontrivial-zero bound `rho.re <= theta`.

## Construction

1. Fix `sigma` to `jointTwoHeightOptimalDensityThreshold beta theta`.
2. Use its optimizer specification to derive `1 / 2 < sigma < theta < beta`.
3. Rewrite the global eta gap as the fixed-sigma prescribed-cap eta gap.
4. Invoke the actual near-optimal selected-good-height transfer from stack55.
5. Rewrite its exponent exactly as
   `alpha = jointTwoHeightGlobalOuterExponentCeiling beta theta - eta`.

## Result

For every uniform natural-point good-height selection, a visible-cluster
target-amplitude witness implies:

- natural-point relative Chebyshev error convergence to zero;
- a far witness for the actual relative error at half the target-zero
  amplitude.

The theorem also returns the canonical optimizer, its balance property, the
selected endpoint, and all height-ordering facts.

## Boundary

The visible-cluster witness remains explicit. This theorem optimizes the
upper/remainder truncation mechanism but does not prove finite-cluster
anti-cancellation.
