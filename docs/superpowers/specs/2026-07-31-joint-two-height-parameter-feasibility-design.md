# Joint two-height parameter feasibility design

## Goal

For every target real part `beta` with `2 / 3 < beta < 1`, construct one
common set of numerical parameters that simultaneously closes:

- the balanced low global-layer exponents;
- the balanced target-amplitude Carlson strip exponents;
- the contour floor `1 - beta < alpha`;
- the polynomial-height restriction `alpha <= 1`.

## Scope

This is a real-arithmetic interface only. It does not change the explicit
formula, complementary-zero decomposition, sharp oscillation witnesses, or
VK-edge modules.

## Construction

Write

`threshold = (3 * beta - 1) / 2`.

Choose `sigma` strictly between `1 / 2` and `threshold`. Carlson's balanced
slope

`a(sigma) = q(sigma)^2 / (q(sigma) + 1)`

is strictly between zero and `1 / 2`. Hence

`a(sigma) * (1 - beta) + sigma - beta < 0`.

Choose `tau` strictly between `sigma` and

`beta - a(sigma) * (1 - beta)`.

There are then three strict upper bounds above the contour floor:

- `1`;
- `2 * (beta - sigma)`, for the low global layer;
- `(beta - tau) / a(sigma)`, for the high Carlson strip.

Choose `alpha` between `1 - beta` and the minimum of those bounds. Set

- `gammaLow = alpha / 2`;
- `gammaHigh = carlsonTwoHeightBalancedCut sigma alpha`;
- each epsilon to half the negative of its common balanced exponent.

## Lean interface

The main theorem returns the seven witnesses

`sigma tau alpha gammaLow gammaHigh epsilonLow epsilonHigh`

together with all ordering, contour, cut, positivity, and strict-margin
facts required by the existing low-layer and Carlson transfer theorems.

## Audit boundary

The contract checks only the new theorem. The axiom audit must report the
standard Lean classical axioms already accepted in this repository and no
new analytic hypothesis.

