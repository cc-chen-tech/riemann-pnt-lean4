# Optimized-Height Unified Transfer

## Goal

Use the exact Stack119/120 optimized good-height schedule throughout the
sigma-only variable-boundary transfer. The height, visible zero package,
running right edge, actual explicit-formula remainder, and zero-free envelope
must all refer to the same function.

## Construction

For `sigma` in `(1/2, 1)`, reuse the existing automatic parameters:

- `alpha = actualDynamicBoundaryBalancedGoodHeightExponent sigma`;
- `epsilon = sigmaOnlyRunningBoundaryEpsilon sigma`;
- `beta0 = sigmaOnlyRunningBoundaryBeta0 sigma`.

Let `H` be the certified pointwise cost optimizer from Stack119 and let

```text
beta(x) = naturalRunningVisibleZeroBoundaryReal H beta0 x.
```

The existing sigma-only parameter theorem supplies positivity, the strict
remainder margin, the Carlson margin, and the real-ordinate right-edge bound.
Stack119 supplies the polynomial height upper bound and divergence. Stack120
supplies the actual remainder certificate. Generic running-boundary theorems
supply monotonicity and the indexed visible right edge.

## Outputs

The first facade applies
`actualMonotoneVariableBoundaryUnifiedUpperSignedOmega` and returns the
eventual Carlson-scale PNT upper bound plus conditional signed witnesses.

The second facade assumes a common candidate zero-free envelope and effective
log-gap divergence. It transfers the envelope to `H`, derives zero-free decay
for `beta`, and squeezes the relative PNT error to zero while retaining the
same conditional signed witnesses.

## Boundary

Positive and negative main-cluster witnesses remain explicit assumptions.
The theorem is not unconditional Omega and does not imply RH. It does not
modify Sharp, VK-edge, or complementary-zero modules.
