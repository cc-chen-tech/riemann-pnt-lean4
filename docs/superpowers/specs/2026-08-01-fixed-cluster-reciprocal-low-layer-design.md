# Fixed-cluster reciprocal low-layer design

## Objective

Expose the reciprocal-mass low-layer argument for an arbitrary fixed visible
cluster `S`.  The previous theorem was specialized to the moving equal-real-
part package and could not be used by the finite-cluster mean-square witness.

## Estimate

For every selected outside-cluster layer in `Re rho <= sigma`, retain the
factor `1 / |rho|` inside the sum and bound it by the global
multiplicity-weighted reciprocal-zero mass.  This mass is `O(log^2 H)`, so
after normalization by `x^(beta-1)` the power term is

```text
x^(sigma-beta),
```

not the old `x^(sigma-beta+alpha)`.

Hence the strict decay margin is

```text
sigma - beta + epsilon < 0,
```

independently of the polynomial selected-height exponent `alpha`.

## Role in the larger chain

This is the missing analytic input for rebuilding the fixed-cluster Carlson
boundary residual.  Once installed there, the actual equal-real-part package
mean-square sign alternative can use `sigma < beta` instead of the older
balanced threshold `(1+sigma)/2 < beta`.

This module itself proves only low-layer decay.  It does not yet claim the full
residual, sign alternative, an unconditional Omega theorem, or RH.
