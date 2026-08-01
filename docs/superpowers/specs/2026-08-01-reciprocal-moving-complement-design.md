# Reciprocal moving-complement design

## Problem

The existing moving right-edge complement theorem uses a two-height low/high
majorant.  Its low-height polynomial loss contributes to the `beta > 2/3`
window in the automatic moving Omega chain.

## Reciprocal replacement

Every visible positive zero outside
`movingRightEdgeExceptionalCluster H tau x` has real part strictly below
`tau`.  Therefore its complete positive sum satisfies

```text
norm(outside sum) <= x^(tau-1) * globalReciprocalZeroMultiplicity(H x).
```

The global reciprocal mass is `O(log^2 H)`.  For polynomially bounded `H`,
division by `x^(beta-1)` tends to zero whenever a positive epsilon satisfies
`tau - beta + epsilon < 0`.  Conjugation doubles the positive bound, while the
real-ordinate outside tail is exactly zero because the moving cluster captures
all real-ordinate zeros.

## Claim boundary

This module proves negligibility of the moving-cluster complement.  It does
not yet replace the absolute-mass estimate used for the moving extension
inside the cluster; that is a separate next step.
