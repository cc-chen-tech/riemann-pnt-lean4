# Reciprocal moving-extension absolute-mass design

## Problem

Controlling a moving-cluster extension requires a bound for the sum of kernel
norms.  A bound for the norm of the complete signed sum is insufficient,
because an arbitrary selected subset can remove cancellation.

## Reciprocal absolute bound

For every finite low layer with `Re rho <= sigma`, prove

```text
sum rho in layer, norm(kernel rho)
  <= x^(sigma-1) * globalReciprocalZeroMultiplicity(H x).
```

After division by `x^(beta-1)`, the polylogarithmic reciprocal mass is absorbed
whenever `sigma - beta + epsilon < 0`.  The high layer converges to the Carlson
boundary mass.  Conjugation doubles that boundary contribution and the
strictly-left real slice is negligible.

Every moving extension is a subset of the complete fixed-cluster outside
zero set.  Its signed absolute value is therefore bounded by the complete
outside absolute mass, yielding the coefficient `2*boundaryMass + delta`
without a cancellation assumption.

## Claim boundary

This module provides the reciprocal extension estimate.  The automatic
actual-package moving Omega theorem that consumes it is intentionally left to
the next bounded stack.
