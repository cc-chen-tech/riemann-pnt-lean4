# Dynamic boundary gap versus Carlson density cost

## Exact exponent identity

For an outside-zero layer whose real parts are bounded by
`beta - delta`, normalization by the target amplitude leaves

```text
targetAmplitudeStripEndpointExponent beta (beta - delta) densityCost
  = densityCost - delta.
```

Therefore the layer decays exactly when `densityCost < delta`.

For Carlson's classical polynomial-height input this becomes

```text
alpha * (4 * sigma * (1 - sigma)) < delta.
```

If the contour also requires `1 - beta < alpha`, then necessarily

```text
(4 * sigma * (1 - sigma)) * (1 - beta) < delta.
```

This lower bound is independent of the scale.

## Actual dynamic package

The module uses classical choice to select, at each natural scale, the
positive finite-complement gap proved by the dynamic boundary package
module.  Its specification is about actual positive nontrivial zeta zeros
visible below the selected height.

Instantiating the existing moving-gap barrier shows that, with a fixed
positive Carlson slope, simultaneous contour admissibility and normalized
density decay force the selected actual-zero gap to be eventually bounded
below by the fixed constant

```text
(4 * sigma * (1 - sigma)) * (1 - beta).
```

In particular, a selected gap tending to zero is incompatible with that
single aggregated density estimate.

## Consequence for the research route

Absorbing all currently visible zeros on the line `re = beta` repairs the
fixed-package contradiction, but pointwise finiteness alone does not close
the normalized complementary remainder.  A one-bucket Carlson aggregate
still demands eventual fixed isolation.

The next viable route is dynamic real-part layering whose density cost can
vary with the strip, rather than treating the whole complement with one
fixed positive density exponent.  This module does not assert such a
layered decay theorem, an unconditional Omega result, or RH.
