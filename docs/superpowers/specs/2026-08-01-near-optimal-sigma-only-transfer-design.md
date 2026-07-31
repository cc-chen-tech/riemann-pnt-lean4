# Near-optimal sigma-only transfer design

## Scope

Stack154 proves that the reciprocal contour-height outer exponent has exact
infimum `1 - beta`.  Stack153 supplies a sigma-only running-boundary transfer,
but chooses a fixed midpoint window.  This slice connects the two results.

The slice adds only:

- `ZeroDensityLayerBudgetNearOptimalSigmaOnlyTransfer.lean`;
- its public contract and axiom audit;
- this design and the matching implementation plan.

It does not modify the complementary-zero, Sharp oscillation, or VK-edge
modules.

## Construction

For the automatic reciprocal anchor `beta0(sigma)` and a parameter
`0 < delta < beta0`, choose

```text
inner = 1 - beta0 + delta / 2,
outer = 1 - beta0 + delta.
```

The Stack154 contour-window theorem supplies:

- `0 < inner <= 1`;
- `1 - beta0 < inner < outer`;
- `outer < 1`;
- the selected-height ceiling and cofinality;
- the actual natural-point contour-remainder certificate.

The reciprocal low-layer margin remains the Stack153 margin

```text
sigma - beta0 + reciprocalSigmaOnlyEpsilon sigma < 0,
```

which is independent of the height exponent.  Therefore the near-optimal
height can be substituted directly into the reciprocal variable-boundary
transfer.

## Public result

The final facade provides the same PNT relative-error upper bound and the same
conditional signed transfer as Stack153, but with an outer truncation exponent
exactly `delta` above the contour floor.  A separate existence theorem proves
that every positive tolerance admits such an actual selected-height window.

## Claim boundary

The signed conclusion still assumes positive and negative visible-main
witnesses.  This slice does not prove anti-cancellation, an unconditional
Omega theorem, or RH.  It proves near-optimal truncation within the existing
audited transfer chain.
