# Moving-sigma Carlson input for the PNT transfer

## Purpose

The existing Carlson theorem has the quantifier shape

```text
for each fixed sigma, there exist a coefficient and an eventual cutoff.
```

It does not imply the same estimate after substituting a threshold
`sigma = sigma(x)`.  The coefficient and cutoff can depend on `sigma`, so a
moving threshold requires a separate uniformity theorem.

`ZeroDensityLayerBudgetPNTMovingSigmaTransfer.lean` records the exact uniform
input needed by the explicit formula without claiming that Carlson's current
fixed-threshold theorem already supplies it.

## The transfer chain

`UniformMovingSigmaHybridDensityDecay rate inputAtHeight` requires density
decay for every height selection in the unit interval above the prescribed
Pintz--Carlson base height.  This quantifier order is deliberate: the good
height is selected by the explicit formula, so the density theorem may not
choose a different favorable height afterwards.

The resulting chain is:

```text
uniform moving-sigma hybrid density decay
  -> selected good-height moving-sigma schedule
  -> complete relative explicit-formula budget tends to zero
  -> actual relative chebyshevPsi0 error tends to zero.
```

The final declaration is

```text
exists_movingSigma_relativeChebyshevPsi0Error_tendsto
```

## Fixed thresholds remain available

`uniformMovingSigmaHybridDensityDecay_of_fixed` proves that the established
fixed-threshold density limit is a special case.  In particular, the current
two-strip Carlson transfer is preserved.

## Remaining analytic obligation

To obtain a genuinely moving Carlson profile, one must prove a zero-density
estimate whose constants and eventual cutoff are uniform over the threshold
range visited by the profile.  This file does not infer that uniformity from
pointwise fixed-`sigma` estimates and does not claim an improved numerical PNT
error rate.
