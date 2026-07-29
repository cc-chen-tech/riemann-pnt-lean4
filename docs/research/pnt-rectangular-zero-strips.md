# Two-dimensional zero strips for the PNT kernel

## Why real-part strips are insufficient

For one simple zeta zero, the exact relative explicit-formula kernel is

```text
x^(Re rho - 1) / |rho|.
```

A real-part upper endpoint controls the numerator.  It does not justify
discarding `|rho|` from the denominator.  In particular, positivity of the
ordinate alone does not imply the unproved shortcut `|rho| >= 1`.

## Rectangular layer data

`PositiveZeroRectangleInput` attaches three parameters to every finite layer:

```text
sigma i           strict lower real-part endpoint used by Carlson;
tau i             upper real-part endpoint used by the power kernel;
ordinateFloor i   positive lower ordinate used by the denominator.
```

For every zero in layer `i`, the verified pointwise bound is

```text
|K_x(rho)| <= x^(tau i - 1) / ordinateFloor i.
```

Analytic multiplicity is then counted exactly once by
`zeroDensityCount (sigma i) T`.

## Resulting budget

The positive-ordinate zero sum is bounded by

```text
sum_i
  x^(tau i - 1) / ordinateFloor i
    * N(sigma i, T).
```

Conjugation gives twice this budget for nonreal zeros, while real-ordinate
zeros remain as an explicit residual.

The main declarations are:

```text
norm_pntRelativeSimpleZeroKernel_le_rectangle
PositiveZeroRectangleInput.sum_norm_layer_le
PositiveZeroRectangleInput.norm_positive_sum_le
PositiveZeroRectangleInput.norm_full_sum_le
```

## Next step

Construct a dynamic finite rectangle grid whose ordinate floors and real-part
endpoints depend on the truncation height, apply Carlson at each `sigma i`,
and optimize the common height against the contour remainder.  That step must
also isolate the finitely many zeros below the first positive ordinate floor.
