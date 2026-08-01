# Stack 174: reciprocal-height contour obstruction

## Question

Can the unsmoothed selected-height explicit formula transfer a moving zero
package at the natural single-zero scale

```text
x^(beta - 1) / H(x)
```

by choosing a better polynomial truncation height `H(x) = x^alpha`?

## Audited calculation

The leading proved relative contour majorant is

```text
10 C x^(-alpha) (1 + log x)^2.
```

After division by `x^(beta - 1) / x^alpha`, the height exponent cancels:

```text
10 C (1 + log x)^2 x^(1 - beta).
```

For `C > 0` and every `beta < 1`, this tends to positive infinity.  The full
two-power selected contour majorant therefore also diverges under the same
normalization and cannot serve as a negligible residual at this scale.

## Consequence

Changing only the dynamic truncation height cannot close the moving-package
`1 / |rho|` lower transfer with the current unsmoothed contour estimate.  A
viable next route must change one of the structural inputs:

- use a smoothed explicit-formula kernel with a stronger remainder;
- keep a bounded-height target package;
- or prove cancellation in the actual contour remainder beyond the displayed
  absolute majorant.

## Claim boundary

This is a theorem about the proved contour majorant, not a lower bound for the
actual remainder.  It does not rule out sharper contour analysis, smoothing,
or a different explicit-formula kernel, and it does not imply RH or its
negation.
