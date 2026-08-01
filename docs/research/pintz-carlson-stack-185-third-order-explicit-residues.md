# Stack 185: Actual cubic explicit-formula residues

## Goal

Shift the cubic Perron kernel from a scalar inversion object to an actual zeta
explicit-formula residue object on a finite rectangle in `Re(s)>0`.

## Construction

Start with the repository's finite first-order principal-part decomposition

```text
explicitFormulaIntegrand = analytic remainder + sum_p r_p/(z-p).
```

Divide by `z^2`.  Since the rectangle is separated from zero, the identity

```text
r / (z^2 (z-p))
  = (r/p^2)/(z-p) - (r/p^2)/z - (r/p)/z^2
```

shows that only the first term remains a pole inside the rectangle.  The two
origin terms are absorbed into the analytic remainder.

## Main output

The cubic boundary integral equals a finite residue sum whose coefficients are

```text
x                                      at p = 1,
-analyticMultiplicity(p) * x^p / p^3  at a nontrivial zeta zero.
```

Thus the correct reciprocal-cube zero scale is now obtained from the actual
zeta principal parts, not stipulated by an abstract residue interface.

## Claim boundary

This stack proves the closed rectangular residue identity.  It does not yet
rewrite the boundary as right line minus a named cubic contour remainder,
combine that shift with Stack 184's second Riesz approximation, or perform the
two finite differences needed to recover the ordinary `1/p` scale.
