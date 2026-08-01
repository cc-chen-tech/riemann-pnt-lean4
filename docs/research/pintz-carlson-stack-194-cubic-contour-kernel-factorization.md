# Stack 194: cubic contour kernel factorization

## Result

The normalized logarithmic second difference of the actual cubic Perron
integrand is identified pointwise with

```text
first-order explicit-formula integrand
* ((exp(h s) - 1) / (h s))^2.
```

This is exactly the same multiplier isolated for the zero residues in Stacks
192 and 193.  The result therefore places the zero sum and contour remainder
on one de-smoothed kernel.

A pathwise theorem moves this identity through a finite interval integral.
Its only analytic hypotheses are the interval integrability of the three
cubic integrands and nonvanishing of the contour parameterization.

## Mathematical role

The contour remainder is no longer an unrelated error term: after the same
second difference it becomes an integral of the classical first-order
explicit-formula kernel with the controlled cubic multiplier.  This is the
correct starting point for a shared Pintz/Carlson bound.

## Claim boundary

Automatic interval integrability from the rectangle boundary hypotheses and
a quantitative norm bound for the resulting contour integral are not yet
proved.  No unconditional oscillation theorem or RH is claimed.
