# Stack 188: Actual second-Riesz to Chebyshev-psi sandwich

## Goal

Sum Stack 187's quadratic hinge kernel against the actual nonnegative von
Mangoldt coefficients and remove second-order Riesz smoothing.

## Main theorem

For `x>0` and `h>0`, set

```text
y = x exp(h),
z = x exp(2h).
```

Then

```text
chebyshevPsi(x)
  <= (Psi_2(z) - 2 Psi_2(y) + Psi_2(x)) / h^2
  <= chebyshevPsi(z).
```

The proof represents all three second Riesz means on the common finite support
`1 <= n <= floor(z)`.  Terms already active at `x` contribute exactly one
after normalization; all other terms contribute between zero and one.

## Significance

This is the actual two-difference de-smoothing theorem needed to transfer the
cubic explicit formula of Stack 186 back to ordinary PNT error.  It preserves
the natural logarithmic window `[x, x exp(2h)]` without inserting a conditional
comparison interface.

## Claim boundary

The theorem de-smooths the arithmetic second Riesz mean.  Bounds for the
twice-differenced cubic contour remainder and the resulting zero-forced
ordinary PNT oscillation remain to be proved.
