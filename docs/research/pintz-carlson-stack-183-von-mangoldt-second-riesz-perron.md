# Stack 183: Von Mangoldt second Riesz Perron formula

## Goal

Insert actual von Mangoldt coefficients into Stack 182's cubic Perron
truncation and define the corresponding arithmetic second Riesz mean.

## Arithmetic object

```text
Psi_2(x) = sum_{1 <= n <= floor(x)}
  Lambda(n) * log(x/n)^2 / 2.
```

The finite support is explicit, and positivity of the von Mangoldt
coefficients permits summing the scalar kernel errors without cancellation.

## Main estimate

For `x,c,W > 0`, the finite-height cubic Perron sum satisfies

```text
norm(truncated cubic von Mangoldt integral - Psi_2(x))
  <= sum_{1 <= n <= floor(x)}
       Lambda(n) * (x/n)^c / (8 pi^3 W^2).
```

The proof first establishes a general finite nonnegative-coefficient theorem,
then identifies the quadratic ramp with `log(x/n)^2/2` on the finite support.

## Significance

The quadratic `W^-2` remainder now acts on the actual PNT coefficient object,
not just a scalar kernel or abstract certificate.  This is the arithmetic
input needed before replacing the finite sum by the full logarithmic
derivative of zeta.

## Claim boundary

This stack uses the finite von Mangoldt support.  It does not yet interchange
the cubic integral with the full Dirichlet series on `Re(s)>1`, perform the
cubic contour shift, or control two finite differences of the contour error.
No unconditional Omega theorem is claimed.
