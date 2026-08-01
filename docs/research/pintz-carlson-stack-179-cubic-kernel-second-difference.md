# Stack 179: Cubic-kernel second-difference transfer

## Goal

Connect the cubic Perron zero coefficient to the ordinary explicit-formula
zero coefficient by the two logarithmic finite differences required to remove
second-order Riesz smoothing.

## Exact calculation

For

```text
F_rho(u) = exp(rho * u) / rho^3,
```

the second forward difference is

```text
F_rho(u + 2h) - 2 F_rho(u + h) + F_rho(u)
  = exp(rho * u) * (exp(rho * h) - 1)^2 / rho^3.
```

After normalization by `h^2`, this becomes

```text
exp(rho * u) / rho
  * ((exp(rho * h) - 1) / (rho * h))^2.
```

Thus two finite differences recover the correct `exp(rho * u) / rho` zero
scale exactly.  All de-smoothing distortion is isolated in the explicit local
factor

```text
K(rho, h) = ((exp(rho * h) - 1) / (rho * h))^2.
```

The coefficient-linear theorem applies the identity directly to signed
analytic multiplicity coefficients.

## Why this matters

Stack 178 showed that the cubic denominator has the scalar `H^-2` vertical
tail needed by the quadratic-remainder transfer.  This stack shows that the
same cubic denominator does not lose the desired `1 / rho` oscillation scale
when the corresponding second Riesz mean is de-smoothed twice.

## Claim boundary

This is an exact zero-term calculation.  It does not yet prove a Perron formula
for the second Riesz mean, does not compare finite differences of that mean to
`chebyshevPsi`, and does not bound the finite-differenced contour remainder.
It also does not yet prove a uniform lower bound for `K(rho, h)` over a moving
zero cluster.  Those are the remaining analytic and local-uniformity inputs;
no unconditional Omega theorem is claimed here.
