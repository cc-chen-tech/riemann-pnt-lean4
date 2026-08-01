# Stack 178: Third-order Perron kernel foundation

## Goal

Separate the denominator order of a Perron kernel from the decay order of its
integrated vertical tail, and construct the smallest kernel order compatible
with the `H^-2` input required by the quadratic-kernel moving PNT certificate.

## Correct order bookkeeping

The existing second-order explicit-formula integrand has denominator `s^2`.
Its vertical absolute tail is modeled by

```text
integral_H^infinity t^-2 dt = H^-1.
```

It therefore remains a first-order truncation remainder in the terminology of
Stack 175.  It does not satisfy the quadratic `H^-2` hypothesis merely because
the integrand contains `s^2`.

The next kernel has denominator `s^3`.  Its scalar tail is

```text
integral_H^infinity t^-3 dt = 1 / (2 * H^2).
```

Thus a third-order Perron kernel is the minimal denominator order that can feed
the abstract quadratic-remainder transfer without losing a power before
de-smoothing.

## Auditable theorem chain

1. `thirdOrderExplicitFormulaIntegrand` divides the repository's actual
   second-order zeta integrand by one additional factor of `s`.
2. `thirdOrderExplicitFormulaIntegrand_eq_explicitFormulaIntegrand_div_sq`
   identifies it with the ordinary explicit-formula integrand divided by
   `s^2`, hence with the logarithmic-derivative kernel having total denominator
   `s^3`.
3. `simplePoleTerm_div_sq_eq` gives the exact partial fraction needed when a
   regularized first-order simple-pole term is divided by `s^2`.  Its pole at
   `p` acquires coefficient `r / p^2`; the remaining poles are at the Perron
   origin and belong to the real-axis correction package.
4. `integral_Ioi_rpow_neg_three_eq_inv_sq` proves the scalar tail identity
   `integral_H^infinity t^-3 dt = 1 / (2 * H^2)` for `H > 0`.

## Claim boundary

This stack does not prove a third-order Perron inversion theorem, a rectangle
shift for the cubic kernel, or an actual `H^-2` bound for the zeta contour
remainder.  It also does not yet define the corresponding second Riesz mean or
control the losses from two finite differences.  Consequently it does not
close the moving-main witness and does not prove an unconditional Omega result.

The next analytic step is to recover the second Riesz mean from the cubic
kernel, shift its contour with zero coefficients proportional to
`-m(rho) * x^rho / rho^3`, and quantify both de-smoothing differences before
connecting the result to the Stack 176 certificate.
