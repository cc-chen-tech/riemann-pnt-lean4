# Exact triangle averaging is required for desmoothing

## Existing forward differences already center by translation

Let

```text
forwardDiff2_h F(u) = F(u + 2*h) - 2*F(u + h) + F(u).
```

The centered logarithmic second difference is not a new kernel:

```text
F(t + h) - 2*F(t) + F(t - h)
  = forwardDiff2_h F(t - h).
```

In the multiplicative variable, instantiate the existing forward theorem at

```text
x0 = x * exp(-h).
```

Its three points become

```text
x0,
x0 * exp(h)   = x,
x0 * exp(2*h) = x * exp(h).
```

Thus a small adapter is sufficient to reuse the current cubic forward kernel
and three-point explicit formula at the centered window
`[x*exp(-h), x*exp(h)]`.

## Why the endpoint sandwich is insufficient

Suppose the second Riesz difference is denoted by `Q_psi(x,h)`.  A sandwich of
the form

```text
psi(x*exp(-h)) <= Q_psi(x,h) <= psi(x*exp(h))
```

is useful for one-sided estimates of `psi`, but it does not directly desmooth
the PNT error

```text
E(x) = psi(x) - x.
```

The centered second difference of the continuous main term is

```text
Q_main(x,h)
  = x * C_h(1),

C_h(1)
  = (exp(h) - 2 + exp(-h)) / h^2.
```

Subtracting `Q_main` from the endpoint sandwich gives only

```text
Q_E(x,h)
  <= E(x*exp(h))
     + x * (exp(h) - C_h(1)),

E(x*exp(-h))
  <= Q_E(x,h)
     + x * (C_h(1) - exp(-h)).
```

For small positive `h`, both deterministic discrepancies have order `x*h`.
After normalization by the target amplitude `x^beta/|rho0|`, the polynomial
size is

```text
x^(1-beta) * h.
```

With `h = x^(-d)`, this is

```text
x^(1-beta-d).
```

It decays only if

```text
d > 1 - beta.
```

The direct-L2 smoothing choice

```text
d = (1 - lambda*(1-beta)) / 8
```

does not satisfy this throughout `beta > 2/3`.  Therefore the endpoint
sandwich cannot serve as the general desmoothing theorem for the proposed
short-interval result.

This obstruction is independent of the Carlson `1/|rho|^2` gain.  It comes
from comparing the smoothed main term to the wrong endpoint main term.

## The exact identity removes the mismatch

Let `t = log x`.  Define the logarithmic second Riesz primitive by

```text
G(t)
  = (1/2) * sum_n Lambda(n) * max(t - log n, 0)^2.
```

Its second derivative, in the interval-integral/distributional sense, is

```text
G''(t) = psi(exp t).
```

The elementary second-difference identity is

```text
(G(t+h) - 2*G(t) + G(t-h)) / h^2
  = integral_{-1}^1
      (1 - |u|) * psi(exp(t+h*u)) du.
```

Apply the same identity to the continuous main primitive.  Since

```text
integral_{-1}^1 (1 - |u|) * exp(t+h*u) du
  = x * C_h(1),
```

subtraction occurs inside the average:

```text
Q_E(x,h)
  = integral_{-1}^1
      (1 - |u|)
      * (psi(x*exp(h*u)) - x*exp(h*u)) du

  = integral_{-1}^1
      (1 - |u|) * E(x*exp(h*u)) du.
```

There is no additive `O(x*h)` term.

## Point extraction with the correct normalization

The triangle kernel is nonnegative and has mass one.  Hence

```text
|Q_E(x,h)|
  <= sup_{|u| <= 1} |E(x*exp(h*u))|.
```

If

```text
|Q_E(x,h)| > c * x^beta / |rho0|,
```

there is `u` with `|u| <= 1` such that, for

```text
x_point = x * exp(h*u),
```

```text
|E(x_point)| > c * x^beta / |rho0|.
```

Since

```text
x^beta >= exp(-beta*h) * x_point^beta,
```

one obtains

```text
|E(x_point)|
  > c * exp(-beta*h) * x_point^beta / |rho0|.
```

Only the multiplicative factor `exp(-beta*h) -> 1` consumes strict constant
margin.  No polynomial `x^(1-beta-d)` loss remains.

## Scalar hinge theorem needed by Lean

The cleanest formal proof starts with one scalar hinge.  For `a,t in Real` and
`h > 0`, define

```text
hinge2(a,t) = (1/2) * max(t-a,0)^2.
```

Prove

```text
(hinge2(a,t+h) - 2*hinge2(a,t) + hinge2(a,t-h)) / h^2
  = integral_{-1}^1
      (1 - |u|) * indicator(a <= t+h*u) du.
```

There are three geometric cases:

```text
a <= t-h,
t-h < a < t+h,
t+h <= a.
```

The middle case splits once at

```text
u0 = (a-t)/h in (-1,1).
```

After the scalar identity, sum over the finite set of integers `n <= x*exp h`
and exchange the finite sum with the interval integral.  Endpoint conventions
at `a = t+h*u` affect a set of measure zero only.

The repository already contains a quadratic-hinge module and a Fejer triangle
kernel module.  The new production theorem should reuse those objects rather
than introduce a second incompatible definition.

## Required actual-production chain

The implementation should expose equivalents of:

```text
secondLogCenteredDifference_eq_forwardDifference_shift
quadraticHinge_centeredDifference_eq_triangleIntegral
secondRiesz_centeredDifference_eq_trianglePsi
continuousMain_centeredDifference_eq_triangleMain
secondRieszError_centeredDifference_eq_trianglePNTError
trianglePNTError_abs_le_intervalSup
trianglePNTError_large_imp_exists_point
centeredWindow_subset_shortPowerInterval
```

The current forward cubic residue and contour factorization can then be reused
at the shifted base point `x*exp(-h)`.

## Interaction with the explicit formula

The pole residue must be identified with `Q_main(x,h)` before point extraction.
The zero residues give

```text
-sum_rho multiplicity(rho)
  * x^rho / rho * C_h(rho).
```

The real-axis, trivial-zero, and contour pieces remain explicit remainder
terms.  The exact triangle identity changes only the desmoothing step; it does
not make those analytic remainders disappear.

## A restricted fallback

The endpoint sandwich could still work in the narrower parameter range

```text
d > 1-beta.
```

That range may be useful as a debugging or intermediate theorem.  It must not
replace the requested full `beta > 2/3` result, and it must state the additive
main mismatch explicitly.

## Nonclaims

This note does not claim:

- that the exact triangle identity is already present as a production theorem;
- that the current quadratic-hinge definition has exactly the normalization
  written above;
- that the existing forward explicit formula has no additional endpoint
  hypotheses after shifting;
- that the pole, trivial-zero, and contour terms have already been assembled;
- that a large triangle average gives both signs rather than absolute value.
