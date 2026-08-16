# Actual cubic second-difference kernel bridge

## Purpose

The two-height route needs one actual kernel to perform two apparently
different jobs:

- preserve the retained low cluster at the exact reciprocal-zero scale;
- gain two additional reciprocal heights on the high tail.

For the standard relative centered second difference of the cubic Perron
residue, both properties follow from one exact identity.  This note isolates
that identity and gives explicit constants suitable for Lean.

The remaining repository task is to identify the production cubic residue
kernel with the normalized kernel below.  Until that adapter is proved, this
note is a deterministic kernel theorem, not an actual-zeta completion claim.

## Normalized cubic residue kernel

Let

```text
0 < eta < 1,
s notin {0,-1,-2}.
```

Define

```text
B_eta(s)
  := ((1 + eta)^(s + 2) - 2 + (1 - eta)^(s + 2))
       / (eta^2 * s * (s + 1) * (s + 2)).
```

If the additive second-difference step is `Delta = eta * x`, then

```text
((x + Delta)^(s+2) - 2*x^(s+2) + (x - Delta)^(s+2))
  / (Delta^2 * s * (s+1) * (s+2))

  = x^s * B_eta(s).
```

Thus `B_eta(s)` is the exact dimensionless multiplier of the zero residue
after desmoothing.

## Exact triangle representation

For every twice differentiable function `f`, the centered second-difference
identity is

```text
f(eta) - 2*f(0) + f(-eta)
  = eta^2
      * integral u in [-1,1],
          (1 - |u|) * f''(eta*u).
```

Apply it to

```text
f(t) := (1 + t)^(s + 2).
```

Since

```text
f''(t) = (s + 2) * (s + 1) * (1 + t)^s,
```

one obtains the exact identity

```text
B_eta(s)
  = (1 / s)
      * integral u in [-1,1],
          (1 - |u|) * (1 + eta*u)^s.
```

Define the dimensionless low-frequency factor

```text
A_eta(s)
  := integral u in [-1,1],
       (1 - |u|) * (1 + eta*u)^s.
```

Then

```text
B_eta(s) = A_eta(s) / s.
```

The triangular weight has unit mass and zero first moment:

```text
integral u in [-1,1], (1 - |u|) = 1,

integral u in [-1,1], (1 - |u|) * u = 0.
```

This explains simultaneously why the low-frequency limit is `1/s` and why
the first-order smoothing distortion cancels.

## Quantitative low-cluster fidelity

Assume

```text
0 < eta <= 1/2,
0 <= Re s <= 1.
```

For

```text
g(t) := (1 + t)^s,
```

Taylor's formula with integral remainder gives

```text
g(t) - g(0) - t*g'(0)
  = t^2 * integral v in [0,1],
      (1 - v) * g''(v*t).
```

On `|t| <= eta`,

```text
|g''(t)|
  = |s * (s - 1)| * (1 + t)^(Re s - 2)
  <= 4 * |s * (s - 1)|.
```

Hence

```text
|g(t) - 1 - s*t|
  <= 2 * t^2 * |s * (s - 1)|.
```

The zero first moment removes the linear term.  Since

```text
integral u in [-1,1], (1 - |u|) * u^2 = 1/6,
```

the exact factor satisfies

```text
|A_eta(s) - 1|
  <= (eta^2 / 3) * |s * (s - 1)|.
```

Equivalently,

```text
|s * B_eta(s) - 1|
  <= (eta^2 / 3) * |s * (s - 1)|.
```

This is the required reciprocal-scale fidelity theorem.

For a fixed finite retained cluster `S`, put

```text
Q_S := max s in S, |s * (s - 1)|.
```

If

```text
eta^2 * Q_S <= 3 * epsilon,
```

then every retained coefficient satisfies

```text
|s * B_eta(s) - 1| <= epsilon.
```

Because `eta = X^(-d)` with `d > 0`, this holds beyond an explicit threshold
depending only on `S`, `d`, and `epsilon`.  Thus a finite Sharp surplus can be
preserved rather than replaced by an unspecified asymptotic equivalence.

## Quantitative high-frequency decay

Assume additionally

```text
0 <= Re s <= 1,
0 < eta <= 1/2.
```

The numerator has the direct bound

```text
|(1 + eta)^(s+2) - 2 + (1 - eta)^(s+2)|
  <= (1 + eta)^(Re s + 2) + 2 + (1 - eta)^(Re s + 2)
  <= 27/8 + 2 + 1
  = 51/8
  < 7.
```

Writing `t := Im s`, each Perron factor satisfies

```text
|s|     >= |t|,
|s + 1| >= |t|,
|s + 2| >= |t|.
```

Therefore, for `t != 0`,

```text
|B_eta(s)|
  <= 7 / (eta^2 * |t|^3).
```

In a signed dyadic shell `T <= |t| < 2*T`,

```text
|B_eta(s)| <= 7 * eta^(-2) * T^(-3).
```

This is exactly the reciprocal-cube input required by the cubic high-tail
Carlson estimate.

## Combined low/high kernel envelope

The same kernel has the two complementary bounds

```text
|B_eta(s)|
  <= |A_eta(s)| / |s|,

|B_eta(s)|
  <= 7 / (eta^2 * |Im s|^3).
```

For the low cluster, use the first identity and the quantitative estimate
`A_eta(s) = 1 + O(eta^2 |s(s-1)|)`.  For the high tail, use the second bound.

No switch of explicit-formula kernels is required.  Consequently the retained
cluster and its complement remain an exact partition of the same zero sum.

## Observation-interval normalization

Let

```text
x in [X, X^lambda],
beta0 fixed,
sigma := Re s.
```

Then

```text
x^(sigma - beta0)
  <= X^(kappa_lambda(sigma - beta0)).
```

For `eta = X^(-d)`, the high-frequency normalized residue satisfies

```text
|x^(s-beta0) * B_eta(s)|
  <= 7
       * X^(kappa_lambda(sigma-beta0))
       * X^(2*d)
       * |Im s|^(-3).
```

This produces the strip exponent

```text
kappa_lambda(sigmaR-beta0)
  + 2*d
  + gamma * (q(sigmaL)-3)
```

after applying the analytic-multiplicity Carlson mass in a shell
`T = X^gamma`.

## Main-cluster coefficient error

Let the ideal retained main term be

```text
MainIdeal(u)
  := sum s in S,
       multiplicity(s) * exp ((s-beta0)*u) / s.
```

The actual cubic-smoothed retained term is

```text
MainCubic(u)
  := sum s in S,
       multiplicity(s) * exp ((s-beta0)*u) * B_eta(s).
```

Their difference is

```text
MainCubic(u) - MainIdeal(u)
  = sum s in S,
      multiplicity(s) * exp ((s-beta0)*u) / s
        * (A_eta(s) - 1).
```

The finite-cluster fidelity estimate bounds this term by

```text
(eta^2 / 3)
  * sum s in S,
      multiplicity(s)
        * |exp ((s-beta0)*u)|
        * |s - 1|.
```

For fixed `S` and the normalized observation interval, the right side is an
explicit finite constant times `eta^2` and can be charged against the Sharp
surplus.  This coefficient-error term must appear in the residual ledger; it
must not be silently identified with zero.

## Explicit finite-cluster threshold

Assume the retained cluster is a maximal-real-part cluster:

```text
Re s <= beta0 for every s in S,
0 <= u.
```

Then

```text
|exp ((s-beta0)*u)| <= 1.
```

Define the fixed analytic-multiplicity cluster constant

```text
C_S := sum s in S, multiplicity(s) * |s - 1|.
```

The preceding coefficient estimate gives the uniform pointwise bound

```text
|MainCubic(u) - MainIdeal(u)|
  <= eta^2 * C_S / 3.
```

Because the observation triangle has unit mass, the same estimate holds in
triangle norm:

```text
triangleNorm(MainCubic - MainIdeal)
  <= eta^2 * C_S / 3.
```

Let the ideal retained-cluster theorem supply the strict surplus

```text
triangleNorm(MainIdeal) >= pi / 2 + deltaSharp,
0 < deltaSharp.
```

Reserve one quarter of the surplus for kernel distortion.  It is enough to
require

```text
eta^2 * C_S / 3 <= deltaSharp / 4.
```

For

```text
eta = X^(-d),
0 < d,
0 < C_S,
```

an explicit sufficient threshold is

```text
X >= (4 * C_S / (3 * deltaSharp))^(1 / (2*d)).
```

After also imposing `X >= 1`, the inequality remains valid when the displayed
base is below one.  If `C_S = 0`, no kernel-distortion threshold is needed.

Beyond this threshold,

```text
triangleNorm(MainCubic)
  >= pi / 2 + 3 * deltaSharp / 4.
```

If all remaining zero-tail, contour, `s = 0`, and trivial-zero residual norms
together satisfy

```text
totalOtherResidual <= deltaSharp / 2,
```

then the exact cubic explicit formula has

```text
triangleNorm(normalizedError)
  >= pi / 2 + deltaSharp / 4.
```

The compact-support witness transfer consequently yields

```text
|E(x)|
  >= (pi / 2 + deltaSharp / 4)
       * x^beta0 / |rho0|
```

for some `x in [X,X^lambda]`.  This is an absolute witness; no signed
conclusion is inferred.

## Proposed deterministic theorem chain

```text
cubicRelativeSecondDifferenceKernel
cubicRelativeSecondDifferenceKernel_scale
centeredSecondDifference_eq_triangleIntegral
cubicRelativeSecondDifferenceKernel_eq_triangle
triangleWeight_integral_eq_one
triangleWeight_firstMoment_eq_zero
triangleWeight_secondMoment_eq_one_sixth
norm_one_add_cpow_secondDeriv_le
cubicRelativeKernel_lowFrequency_error_le
cubicRelativeKernel_highFrequency_le
cubicRelativeKernel_signedShell_le
cubicRetainedMain_coefficientError_le
cubicRetainedMain_coefficientError_triangleNorm_le
cubicRetainedMain_fidelity_threshold
cubicRetainedMain_pi_div_two_surplus
```

The actual adapter should then prove:

```text
actualCubicResidueKernel_eq_relativeKernel
actualCubicRetainedMain_eq_ideal_add_error
actualCubicRetainedMain_error_triangleNorm_le
actualCubicHighTail_triangleNorm_le_carlson
```

Names are provisional.

## Lean proof strategy

1. Prove the real centered-difference integral identity once for a Banach-valued
   `C^2` function.
2. Instantiate it with the complex-valued map `t -> (1+t)^s` on
   `[-eta,eta]`, where the base is positive.
3. Keep the complex power as `exp (s * log (1+t))` so norm simplification uses
   a real logarithm.
4. Prove the three elementary triangle moments separately.
5. Derive the low-frequency error from the integral Taylor remainder and zero
   first moment.
6. Derive the high-frequency bound directly from the three numerator terms;
   do not weaken it through the triangle representation.
7. Only in the actual adapter rewrite the repository cubic residue expression
   into `x^s * B_eta(s)`.

## Audit rules

- Require `0 < eta <= 1/2` explicitly.
- Require the nonzero Perron factors explicitly.
- Keep analytic multiplicity outside `B_eta`.
- Record the high-frequency constant `7`.
- Record the low-frequency error constant `1/3`.
- Charge retained-cluster kernel distortion to the Sharp surplus.
- Use the same kernel for the retained cluster and the deleted complement.
- Do not replace the actual adapter with an arbitrary kernel hypothesis.
- Do not claim the final oscillation theorem until the production cubic
  expression has been rewritten to this kernel and all residuals are bounded.
