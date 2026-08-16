# Centered-cubic smoothing for the direct-L2 explicit-formula transfer

## Role in the proof

The direct-L2 Carlson estimate controls the zero complement inside a dynamic
height range.  It does not by itself control the contour remainder of the
truncated explicit formula after normalization by the target zero amplitude.

The smoothing layer must accomplish three things simultaneously:

1. act almost as the identity on the fixed finite low-zero cluster;
2. remain uniformly bounded on the Carlson-controlled middle zeros;
3. gain two powers of height on the outer contour and omitted high zeros.

A centered second difference of a twice logarithmically integrated explicit
formula has exactly this behavior.

## The centered-cubic multiplier

For `h > 0` and complex `s != 0`, define

```text
C_h(s)
  = (exp(h*s) - 2 + exp(-h*s)) / (h^2 * s^2)
  = exp(-h*s) * ((exp(h*s) - 1) / (h*s))^2.
```

The name "centered cubic" refers to applying the centered second difference to
an explicit formula whose zero term has acquired two additional powers of
`s` in the denominator through logarithmic integration.  After differencing,
the original `x^s / s` PNT zero scale is multiplied by `C_h(s)`.

Equivalently,

```text
C_h(s) = integral_{-1}^1 (1 - |u|) * exp(h*s*u) du.
```

The triangle kernel has total mass one.

## Uniform low/high-frequency bound

Assume

```text
0 <= Re s <= 1,
0 < h <= 1.
```

The integral identity

```text
exp(z) - 1 = z * integral_0^1 exp(t*z) dt
```

gives

```text
|exp(h*s) - 1|
  <= h * |s| * exp(h * max(Re s, 0)).
```

Using the factorized formula for `C_h`,

```text
|C_h(s)| <= exp(h * Re s) <= exp(h)
```

in the low-frequency regime.  Independently,

```text
|exp(h*s) - 2 + exp(-h*s)|
  <= exp(h*Re s) + 2 + exp(-h*Re s)
  <= 4 * exp(h),
```

so

```text
|C_h(s)| <= 4 * exp(h) / (h*|s|)^2.
```

Combining the two estimates yields the auditable global bound

```text
|C_h(s)|
  <= 4 * exp(h) * min(1, (h*|s|)^(-2))
  <= 4 * exp(1) * min(1, (h*|s|)^(-2)).
```

Thus the Carlson middle range can discard the `min` and pay only a fixed
constant, retaining its `multiplicity^2 / |rho|^2` mass.  The high range uses
the second branch and gains two additional powers of `h*|rho|`.

## Quantitative identity approximation on a finite cluster

For a fixed `s`, the triangle representation gives

```text
|C_h(s) - 1|
  <= integral_{-1}^1 (1 - |u|) * |exp(h*s*u) - 1| du.
```

Since

```text
integral_{-1}^1 (1 - |u|) * |u| du = 1/3,
```

one obtains

```text
|C_h(s) - 1|
  <= (h * |s| / 3) * exp(h * |s|).
```

For a finite low-zero cluster `S`, set

```text
R_S = max_{rho in S} |rho|.
```

Then

```text
max_{rho in S} |C_h(rho) - 1|
  <= (h * R_S / 3) * exp(h * R_S),
```

which tends to zero as `h -> 0`.  This is the exact input needed to preserve a
strict low-zero energy constant.  No uniform approximation over an unbounded
zero set is claimed or required.

If the low-zero theorem supplies a constant

```text
c_low > pi/2,
```

the total budget

```text
c_low - pi/2
```

must be split explicitly among:

- the finite-cluster multiplier perturbation;
- the Carlson middle-zero L2 tail;
- the outer contour/high-zero tail;
- the final triangle-to-point scale conversion.

The proof may choose four positive losses whose sum is strictly smaller than
`c_low - pi/2`.  Replacing strict inequalities by equality is invalid.

## Dynamic smoothing and contour parameters

Let

```text
lambda = 1 + epsilon,
g      = lambda * (1 - beta),
h      = Y^(-d),
H      = Y^alpha.
```

The right endpoint of the observation interval is `Y^lambda`.  A contour term
with the second-order height gain has normalized polynomial exponent

```text
g + 2*d - 2*alpha.
```

For the polylogarithmic Occupancy specialization, choose

```text
alpha = (1 + g) / 2,
d     = (1 - g) / 8.
```

Provided `0 < g < 1`, these parameters satisfy

```text
d > 0,
alpha > g,
g + 2*d - 2*alpha = -(3 + g) / 4 < 0.
```

The contour decay is therefore polynomial and leaves ample room for fixed
logarithmic factors.

The direct-L2 numerical design uses

```text
gammaL2Left  = 1/8,
gammaL2Right = (g + lambda/2) / 2.
```

The smoothing exponent lies strictly below both cutoffs:

```text
gammaL2Left - d = g/8 > 0,

gammaL2Right - d
  = (5*g + 2*lambda - 1) / 8 > 0
```

when `lambda >= 1` and `g > 0`.  Hence

```text
h * Y^gammaL2Left  -> infinity,
h * Y^gammaL2Right -> infinity.
```

This is why an existing facade with a hypothesis of the form `h*H <= 1` cannot
serve this proof: the required high-frequency branch needs `h*T` to grow, not
remain small.

## Triangle-average identity

Write `t = log x`, and let `G` be a twice logarithmically integrated PNT error
such that

```text
G''(t) = E(exp t),

E(x) = psi(x) - x
```

in the appropriate interval-integral sense.  Then

```text
(G(t+h) - 2*G(t) + G(t-h)) / h^2
  = integral_{-1}^1 (1 - |u|) * E(exp(t + h*u)) du.
```

For a zero term `exp(rho*t) / rho^3`, the left side equals

```text
exp(rho*t) / rho * C_h(rho),
```

so the target scale remains `x^(Re rho) / |rho|`.

The production theorem must derive this identity from the repository's actual
explicit-formula primitive.  The abstract identity above does not establish
that a currently available Riesz-sum normalization has exactly this second
logarithmic derivative.

## Returning from the average to a point witness

The triangle kernel is nonnegative and has total mass one.  Therefore

```text
|integral triangle(u) * E(x*exp(h*u)) du|
  <= sup_{|u| <= 1} |E(x*exp(h*u))|.
```

A lower bound for the smoothed expression produces some `u in [-1,1]` with a
pointwise lower bound for the genuine PNT error.

To keep that point inside the requested interval, choose the center `x` in

```text
[Y*exp(h), Y^lambda*exp(-h)].
```

Then

```text
x*exp(h*u) in [Y, Y^lambda]
```

for every `|u| <= 1`.  The center interval is nonempty once

```text
2*h < (lambda - 1) * log Y.
```

With `h = Y^(-d)`, `d > 0`, and `lambda > 1`, this holds for all sufficiently
large `Y`.

If `x_point = x*exp(h*u)`, then

```text
x^beta >= exp(-beta*h) * x_point^beta.
```

The factor `exp(-beta*h)` tends to one.  It must nevertheless consume an
explicit part of the strict constant budget before concluding a constant
strictly larger than `pi/2` at `x_point`.

This argument yields an absolute-value witness.  It does not by itself yield
both signs, so the final statement must not be labeled `Omega_plus_minus`
without a separate signed argument.

## Separation of the three height ranges

The smoothed explicit formula should be audited in three ranges:

```text
low cluster S:
  C_h(rho) = 1 + o_S(1),
  strict energy constant retained;

middle complement, |Im rho| <= H:
  |C_h(rho)| <= 4*e,
  direct-L2 Carlson square mass applies without exponent/log change;

outer contour and omitted high zeros:
  |C_h(rho)| <= 4*e/(h*|rho|)^2,
  normalized exponent g + 2*d - 2*alpha < 0.
```

The middle complement must use the same finite cluster `S` as the low-energy
theorem.  Its deletion is supplied by nonnegative mass monotonicity from the
Carlson layer.

## Lean-facing theorem chain

The smoothing slice should expose equivalents of:

```text
centeredCubic_eq_triangleIntegral
centeredCubic_abs_le
centeredCubic_sub_one_abs_le
finiteCluster_centeredCubic_tendsto_one
centeredSecondDifference_eq_triangleAverage
triangleAverage_le_sup
triangleWindow_subset_shortPowerInterval
polylogSmoothing_contourExponent_eq
polylogSmoothing_contourExponent_neg
polylogSmoothing_lt_gammaL2Left
polylogSmoothing_lt_gammaL2Right
strictConstant_survives_four_losses
```

The first group is generic complex analysis/calculus.  The second group is
elementary real parameter arithmetic.  Only after those pieces are audited
should the actual zeta explicit-formula theorem instantiate them.

## Remaining mathematical bridge

The unresolved production-level obligation is not the elementary kernel
estimate.  It is the exact theorem connecting the repository's available
explicit-formula primitive to a twice logarithmically integrated error `G`
with:

```text
zero coefficient: exp(rho*t) / rho^3,
second derivative: E(exp t),
contour remainder: compatible with the h^(-2) * H^(-2) bound.
```

If the actual primitive has different powers of `rho`, endpoint terms, or
normalization, the multiplier and contour ledger must be recomputed rather
than hidden behind an abstract kernel assumption.

## Nonclaims

This design does not yet prove:

- that the current explicit-formula API has the required twice-integrated
  normalization;
- that all real-axis and trivial-zero terms fit the same loss budget;
- that the direct-L2 middle complement is small on the exact low-energy
  averaging interval;
- an unconditional `[Y, Y^(1+epsilon)]` oscillation theorem;
- an `Omega_plus_minus` theorem.
