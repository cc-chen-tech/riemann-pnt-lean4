# Cubic two-height direct-L2 feasibility above one half

## Purpose

This note gives an explicit two-height exponent construction for the actual
smoothed explicit-formula route:

- direct `L2` controls the middle zero range;
- the cubic second-difference kernel controls the high zero range in `L1`;
- the cubic contour controls the outer truncation.

At the exponent level, the construction is feasible for every

```text
1/2 < beta < 1.
```

This is a parameter-feasibility statement conditional on the stated actual
cubic kernel bound.  It is not a zero-free theorem, an RH theorem, or a proof
that no zeta zero has real part greater than `1/2`.

## Base parameters

Fix

```text
1/2 < beta < 1,
1 < lambda < 2,

g := lambda * (1 - beta).
```

Then

```text
0 < g < 1,
g < lambda / 2.
```

Choose the outer cubic contour and relative smoothing width

```text
alpha := (1 + g) / 2,
d     := (1 - g) / 8,
h     := X^(-d).
```

The known exponent identities are

```text
g < alpha < 1,
0 < d,

contourExponent = -(3 + g) / 4 < 0,
sZeroExponent   = -beta < 0,
trivialExponent = -(7 + g + 4 * beta) / 4 < 0.
```

The outer explicit-formula height is

```text
Touter = X^alpha.
```

## Required actual cubic high-frequency kernel

The high-tail adapter must prove a bound of the following concrete form for a
zero `rho` with `|Im rho| * h >= 1`:

```text
|normalizedCubicKernel(X,h,rho,beta)|
  <= Ckernel
       * X^(kappa_lambda(Re rho - beta))
       * h^(-2)
       / |rho|^3.
```

Here

```text
kappa_lambda(r) := r          if r <= 0,
                   lambda * r if 0 <= r.
```

This is the high-frequency consequence expected from:

- a third-order Perron denominator;
- a centered second difference;
- division by the square smoothing width.

The theorem must be instantiated with the actual cubic residue kernel.  An
opaque `hkernel` assumption is not final evidence.

## Cubic high-tail Carlson exponent

For a real strip `[sigmaL,sigmaR]` and signed dyadic height `T = X^eta`, the
linear Carlson mass gives the high-tail exponent

```text
High(sigmaL,sigmaR,eta)
  := kappa_lambda(sigmaR - beta)
       + 2 * d
       + eta * (q(sigmaL) - 3),

q(sigma) := 4 * sigma * (1 - sigma).
```

The logarithmic loss is Carlson's

```text
(log X)^4.
```

No local weighted-occupancy logarithm is needed in this `L1` high tail.

On `1/2 <= sigmaL <= sigmaR <= 1`,

```text
kappa_lambda(sigmaR - beta) <= g,
q(sigmaL) <= 1.
```

Therefore every strip satisfies the uniform bound

```text
High(sigmaL,sigmaR,eta)
  <= g + 2 * d - 2 * eta.
```

Define the sufficient high-tail critical exponent

```text
etaHighCritical
  := (g + 2 * d) / 2
   = (1 + 3 * g) / 8.
```

If

```text
etaHighCritical < eta,
```

then the complete high-tail polynomial margin is

```text
rHigh(eta) := 2 * eta - (g + 2 * d) > 0.
```

Moreover `eta > etaHighCritical >= d`, so the required high-frequency regime
`X^eta * h >= 1` holds for `X >= 1`.

## Direct-L2 middle range

Let the lower middle-range cutoff be

```text
Tlow = X^gammaLow.
```

The direct-L2 strip exponent is

```text
Middle(sigmaL,sigmaR,gammaLow)
  := 2 * kappa_lambda(sigmaR - beta)
       + gammaLow * (q(sigmaL) - 2).
```

The dynamic-strip result gives a strictly negative finite-strip exponent when

```text
g < gammaLow < lambda / 2.
```

Its infinitesimal margin is

```text
rMiddle
  := min gammaLow (2 * (gammaLow - g)) > 0.
```

The energy logarithmic loss is

```text
(log X)^5
```

from Carlson `(log X)^4` and one weighted local-occupancy logarithm.  There is
no separate maximum-multiplicity logarithm.

This estimate applies to the middle range

```text
X^gammaLow <= |Im rho| < X^gammaHigh.
```

Its dyadic sum is dominated by the lower endpoint, so its polynomial exponent
depends on `gammaLow`, not `gammaHigh`.

## Explicit simultaneous construction

Define the upper admissible point for the direct-L2 lower cutoff:

```text
cLow := min (lambda / 2) alpha.
```

Both entries exceed `g`, hence

```text
g < cLow.
```

Choose

```text
gammaLow := (g + cLow) / 2.
```

Then

```text
g < gammaLow,
gammaLow < lambda / 2,
gammaLow < alpha.
```

Next put

```text
mHigh := max gammaLow etaHighCritical,

gammaHigh := (mHigh + alpha) / 2.
```

The two quantities inside `mHigh` are both strictly smaller than `alpha`:

```text
gammaLow < alpha,

alpha - etaHighCritical
  = (3 + g) / 8 > 0.
```

Therefore

```text
gammaLow < gammaHigh,
etaHighCritical < gammaHigh,
gammaHigh < alpha.
```

This gives the strict height chain

```text
0 < d < gammaHigh,
g < gammaLow < gammaHigh < alpha < 1.
```

The ranges are now:

```text
retained low cluster:
  |Im rho| < X^gammaLow,

direct-L2 middle tail:
  X^gammaLow <= |Im rho| < X^gammaHigh,

cubic-L1 high tail:
  X^gammaHigh <= |Im rho| < X^alpha,

outer contour:
  |Im s| = X^alpha.
```

All middle, high, contour, `s = 0`, and trivial-zero polynomial exponents are
strictly negative.

## Explicit margins

The construction supplies:

```text
rMiddle
  := min gammaLow (2 * (gammaLow - g)) > 0,

rHigh
  := 2 * gammaHigh - (g + 2 * d) > 0,

rContour
  := (3 + g) / 4 > 0,

rSZero
  := beta > 0,

rTrivial
  := (7 + g + 4 * beta) / 4 > 0.
```

After finite real-strip discretization, reserve half of `rMiddle`.  After
absorbing fixed logarithmic powers, reserve another half.  A conservative
energy-level middle rate is therefore

```text
etaMiddleEnergy := rMiddle / 4.
```

For the high `L1` tail, reserve half of `rHigh` for `(log X)^4`:

```text
etaHighAmplitude := rHigh / 2.
```

An `L1` pointwise upper bound also bounds its probability-triangle norm with
the same amplitude exponent.

The common residual amplitude rate can be chosen below

```text
min (rMiddle / 8)
  (min (rHigh / 2)
    (min (rContour / 2)
      (min (rSZero / 2) (rTrivial / 2)))).
```

The factor `rMiddle / 8` appears because the direct-L2 estimate is first an
energy bound and must be square-rooted before entering the residual norm.

## Explicit dyadic high-tail constant

Since `q(sigmaL) - 3 <= -2`, for `H >= 1`,

```text
(2^n * H)^(q(sigmaL)-3)
  <= 2^(-2*n) * H^(q(sigmaL)-3)
  <= 2^(-n) * H^(q(sigmaL)-3).
```

Also

```text
1 + log (2^n * H)
  <= (1 + log H) * (n + 1).
```

Using the exact moment

```text
sum n >= 0, 2^(-n) * (n + 1)^4 = 300,
```

one signed high tail costs at most the explicit dyadic factor `300`; both
signs cost `600`, before the kernel and Carlson constants.

## What is new in this feasibility calculation

The construction does not force one height to perform all jobs:

- `gammaLow` is chosen for direct-L2 reciprocal-square decay;
- `gammaHigh` is chosen for cubic reciprocal-cube decay;
- `alpha` is the outer contour height.

This removes the artificial requirement that a single cutoff satisfy both an
`L1` reciprocal-height inequality and the direct-L2 cap.  The resulting
exponent feasibility requires only `beta > 1/2`.

The mathematical gap is now sharply localized: prove that the actual cubic
second-difference kernel and explicit formula instantiate the stated
high-frequency `h^(-2) / |rho|^3` bound with all real-axis and contour terms on
the same normalization.

## Proposed formal theorem chain

### Arithmetic-only slice

```text
cubicHighCritical
cubicHighCritical_eq
cubicHighCritical_lt_outer
directL2LowCap
directL2LowCap_gt_support
twoHeightGammaLow
twoHeightGammaLow_gt_support
twoHeightGammaLow_lt_directL2Cap
twoHeightGammaLow_lt_outer
twoHeightGammaHigh
twoHeightGammaLow_lt_gammaHigh
cubicHighCritical_lt_gammaHigh
twoHeightGammaHigh_lt_outer
twoHeightMiddleMargin_pos
twoHeightHighMargin_pos
twoHeightCommonResidualRate_pos
```

### Actual cubic adapter slice

```text
actualCubicKernel_highFrequency_le
actualCubicSignedShell_l1_le_carlson
actualCubicSignedShell_l1_delete_le
actualCubicHighTail_l1_le
actualCubicHighTail_triangleNorm_le
actualTwoHeightMiddleHighResidual_triangleNorm_le
```

Names are provisional.

## Audit rules

- Treat the `beta > 1/2` result as parameter feasibility until the actual
  cubic kernel theorem is instantiated.
- Do not claim that feasibility excludes zeta zeros with `Re rho > 1/2`.
- Keep `gammaLow`, `gammaHigh`, and `alpha` distinct in every theorem.
- Attach `(log X)^5` to middle energy and `(log X)^4` to high amplitude.
- Square-root middle energy before combining residual amplitudes.
- Use analytic multiplicity in both Carlson sums.
- Delete the retained finite set by nonnegative monotonicity.
- Do not import or reprove Sharp or half-isolated lower bounds.
- Do not call the construction optimal without adding the retained-cluster
  cost to the minimax objective.
