# Explicit residual-threshold compiler

## Purpose

The final sharp transfer cannot stop at statements of the form

```text
C * X^(-eta) * (1 + log X)^ell -> 0.
```

It must produce one threshold beyond which every residual consumes its
assigned part of the retained-cluster surplus.  This note gives a uniform
closed-form threshold and a finite aggregation rule.

## One power-log term

Fix

```text
0 <= C,
0 < eta,
ell : Nat,
0 < budget,
1 <= X.
```

Consider

```text
Term(X) := C * X^(-eta) * (1 + log X)^ell.
```

Define

```text
a := eta / (2 * (ell + 1)).
```

Then `a>0`.  For `X>=1`, the elementary logarithm bound

```text
log X <= X^a / a
```

and `1<=X^a` give

```text
1 + log X
  <= (1 + 1/a) * X^a
  = (1 + 2*(ell+1)/eta) * X^a.
```

Put

```text
K(eta,ell)
  := (1 + 2*(ell+1)/eta)^ell.
```

Since

```text
a * ell
  = eta * ell / (2*(ell+1))
  <= eta / 2,
```

one obtains

```text
(1 + log X)^ell
  <= K(eta,ell) * X^(eta/2).
```

Therefore

```text
Term(X)
  <= C * K(eta,ell) * X^(-eta/2).
```

## Explicit sufficient threshold

Define

```text
powerLogThreshold(C,eta,ell,budget)
  := max 1
       ((C * K(eta,ell) / budget)^(2/eta)).
```

If

```text
powerLogThreshold(C,eta,ell,budget) <= X,
```

then

```text
Term(X) <= budget.
```

When `C=0`, the term vanishes and the threshold can be simplified to `1`.
The displayed formula remains a sufficient convention after defining
`0^positive = 0` in the chosen real-power API.

The retained polynomial rate after this explicit absorption is `eta/2`.

## From energy to norm

Suppose the direct-L2 middle tail has energy bound

```text
Energy(X)
  <= CEnergy * X^(-etaEnergy) * (1 + log X)^5.
```

Taking square roots gives

```text
triangleNorm(X)
  <= sqrt(CEnergy)
       * X^(-etaEnergy/2)
       * (1 + log X)^(5/2).
```

To avoid a fractional logarithmic exponent in the threshold compiler, use

```text
(1 + log X)^(5/2) <= (1 + log X)^3
```

for `X>=1`.  Thus the norm is bounded by the integer signature

```text
CNorm   := sqrt(CEnergy),
etaNorm := etaEnergy / 2,
ellNorm := 3.
```

Applying `powerLogThreshold` leaves the explicit post-absorption norm rate

```text
etaEnergy / 4.
```

For the finite-strip middle estimate

```text
etaEnergy = rMiddle / 2,
```

this becomes

```text
middle norm rate = rMiddle / 8.
```

This recovers the earlier exponent ledger without silently square-rooting a
logarithmic factor.

## Residual term specification

Use a typed record

```text
structure ResidualTermSpec where
  tag       : ResidualTag
  constant  : Real
  rate      : Real
  logLoss   : Nat
  budget    : Real
  constant_nonneg : 0 <= constant
  rate_pos       : 0 < rate
  budget_pos     : 0 < budget
```

with tags such as

```text
middleZeroNorm,
cubicHighZeroNorm,
cubicKernelDistortion,
contour,
sZero,
trivialZero.
```

The compiler assigns

```text
spec.threshold
  := powerLogThreshold
       spec.constant spec.rate spec.logLoss spec.budget.
```

Each actual analytic theorem proves that its residual is bounded by the
corresponding `Term(X)` beyond its own structural threshold.

## Finite aggregation

For a finite family `specs`, define

```text
compiledThreshold
  := max
       structuralThreshold
       (max spec in specs, spec.threshold).
```

If

```text
compiledThreshold <= X,
```

then every residual satisfies its individual budget and

```text
sum spec in specs, residual(spec,X)
  <= sum spec in specs, spec.budget.
```

To preserve a retained-cluster surplus `deltaSharp`, require the arithmetic
certificate

```text
sum spec in specs, spec.budget < deltaSharp.
```

The final normalized error norm then exceeds

```text
pi/2 + deltaSharp
  - sum spec in specs, spec.budget
  > pi/2.
```

This formulation supports unequal allocations and avoids hard-coding a number
of residual terms into the transfer theorem.

## One explicit allocation

For six residual tags, a simple auditable choice is

```text
cubicKernelDistortion : deltaSharp / 4,
middleZeroNorm        : deltaSharp / 8,
cubicHighZeroNorm     : deltaSharp / 8,
contour                : deltaSharp / 8,
sZero                  : deltaSharp / 8,
trivialZero            : deltaSharp / 8.
```

The total is

```text
7 * deltaSharp / 8 < deltaSharp,
```

so the final retained margin is at least

```text
deltaSharp / 8.
```

Consequently the witness constant is at least

```text
pi/2 + deltaSharp/8.
```

The earlier coarser allocation yielding `deltaSharp/4` remains valid if the
non-kernel residuals are first grouped into one term with budget
`deltaSharp/2`.  The compiler should permit both presentations.

## Actual term signatures

The intended lower-transfer instance has the following shapes:

```text
middleZeroNorm:
  constant = sqrt(CMiddleEnergy),
  rate     = rMiddle/4 before compiler absorption,
  logLoss  = 3,

cubicHighZeroNorm:
  constant = CHigh,
  rate     = rHigh,
  logLoss  = 4,

cubicKernelDistortion:
  constant = C_S/3,
  rate     = 2*d,
  logLoss  = 0,

contour:
  constant = CContour,
  rate     = rContour,
  logLoss  = ellContour,

sZero:
  constant = CSZero,
  rate     = beta,
  logLoss  = 2,

trivialZero:
  constant = CTrivial,
  rate     = rTrivial,
  logLoss  = ellTrivial.
```

For the middle term, `rMiddle/4` is the rate after taking the square root of
the finite-strip energy exponent `-rMiddle/2`; the compiler then retains
`rMiddle/8`.

Every constant and structural threshold must come from the corresponding
actual explicit-formula theorem.

## Separation from asymptotic notation

The compiler proves a concrete implication

```text
compiledThreshold <= X
  -> totalResidual(X) <= allocatedBudget.
```

An eventual/asymptotic corollary can then be derived by existentially hiding
`compiledThreshold`.  The proof direction must not be reversed: an `O` or
`Tendsto` statement with an unspecified constant is insufficient to compute
the sharp-surplus threshold.

## Proposed theorem chain

```text
log_le_rpow_div
one_add_log_le_constant_mul_rpow
powerLog_le_half_power
powerLogThreshold
powerLog_le_budget_of_threshold_le
sqrt_log_fifth_le_log_cube
middleEnergy_to_integerLogNorm
ResidualTag
ResidualTermSpec
ResidualTermSpec.threshold
ResidualTermSpec.bound_of_threshold_le
compiledResidualThreshold
all_residual_bounds_of_compiledThreshold_le
sum_residual_le_sum_budget
pi_div_two_surplus_of_budget_sum_lt
explicitSixResidualBudget_sum
explicitSixResidualWitnessMargin
```

Names are provisional.

## Audit rules

- Require every rate and budget to be strictly positive.
- Keep constants nonnegative and explicit.
- Convert energy to norm before aggregation.
- Use an integer logarithmic exponent after square root.
- Do not hide constants inside asymptotic notation.
- Take a finite maximum of all structural and absorption thresholds.
- Verify the budget sum arithmetically.
- Preserve a strict positive surplus over `pi/2`.
- Do not infer a signed witness from the absolute norm transfer.
