# Kernel-signature unified upper/lower transfer

## Purpose

The upper and lower PNT routes should share one budget compiler without
pretending that they use the same analytic norm.  The common object is a
kernel signature derived from an actual explicit-formula term.

The signature records:

- how many endpoint-support factors occur;
- how many reciprocal zero heights survive;
- the smoothing penalty;
- the Carlson logarithmic loss.

From this data, one formula produces the layer budget.  Separate assemblers
then use that budget:

- `L1` summation for a PNT upper bound;
- weighted `L2` energy plus a retained-cluster lower bound for oscillation;
- cubic `L1` summation for the high complement in either route.

This is the intended common transfer machine.  It does not replace the actual
kernel, density, explicit-formula, or lower-energy theorems.

## Logarithmic layer budget

Fix:

```text
X > 1,
x in [X, X^lambda],
b = normalization real exponent,
[sigmaL,sigmaR] = real-part strip,
T = dyadic height.
```

Let

```text
kappa_lambda(r) := r          if r <= 0,
                   lambda * r if 0 <= r.
```

Assume the analytic-multiplicity Carlson mass has the form

```text
Mass(sigmaL,T)
  <= Cdensity
       * T^(q(sigmaL))
       * (1 + log T)^ellDensity.
```

A kernel signature consists of:

```text
rSupport  : Nat,
pHeight   : Nat,
smoothLog : X -> Real,
ellExtra  : Nat.
```

Its logarithmic layer budget is

```text
LayerLogBudget
  := rSupport * kappa_lambda(sigmaR - b) * log X
       + smoothLog(X)
       + (q(sigmaL) - pHeight) * log T
       + (ellDensity + ellExtra) * log (1 + log T)
       + log Ckernel
       + log Cdensity.
```

The corresponding contribution is bounded by

```text
exp LayerLogBudget.
```

This log form is primary.  It remains meaningful for non-polynomial dynamic
heights and Vinogradov-Korobov zero-free boundaries.  The polynomial exponent
form is only the specialization `T = X^gamma` and
`smoothLog(X) = a * log X`:

```text
LayerPolyExponent
  = rSupport * kappa_lambda(sigmaR - b)
      + a
      + gamma * (q(sigmaL) - pHeight).
```

## Three actual signatures

### Ordinary explicit-formula L1 layer

For one reciprocal zero height and direct absolute summation:

```text
rSupport  = 1,
pHeight   = 1,
smoothLog = 0,
ellExtra  = 0.
```

Thus

```text
UpperL1Exponent
  = kappa_lambda(sigmaR - b)
      + gamma * (q(sigmaL) - 1),

log loss = ellDensity.
```

For a relative PNT upper bound, use `b = 1`.

### Complex-triangle weighted L2 layer

The energy expansion has two endpoint-support factors, while weighted Schur
retains only one linear Carlson mass and two reciprocal heights:

```text
rSupport  = 2,
pHeight   = 2,
smoothLog = 0,
ellExtra  = 1.
```

Hence

```text
LowerL2EnergyExponent
  = 2 * kappa_lambda(sigmaR - b)
      + gamma * (q(sigmaL) - 2),

log loss = ellDensity + 1.
```

For Carlson `(log T)^4`, this is the actual energy loss `(log T)^5`.  The
extra logarithm is weighted local occupancy, not maximum multiplicity.

For a target zero or retained maximal-real-part cluster, use `b = beta0`.

### Cubic high-frequency L1 layer

The cubic second-difference residue has one endpoint-support factor, three
reciprocal heights, and smoothing penalty `eta^(-2)`:

```text
rSupport  = 1,
pHeight   = 3,
smoothLog = 2 * log (eta^(-1)),
ellExtra  = 0.
```

For `eta = X^(-d)`,

```text
CubicHighExponent
  = kappa_lambda(sigmaR - b)
      + 2*d
      + gamma * (q(sigmaL) - 3),

log loss = ellDensity.
```

This is an amplitude bound, not an energy bound.

## Concrete signature table

```text
route                 norm    b       rSupport pHeight smooth   log loss
----------------------------------------------------------------------------
PNT upper low layer   L1      1       1        1       0        4
oscillation middle    L2      beta0   2        2       0        5
cubic upper high      L1      1       1        3       2d       4
cubic lower high      L1      beta0   1        3       2d       4
```

Every row refers to a distinct actual kernel theorem.  The table is not a
license to interchange norms or denominator powers.

## Upper transfer mode

For the upper PNT direction, set

```text
b = 1.
```

A zero-free boundary gives, in each height range,

```text
sigmaR <= 1 - zfr(T).
```

Since the offset is nonpositive,

```text
kappa_lambda(sigmaR - 1)
  = sigmaR - 1
  <= -zfr(T).
```

The ordinary `L1` log budget is therefore bounded by

```text
-zfr(T) * log X
  + (q(sigmaL) - 1) * log T
  + ellDensity * log (1 + log T)
  + constants.
```

The cubic high layer replaces `(q-1) * log T` by

```text
(q-3) * log T + 2 * log (eta^(-1)).
```

The optimal dynamic height minimizes the maximum of:

- all zero-layer log budgets;
- the contour log budget;
- the real-axis and trivial-zero log budgets;
- the desmoothing budget.

Because `zfr(T)` may be logarithmic rather than a constant real-part gap, this
optimization must remain in log-budget form until the final asymptotic
specialization.

## Lower oscillation mode

For the lower direction, set

```text
b = beta0.
```

Split the exact same cubic zero sum into:

```text
retained finite cluster S,
middle complement,
high complement.
```

Use:

- the actual cubic low-frequency identity to compare the retained coefficient
  with `1/rho`;
- the weighted `L2` signature for the middle complement;
- the cubic `L1` signature for the high complement;
- finite deletion monotonicity for both complement estimates.

The budget compiler outputs energy for the middle layer and amplitude for the
high layer.  Before adding residuals, convert middle energy to triangle norm by
taking a square root:

```text
MiddleNormLogBudget = MiddleEnergyLogBudget / 2.
```

The retained-cluster theorem supplies an independent lower norm
`pi/2 + surplus`.  The unified-transfer assembler subtracts the compiled
residual norms and obtains an actual witness only when the surplus remains
strictly positive.

## Finite deletion law

The budget compiler may carry a finite deletion tag `S`, but it does not
modify density data.  For each nonnegative analytic-multiplicity mass or row
mass,

```text
mass(layer \ S) <= mass(layer).
```

Consequently the constants, exponents, and logarithmic losses in the layer
signature remain unchanged after deleting `S`.

The retained cluster enters only the lower assembler and the explicit-formula
identity.

## Dynamic-height optimization

For a finite strip and height decomposition, collect every log budget into a
tagged finite family:

```text
upperZeroL1,
lowerZeroL2Energy,
cubicHighL1,
contour,
desmoothing,
sZero,
trivialZero.
```

The optimization target is

```text
minimize over admissible parameters,
  max tag, LayerLogBudget(tag).
```

If the budgets become affine after a polynomial-height specialization, the
finite primal/dual affine certificate verifies the optimum.  If a zero-free
boundary remains nonlinear, the same tagged family is retained but its
analytic minimization theorem is proved separately.

The verifier must distinguish:

- a true minimizing parameter;
- a boundary supremum or infimum;
- an arbitrary feasible witness;
- a robust optimizer that includes an actual competing error exponent.

## Common transfer object

The minimal common structure should contain data, not conclusions:

```text
structure KernelLayerSignature where
  mode        : LayerMode
  normKind    : L1 | L2Energy
  rSupport    : Nat
  pHeight     : Nat
  smoothLog   : Real -> Real
  logLoss     : Nat
  nonnegative : mass is nonnegative
```

The production theorem for each actual kernel proves that its contribution is
bounded by the compiled budget.  The two assemblers are separate:

```text
upperTransfer:
  all layer amplitudes small -> PNT error upper bound,

lowerTransfer:
  retained lower norm + residual norms small -> oscillation witness.
```

This prevents an `L2` energy hypothesis from being silently consumed as an
`L1` amplitude bound.

## Candidate mathematical contribution

The potentially new component is not the isolated formula for any one row.
It is the verified composition:

1. actual explicit-formula kernels produce typed signatures;
2. analytic-multiplicity Carlson bounds feed both `L1` and weighted `L2` rows;
3. finite deletion preserves the same budgets;
4. a dynamic optimizer selects one or two heights;
5. upper and lower assemblers consume the same certified layer ledger without
   conflating their norms;
6. the lower assembler preserves an explicit sharp surplus and reciprocal
   target-zero scale.

Any novelty claim must be limited to this composed, explicit, machine-checked
transfer unless a genuinely new analytic estimate is proved.

## Proposed theorem chain

### Budget compiler

```text
KernelLayerSignature
KernelLayerSignature.logBudget
KernelLayerSignature.polyExponent
ordinaryL1Signature
weightedL2Signature
cubicHighL1Signature
ordinaryL1Signature_logBudget
weightedL2Signature_logBudget
cubicHighL1Signature_logBudget
logBudget_delete_mono
```

### Upper assembler

```text
upperLayerBound_of_zeroFree_density_kernel
upperFiniteLayersBound
upperExplicitFormulaTransfer
upperOptimalHeightTransfer
```

### Lower assembler

```text
lowerMiddleEnergyBound_of_density_kernel
lowerMiddleNormBound
lowerHighAmplitudeBound
lowerResidualNormBound
lowerExplicitFormulaWitnessTransfer
lowerPiDivTwoSurplusTransfer
```

Names are provisional.  No assembler should be added before at least one
actual production kernel has instantiated every field it consumes.

## Audit rules

- Keep log budgets primary for VK-scale heights.
- Record `L1`, `L2 energy`, and `L2 norm` as different types or tags.
- Record denominator power and smoothing penalty explicitly.
- Use analytic multiplicity throughout.
- Preserve finite deletion by nonnegative monotonicity.
- Never call a zero exponent decay.
- Never take a square root silently.
- Keep upper normalization `b = 1` distinct from lower normalization
  `b = beta0`.
- Require actual kernel instances before exposing a unified facade theorem.
- Do not infer RH or signed oscillation from parameter feasibility.
