# Actual Cubic Two-Height L2 Tail Design

## Objective

Construct the third independent Pintz-Carlson-explicit-formula PR.  The PR
must turn the actual third-order zeta explicit formula at outer height
`H = x^alpha` into a low detector layer at `Y = x^gammaLow` plus an actual
dyadic middle/high zero-tail capacity that is negligible at the exact target
zero scale.  It must retain the cubic kernel until all contour estimates have
been made.

The result is an L2-capacity handoff.  It does not prove the Gram/Schur or
Occupancy estimate supplied by the half-isolated task, and it does not yet
de-smooth the second Riesz mean back to `psi`.

## Fixed inputs

The PR consumes the following already audited interfaces.

- `exists_jointTwoHeightTargetAmplitudeParameters` supplies `sigma`, `tau`,
  `alpha`, `gammaLow`, `gammaHigh`, `epsilonLow`, and `epsilonHigh` for each
  `2 / 3 < beta < 1`.
- `gammaLow = alpha / 2` is the low detector exponent, so
  `Y = x^gammaLow`.
- `gammaHigh = carlsonTwoHeightBalancedCut sigma alpha` is the Carlson
  middle/high bookkeeping split.  It is not the contour height.
- `H = x^alpha` is the outer Perron and contour height.
- `exists_actualCarlsonDyadicStripSquareReciprocalCapacityExcluding_le_count`
  supplies actual-zeta square-multiplicity capacity after deleting an
  arbitrary finite set `S`.
- `exists_norm_residue_sum_sub_thirdOrderContourRemainder_sub_secondRieszPsi_le`
  supplies the actual finite-height cubic explicit formula.
- The actual good-height theorem supplies one common horizontal height in
  `[H,H+1]` with a uniform `O((1+log H)^2)` logarithmic-derivative bound.

## Scale discipline

For a fixed target zero `rho0`, put `beta = rho0.re` and
`R = norm rho0`.  The exact cubic coefficient scale is

```text
x^beta / R^3.
```

The later normalized second difference multiplies a cubic zero coefficient by
the exact factor represented by the repository's cubic kernel multiplier.  On
the local range `h*R <= 1`, this recovers the intended first-order scale

```text
x^beta / R.
```

This PR keeps `R` visible.  It must not replace `R` by `H` and must not claim
uniformity for a target zero whose ordinate changes with `x`.

## Actual dyadic cubic L2 capacity

For the actual zeta strip

```text
2^n < Im rho <= 2^(n+1),
sigma < Re rho <= tau,
rho not in S,
```

define the cubic coefficient square mass

```text
sum m(rho)^2 * x^(2*Re rho) / norm(rho)^6.
```

The Stack200 capacity theorem gives

```text
sum m(rho)^2 / norm(rho)^2
  <= B * (1 + log(2^(n+1)+6))
       * N(sigma,2^(n+1)) / (2^n)^2.
```

The four additional denominator powers and `Re rho <= tau` therefore give

```text
cubicSquareMass(n)
  <= B * x^(2*tau) * (1 + log(2^(n+1)+6))
       * N(sigma,2^(n+1)) / (2^n)^6.
```

After Carlson's `log^4` majorant, the effective block is

```text
x^(2*tau) * (1 + log(2^(n+1)+6))^5
  * 2^(n*(q(sigma)-6)),
q(sigma) = 4*sigma*(1-sigma).
```

The multiplicity-square lift contributes exactly one logarithm.  There is no
additional multiplicity loss.  Since `q(sigma) <= 1`, the dyadic exponent
obeys

```text
q(sigma)-6 <= -5 < 0.
```

At `sigma = 1/2`, the count exponent has the equality `q=1`, while the cubic
L2 block exponent is still strictly negative and equals `-5`.

Deleting a finite set `S` is handled only by nonnegative-mass monotonicity.
No zero-density theorem is reproved for `S`.

## Two-height aggregate

The aggregate covers all dyadic blocks meeting

```text
Y < Im rho <= H.
```

Blocks below and above `x^gammaHigh` are exposed separately so the result can
be compared directly with the four strict inequalities returned by the joint
parameter theorem.  The direct cubic L2 exponent at a polynomial block
`2^n` comparable with `x^gamma` is

```text
E_cubic(gamma)
  = 2*(tau-beta) + gamma*(q(sigma)-6).
```

It is strictly decreasing in `gamma`.  Its worst value on
`gammaLow <= gamma <= alpha` is at `gammaLow`, and is strictly negative from
`tau < beta`, `0 < gammaLow`, and `q(sigma)-6 < 0`.  The `log^5` factor is
absorbed by this strict polynomial margin.

The aggregate theorem takes dyadic bracketing hypotheses for `Y` and `H`
rather than hiding floor/ceiling arithmetic in its mathematical interface.

## Cubic contour strategy

The de-smoothed contour modules are not used for decay.  Dividing the cubic
second difference by `h^2` returns a first-order contour and recreates the
proved `x^(1-beta)*(1+log x)^2` obstruction.

Instead choose

```text
c(x) = 1 + 1/log x,
H(x) = x^alpha,
a(x) = one half of the reflected classical zero-free width at H(x).
```

For sufficiently large `x`, `0 < a(x) < 1 < c(x)`.  Reflection of the proved
right zero-free region shows that the positive line `Re s = a(x)` is free of
nontrivial zeros up to the selected height.  Because `a(x) > 0`, the contour
does not cross the cubic Perron pole at `s=0` and no new origin residue is
introduced.

The contour is estimated before de-smoothing.

- The right Perron truncation retains `H^-2`.  At the fixed target cubic scale
  its polynomial exponent is `1-beta-2*alpha`, which is strictly negative
  because `1-beta < alpha`.
- Each horizontal cubic edge retains `norm s^-3`.  The actual good-height
  logarithmic-derivative bound gives a power-log majorant with exponent
  `1-beta-3*alpha`, which is strictly negative.
- On the dynamic left edge, the zeta functional equation moves the
  logarithmic derivative to the reflected right zero-free line.  Splitting
  bounded and large ordinates gives only powers of `log H` and `1/a(x)`.
  Since `x^a(x)` is bounded and `beta > 0`, this is negligible relative to
  `x^beta/R^3`.

The final contour theorem must expose every polynomial exponent and every log
power.  It must not hide the left-edge estimate in an unconstrained function.

## Public theorem chain

The PR creates the following focused modules.

```text
PrimeNumberTheorem/
  ZeroDensityLayerBudgetActualCubicContourBudget.lean
  ZeroDensityLayerBudgetActualCubicContourBudgetContract.lean
  ZeroDensityLayerBudgetActualCubicContourBudgetAxiomAudit.lean
  ZeroDensityLayerBudgetActualCubicTwoHeightL2Tail.lean
  ZeroDensityLayerBudgetActualCubicTwoHeightL2TailContract.lean
  ZeroDensityLayerBudgetActualCubicTwoHeightL2TailAxiomAudit.lean
```

The public declarations are:

```text
actualCubicDyadicStripSquareCapacity
actualCubicDyadicStripSquareCapacityExcluding
exists_actualCubicDyadicStripSquareCapacityExcluding_le
cubicCarlsonL2BlockExponent
cubicCarlsonL2BlockExponent_lt_zero
actualCubicTwoHeightSquareTailCapacity
exists_actualCubicTwoHeightSquareTailCapacity_le
dynamicCubicLeftBoundary
exists_actualCubicContourTargetNegligible
exists_actualCubicHighToLowL2TailCertificate
```

The final certificate contains the exact `H`, `Y`, and `gammaHigh` roles, the
four strict inequalities from the joint parameter theorem, the cubic L2 tail
decay, and the cubic contour decay.

## Half-isolated boundary

This PR provides coefficient-square capacities and the actual smoothed
explicit-formula residual.  It does not prove a time-domain Gram inequality.
The half-isolated task consumes the square capacity and supplies Gram/Schur
and Occupancy.

## Claim boundary

The result is not RH, does not exclude zeros with real part greater than
`2/3`, and does not prove an unconditional `Omega` theorem by itself.  It
does not redo the Sharp lower bound, the `S`-relative energy theorem, or Gate
B set growth.  A later PR must perform a quantitative de-smoothing or
Tauberian transfer while preserving the exact `x^beta/R` scale.
