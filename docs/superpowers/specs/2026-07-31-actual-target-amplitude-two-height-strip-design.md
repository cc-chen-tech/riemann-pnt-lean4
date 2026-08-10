# Actual Target-Amplitude Two-Height Strip Design

## Purpose

Stack 35 proves the target-normalized two-height exponent arithmetic. The
existing actual Carlson two-height module already constructs:

- the low actual zeta-zero strip;
- the high ordinate annulus;
- multiplicity-weighted zero sums;
- the intermediate-height denominator saving.

This stack connects those two layers without rebuilding any zero finsets.

## Endpoint-Shift Principle

For positive `x`,

```text
x^(tau - 1) / x^(beta - 1) = x^(tau - beta).
```

The right side is the ordinary relative kernel bound with shifted endpoint

```text
tau' = tau - beta + 1,
```

because

```text
x^(tau' - 1) = x^(tau - beta).
```

Therefore:

```text
targetLowBudget(beta, sigma, tau, gamma)
  = actualLowBudget(sigma, tau - beta + 1, gamma)

targetHighBudget(beta, sigma, tau, alpha, gamma)
  = actualHighBudget(sigma, tau - beta + 1, alpha, gamma).
```

The existing convergence theorems then apply after the exact exponent
identities:

```text
carlsonTwoHeightLowExponent sigma (tau - beta + 1) gamma
  = targetAmplitudeCarlsonTwoHeightLowExponent beta sigma tau gamma

carlsonTwoHeightHighExponent sigma (tau - beta + 1) alpha gamma
  = targetAmplitudeCarlsonTwoHeightHighExponent beta sigma tau alpha gamma.
```

## Actual Strip Transfer

Define the normalized actual strip mass:

```text
sum_{rho in actualPositiveCarlsonStrip(sigma,tau,x^alpha)}
  ||pntRelativeZeroContribution(x,rho)||
/
targetZeroPowerAmplitude(beta,x).
```

For `x >= 1`, the existing actual two-height sum bound divided by the positive
target amplitude is bounded by the sum of the target low and high budgets.
If both target exponents have one strict positive margin, squeeze gives
convergence to zero.

At the balanced cut, stack 35 supplies both exponent margins from one
feasibility inequality.

## Genuine `beta > 2/3` Actual Strip

Stack 35 proves feasibility at the limiting endpoint

```text
sigma0 = tau0 = (3 * beta - 1) / 2.
```

The corresponding actual strip is empty because its lower threshold and upper
endpoint coincide. This stack must not present that limit as an actual strip
result.

Instead, strict feasibility leaves room to choose

```text
sigma = sigma0
sigma < tau < beta - r(sigma) * (1 - beta) < beta.
```

This gives a genuine positive-width actual strip and, by the balanced transfer,
an outer height exponent `alpha > 1 - beta` for which its complete
multiplicity-weighted target-normalized mass tends to zero.

## Lean Artifacts

Create:

- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetAmplitudeTwoHeightStrip.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetAmplitudeTwoHeightStripContract.lean`
- `Test/ZeroDensityLayerBudgetActualTargetAmplitudeTwoHeightStripAxiomAudit.lean`

## Scope Boundary

This stack controls one actual positive-height Carlson strip. It does not:

- aggregate all real-part strips into the full cluster-excluded complement;
- alter the frozen complementary-zero module;
- alter VK-edge modules;
- supply the separate local pi/2 main-term theorem;
- claim an unconditional Omega theorem or RH.

The next stack may combine this strip with the already-formalized low layer,
conjugate negative ordinates, and real-ordinate residual.
