# Target-Amplitude Two-Height Exponent Design

## Purpose

The existing one-height target-amplitude transfer bounds every zero in a
strip using the outer truncation height. For Carlson's classical density
exponent

```text
q(sigma) = 4 * sigma * (1 - sigma),
```

this gives the normalized power exponent

```text
q(sigma) * alpha + tau - beta.
```

The existing two-height Carlson module improves the unnormalized PNT
exponent by splitting the zero sum at `x ^ gamma`, but its formulas are
normalized against the PNT scale `x`, not the target-zero scale `x ^ beta`.
This stack supplies the missing target-amplitude arithmetic.

## Mathematical Design

Split a strip with real-part endpoint `tau` into:

- low ordinates, counted only up to `x ^ gamma`;
- the high annulus, counted up to `x ^ alpha` and using
  `1 / |rho| <= x ^ (-gamma)`.

After division by the target amplitude `x ^ (beta - 1)`, the power
exponents are

```text
low  = q(sigma) * gamma + tau - beta
high = q(sigma) * alpha + tau - beta - gamma.
```

The unique balancing cut is unchanged:

```text
gamma* = q(sigma) * alpha / (q(sigma) + 1).
```

At this cut both exponents equal

```text
tau - beta
  + q(sigma)^2 * alpha / (q(sigma) + 1).
```

This is strictly smaller than the one-height exponent whenever
`1/2 < sigma < 1` and `0 < alpha`.

## Exact Feasibility Criterion

Write

```text
r(sigma) = q(sigma)^2 / (q(sigma) + 1).
```

Under `1/2 < sigma < 1`, there exists an outer exponent satisfying both the
contour floor and balanced Carlson decay,

```text
1 - beta < alpha
balancedExponent beta sigma tau alpha < 0,
```

if and only if

```text
r(sigma) * (1 - beta) + tau - beta < 0.
```

Once the common exponent is negative, choose a positive epsilon smaller than
its absolute value. The balanced-cut identities then provide strict negative
margins for both the low and high terms.

## Canonical Two-Thirds Threshold

For

```text
2/3 < beta < 1,
sigma = (3 * beta - 1) / 2,
tau = sigma,
```

one has

```text
1/2 < sigma < beta < 1.
```

Moreover `0 < q(sigma) < 1`, hence

```text
0 < r(sigma) < 1/2.
```

Since

```text
sigma - beta = -(1 - beta) / 2,
```

the feasibility expression is strictly negative. Therefore explicit
`alpha`, `gamma`, and `epsilon` exist with:

```text
1 - beta < alpha,
0 < gamma < alpha,
0 < epsilon,
lowExponent + epsilon < 0,
highExponent + epsilon < 0.
```

This lowers the arithmetic threshold from the canonical one-height
`beta > 3/4` to the denominator-saving two-height threshold `beta > 2/3`.

## Lean Artifacts

Create:

- `PrimeNumberTheorem/ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponent.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponentContract.lean`
- `Test/ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponentAxiomAudit.lean`

The implementation imports the existing audited
`ZeroDensityLayerBudgetCarlsonTwoHeightSplit` module and reuses its density
exponent and balanced cut.

## Scope Boundary

This stack proves exponent arithmetic and parameter feasibility only.

It does not:

- claim that an actual zeta-zero annulus already satisfies the new bound;
- modify the frozen complementary-zero module;
- modify VK-edge files;
- prove an unconditional Omega theorem or RH;
- alter the separate local pi/2 oscillation work.

The next stack must prove the actual multiplicity-weighted annulus kernel
bound with the growing denominator and then instantiate this arithmetic.
