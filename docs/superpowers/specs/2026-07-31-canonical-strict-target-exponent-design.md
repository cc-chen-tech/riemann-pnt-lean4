# Canonical Strict Target Exponent Design

## Goal

Convert the unique boundary target exponent into a canonical strictly feasible
target exponent without requiring a user-supplied epsilon.

## Construction

Let

```text
betaBoundary(theta)
```

be the unique exponent satisfying

```text
thetaGlobal(betaBoundary) = theta.
```

Define

```text
betaStrict(theta) = (betaBoundary(theta) + 1) / 2.
```

Since `2 / 3 < betaBoundary < 1`,

```text
betaBoundary < betaStrict < 1.
```

Strict monotonicity of `thetaGlobal` gives

```text
theta
  = thetaGlobal(betaBoundary)
  < thetaGlobal(betaStrict).
```

The general threshold bound also gives

```text
theta < betaBoundary < betaStrict.
```

## Result

The specification theorem returns the boundary identity, all interval
relations, and the strict improved-cap condition needed by the automatic
actual transfer. This removes both `beta` and an auxiliary beta-slack
parameter from later public interfaces.
