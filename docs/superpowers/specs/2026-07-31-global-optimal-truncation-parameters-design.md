# Global Optimal Truncation Parameters Design

## Goal

Turn the unique implicit density-threshold optimizer into a canonical global
outer-height ceiling and a transfer-ready near-optimal parameter constructor.

## Canonical optimizer

Define `jointTwoHeightOptimalDensityThreshold beta theta` by choosing the
unique balancing threshold when

```text
1 / 2 < theta < beta < 1.
```

The definition has a harmless fallback outside this regime. Its specification
theorem, not the fallback value, is the public mathematical interface.

## Global ceiling

Define

```text
globalCeiling(beta, theta)
  = prescribedCapCeiling(beta, optimalSigma(beta, theta), theta).
```

Stack57 proves that every admissible fixed `sigma` has ceiling at most this
value. At the optimizer,

```text
globalCeiling
  = min 1 (2 * (beta - optimalSigma)).
```

## Near-optimal realization

For every

```text
0 < eta < globalCeiling - (1 - beta),
```

set

```text
alpha = globalCeiling - eta.
```

The existing fixed-`sigma` constructor then supplies:

- a strip endpoint `optimalSigma < tau` and `theta < tau < beta`;
- balanced low and Carlson cuts;
- positive epsilon margins;
- the contour floor, unit cap, and all four strict decay inequalities.

## Boundary

The global ceiling is a supremal truncation exponent. The transfer uses a
strictly smaller exponent `globalCeiling - eta`; no claim is made that the
strict analytic constraints are attained at the ceiling itself.
