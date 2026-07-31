# Improved Cap Threshold Strict Monotonicity Design

## Goal

Prove the improved global cap threshold is a strict increasing map from the
target interval `(2 / 3, 1)` into the cap interval `(1 / 2, 1)`.

## Density exponent

The canonical density exponent is

```text
Q(beta) = 3 * (3 * beta - 1) * (1 - beta).
```

For `2 / 3 < beta₁ < beta₂`, its difference factors through

```text
(beta₂ - beta₁) * (9 * (beta₁ + beta₂) - 12),
```

so `Q(beta₂) < Q(beta₁)`.

## Threshold monotonicity

The deficit is

```text
D(beta) = (1 - beta) * Q(beta)^2 / (Q(beta) + 1).
```

Both positive factors strictly decrease as `beta` increases. Therefore
`D(beta)` strictly decreases, while

```text
thetaGlobal(beta) = beta - D(beta)
```

strictly increases.

## Endpoints

Direct evaluation gives

```text
thetaGlobal(2 / 3) = 1 / 2,
thetaGlobal(1) = 1.
```

Together with strict monotonicity, this prepares a unique inverse target
exponent for every cap `theta` in `(1 / 2, 1)`.
