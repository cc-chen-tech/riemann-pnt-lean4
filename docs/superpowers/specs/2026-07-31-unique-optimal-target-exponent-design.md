# Unique Optimal Target Exponent Design

## Goal

Invert the strictly increasing improved cap threshold. For every prescribed
cap `theta` in `(1 / 2, 1)`, construct the unique target exponent `beta` in
`(2 / 3, 1)` satisfying

```text
jointTwoHeightImprovedGlobalCapThreshold beta = theta.
```

## Existence

Clear the positive denominator in the threshold equation and define

```text
F_theta(beta)
  = (beta - theta) * (Q(beta) + 1)
    - (1 - beta) * Q(beta)^2.
```

At the endpoints,

```text
F_theta(2 / 3) = 1 - 2 * theta < 0,
F_theta(1) = 1 - theta > 0.
```

The polynomial is continuous, so the intermediate value theorem supplies an
interior zero. Positivity of `Q + 1` converts that zero back to the original
threshold equation.

## Uniqueness

Stack67 proves the improved threshold is strictly increasing. Two target
exponents with the same threshold value therefore coincide.

## Canonical interface

Package the unique inverse as

```text
jointTwoHeightOptimalTargetExponent theta.
```

Its specification theorem returns the interval bounds and exact inverse
identity. This removes `beta` as a free optimization parameter in later
transfer theorems.
