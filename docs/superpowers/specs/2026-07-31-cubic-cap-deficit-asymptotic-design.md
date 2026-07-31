# Cubic Cap Deficit Asymptotic Design

## Goal

Determine the asymptotic scale of the distance between the globally improved
cap threshold and `beta` as `beta` tends to one from below.

## Exact normalization

Using

```text
Q(beta) = 3 * (3 * beta - 1) * (1 - beta),
```

the improved threshold satisfies

```text
beta - thetaGlobal(beta)
  = (1 - beta) * Q(beta)^2 / (Q(beta) + 1).
```

Therefore

```text
(beta - thetaGlobal(beta)) / (1 - beta)^3
  = 9 * (3 * beta - 1)^2 / (Q(beta) + 1).
```

The right-hand side tends to `36`.

## Comparison with the old threshold

The old canonical deficit is

```text
beta - c(beta) = (1 - beta) / 2.
```

Hence

```text
(beta - thetaGlobal(beta)) / (beta - c(beta))
  = 2 * Q(beta)^2 / (Q(beta) + 1),
```

which tends to zero.

## Meaning

The old admissible-cap loss is linear in `1 - beta`. Global optimization
reduces it to

```text
36 * (1 - beta)^3 * (1 + o(1)).
```

This is a quantitative structural gain inside the two-height Carlson model,
not only a strict inequality.
