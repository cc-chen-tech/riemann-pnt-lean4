# Cubic Strict Target Exponent Design

## Goal

Replace the asymptotically coarse midpoint strict target by an automatic
strict target that remains at cubic distance from the cap `theta`.

## Construction

Write

```text
betaStar = jointTwoHeightOptimalTargetExponent theta
```

and define

```text
betaCubic =
  betaStar + ((1 - theta)^2 / 2) * (1 - betaStar).
```

For `theta` in `(1 / 2, 1)`, the interpolation coefficient lies strictly in
`(0, 1 / 2)`. Therefore

```text
betaStar < betaCubic < betaMidpoint < 1.
```

Strict monotonicity of the improved cap threshold then gives

```text
theta <
  jointTwoHeightImprovedGlobalCapThreshold betaCubic.
```

## Asymptotic

The theta-only inverse theorem gives

```text
(betaStar - theta) / (1 - theta)^3 -> 36
```

and

```text
(1 - betaStar) / (1 - theta) -> 1.
```

Hence

```text
(betaCubic - theta) / (1 - theta)^3
  -> 36 + 1 / 2
  = 73 / 2.
```

The new selector preserves the cubic scale while retaining a strict contour
gap. The old midpoint selector has linear excess and is pointwise larger.

## Boundary

This is a density/transfer parameter optimization. It does not alter the
explicit formula, complementary-zero, VK-edge, or sharp-oscillation modules,
and it does not supply visible-cluster anti-cancellation.
