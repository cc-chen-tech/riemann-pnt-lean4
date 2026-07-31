# Theta-Only Target Asymptotic Design

## Goal

Transfer the cubic improved-cap asymptotic from the target exponent variable
`beta` to the cap variable `theta`, and quantify the asymptotic loss caused by
the current midpoint strict target.

## Mathematical chain

Let

```text
betaStar(theta) = jointTwoHeightOptimalTargetExponent theta.
```

For `theta` in `(1 / 2, 1)`, the existing inverse specification gives

```text
jointTwoHeightImprovedGlobalCapThreshold (betaStar theta) = theta.
```

The first step proves `betaStar(theta) -> 1-` as `theta -> 1-` by squeezing
`1 - betaStar(theta)` between zero and `1 - theta`. Composing this with the
existing beta-side cubic theorem gives

```text
(betaStar(theta) - theta) / (1 - betaStar(theta))^3 -> 36.
```

The same cubic estimate shows

```text
(1 - betaStar(theta)) / (1 - theta) -> 1.
```

Multiplying the two limits yields the theta-side result

```text
(betaStar(theta) - theta) / (1 - theta)^3 -> 36.
```

Finally, for the existing midpoint strict target

```text
betaStrict(theta) = (betaStar(theta) + 1) / 2,
```

the normalized excess satisfies

```text
(betaStrict(theta) - theta) / (1 - theta) -> 1 / 2.
```

Thus the inverse boundary is cubically close to `theta`, while the midpoint
strictification introduces a linear loss.

## Approaches considered

1. Compose the existing cubic limit with the canonical inverse and prove the
   required change-of-normalization ratio. This is selected because it reuses
   the audited constant `36` and exposes the conceptual inverse-transfer chain.
2. Substitute the explicit rational threshold formula and repeat a direct
   polynomial limit calculation. This duplicates stack66 and obscures the
   inverse structure.
3. Solve the inverse polynomial explicitly. This introduces unnecessary root
   formulas and branch bookkeeping.

## Boundary

This module concerns only parameter asymptotics in the density/transfer layer.
It does not modify the explicit formula, complementary-zero, VK-edge, or
sharp-oscillation modules, and it does not close visible-cluster
anti-cancellation.
