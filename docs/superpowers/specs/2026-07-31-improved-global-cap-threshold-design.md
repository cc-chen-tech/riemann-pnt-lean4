# Improved Global Cap Threshold Design

## Goal

Determine the exact real-part cap range for which the globally optimized
two-height truncation ceiling lies above the contour floor.

## Balance map

Define

```text
B_beta(sigma)
  = 2 * balancedSlope(sigma) * (beta - sigma).
```

On `1 / 2 < sigma < beta < 1`, both factors are positive and strictly
decreasing, so `B_beta` is strictly decreasing. The unique optimizer satisfies

```text
B_beta(sigmaOpt) = beta - theta.
```

## Improved threshold

Let

```text
c(beta) = (3 * beta - 1) / 2
```

be the old canonical threshold and define

```text
thetaGlobal(beta) = beta - B_beta(c(beta)).
```

Because `balancedSlope(c) < 1 / 2`,

```text
c(beta) < thetaGlobal(beta) < beta.
```

Thus optimizing `sigma` strictly enlarges the permitted real-part cap range.

## Exact criterion

The global contour condition is equivalent to

```text
1 - beta < 2 * (beta - sigmaOpt),
```

which is equivalent to `sigmaOpt < c(beta)`. Since `B_beta` is strictly
decreasing and `B_beta(sigmaOpt) = beta - theta`, this is equivalent to

```text
theta < thetaGlobal(beta).
```

The resulting theorem is an iff, not only a sufficient condition.

## Boundary

This is an arithmetic improvement inside the formalized Carlson model. It
does not claim a stronger external zero-density theorem.
