# Balanced-Rate Grid Approximation

## Goal

Quantify how well a finite Pintz rate grid approximates the continuous
classical contour/zero-free envelope optimizer.

## Continuous envelope

For zero-free parameter `b > 0`, the common decay rate at height rate `k` is

```text
classicalDynamicBalancedRate b k = min k (b / k).
```

Under `0 < k <= 1`, its exact maximum is attained at

```text
rStar = classicalAdmissibleBalancedRate b = min 1 (sqrt b).
```

## Quantitative finite-grid statement

Suppose `q >= 1` and the finite grid contains a rate

```text
rStar / q <= k <= rStar.
```

Because `k` lies below the balanced point, `b / k >= k`, so its envelope rate
is exactly `k`. Consequently the candidate and the grid envelope optimizer
retain at least `rStar / q` of the optimal exponential rate, while no
admissible grid rate exceeds `rStar`.

The competing exponential terms are therefore bounded by

```text
2 * exp (-(rStar / q) * u).
```

## Boundary

This is a quantitative approximation theorem for the continuous analytic
envelope. It does not assume that the actual zero-counting budget or classical
good-height selector is continuous in the rate. Transfer back to the full
actual budget remains a separate theorem.
