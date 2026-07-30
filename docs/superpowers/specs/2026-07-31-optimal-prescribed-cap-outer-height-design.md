# Optimal prescribed-cap outer-height design

## Goal

Optimize the Carlson strip endpoint `tau` away when a prescribed global
real-part ceiling `theta` must lie below it.

## Optimized ceiling

For fixed `beta`, `sigma`, and `theta`, define

`C_theta = min 1 (min (2 * (beta - sigma))
  ((beta - max sigma theta) / a(sigma)))`.

Here `a(sigma)` is the balanced Carlson slope.

## Feasibility

An exponent `alpha` is prescribed-cap feasible when there exists `tau` such
that:

- `sigma < tau`;
- `theta < tau`;
- `tau < beta`;
- `alpha` is feasible for the fixed-endpoint joint low/Carlson constraints.

## Optimality

For `beta < 1` and the contour floor `1 - beta < alpha`:

- every `alpha < C_theta` admits an explicit feasible `tau`;
- every prescribed-cap feasible `alpha` satisfies `alpha <= C_theta`;
- a contour-compatible pair `(alpha, tau)` exists exactly when
  `1 - beta < C_theta`.

The constructive endpoint is the midpoint between `max sigma theta` and
`beta - a(sigma) * alpha`.

## Explicit criterion

The contour floor lies below the optimized ceiling exactly when:

- `0 < beta`;
- `sigma < (3 * beta - 1) / 2`;
- `a(sigma) * (1 - beta) + max sigma theta - beta < 0`.

