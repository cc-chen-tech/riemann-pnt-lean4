# Carlson's positive slope floor below a fixed target zero

## Result

On the right half of the critical strip, the classical Carlson slope is
antitone:

```text
1/2 <= sigma <= beta <= 1
  implies
4 * beta * (1 - beta) <= 4 * sigma * (1 - sigma).
```

Thus, for a fixed target real part `1/2 < beta < 1`, moving a strip threshold
`sigma` upward toward `beta` cannot make the density slope tend to zero.

Combining this with the contour requirement `1 - beta < alpha` and the exact
boundary-gap exponent gives the scale-independent necessary condition

```text
(4 * beta * (1 - beta)) * (1 - beta) < gap.
```

The module proves the same statement for scale-dependent `sigma(m)` and
`alpha(m)`, and derives a contradiction when `gap(m) -> 0`.

## Actual-zero consequence

The no-go theorem is instantiated with the selected finite-complement gap of
the actual dynamic equal-real-part zeta-zero package.  Even a moving family
of classical Carlson strips cannot control that package at target amplitude
if the selected gap tends to zero.

## Research boundary

This rules out a common but incorrect expectation: arbitrarily fine
near-boundary strip subdivision does not by itself remove the density cost.
At fixed `beta < 1`, Carlson's classical exponent retains a positive floor.

A viable transfer therefore needs an input stronger than the globally
aggregated classical Carlson estimate near the target boundary, such as a
local count whose effective density cost is genuinely `o(gap)`, or a
different cancellation mechanism.  No such input, unconditional Omega
theorem, or RH consequence is asserted here.
