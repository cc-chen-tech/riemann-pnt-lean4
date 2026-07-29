# VK-edge finite-height approximation: local L2 status

## Proved in this branch

Fix `1 / 2 < beta < 1`, a logarithmic window length `L >= 0`, and
`eta > 0`. For every sufficiently large left endpoint `a`, one height

```text
T in [exp (a / 2), exp (a / 2) + 1]
```

is a `goodHeight` and makes the normalized finite-height
explicit-formula approximation error satisfy

```text
integral from a to a + L of |A_T,beta(y)|^2 dy < eta.
```

The same height works over the whole interval. The proof is the local
second-moment consequence of the uniform pointwise estimate in
`ExplicitFormulaNormalizedWindowRemainder`.

## What this does not prove

The selected-zero-cluster remainder is the sum of:

1. the unselected complementary-zero contribution;
2. the finite-height approximation error controlled here;
3. the elementary closed terms, whose local second moment already decays.

This branch does not bound item 1. It therefore does not prove an
unconditional fixed-length-window oscillation theorem, a contradiction with
Carlson zero density, or RH.

## Remaining analytic blocker

At the moving height `T` of size `exp (a / 2)`, control

```text
integral from a to a + L of
  |normalized complementary-zero contribution|^2 dy
```

by a uniform positive margin below the selected cluster's coercivity budget.
A fixed-height real-part gap is insufficient because the maximal layer and
its gap may change with `T`.
