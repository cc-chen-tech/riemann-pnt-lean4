# Complementary zero package: fixed-gap local L2 model

## Proved in this branch

Let the selected package contain every height-`T` zero with real part
exactly `beta`. Assume that every remaining zero satisfies

```text
Re rho <= beta - delta
```

for one fixed `delta > 0`. Uniformly for

```text
T in [exp (a / 2), exp (a / 2) + 1],
```

the normalized complementary-zero second moment on `[a, a + L]` tends to
zero:

```text
integral |exp (-beta y) * complement(exp y, T, beta)|^2 dy = o(1).
```

The proof combines the repository's multiplicity-weighted reciprocal-zero
`O(log^2 T)` bound with exponential decay `exp (-delta y)`. The module also
proves:

- equality between the arbitrary selected-cluster complement and the
  equal-real-part complement;
- a uniform pointwise normalized bound;
- an explicit local second-moment envelope;
- the pointwise three-component square bound for the actual no-jump
  remainder.

## Exact remaining obstruction

At each fixed height, finiteness supplies a positive gap below the maximal
real-part layer. This does not provide one `delta > 0` valid while
`T` moves with `a`. The gap may shrink faster than the logarithmic
reciprocal-zero budget can absorb.

Consequently this branch is a conditional fixed-gap closure, not an
unconditional fixed-length-window oscillation theorem. It does not produce a
Carlson contradiction or prove RH.

Removing the hypothesis requires a collision-safe moving-layer estimate,
such as a dynamic real-part decomposition or a local large-sieve bound for
the high-zero tail.
