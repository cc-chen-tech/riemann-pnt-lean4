# Global Optimal Quantitative Reverse Zero-Free Design

## Goal

Use the globally optimized actual transfer in the reverse direction: an
eventual actual-error coefficient below one half excludes a finite-height
right-edge zero cluster.

## Inputs

- the global optimizer regime `2 / 3 < beta < 1` and
  `1 / 2 < theta < beta`;
- a strict truncation loss below the global contour gap;
- a global positive-zero real-part cap `rho.re <= theta`;
- an eventual actual relative-error upper bound

```text
|relativeError(x)| <= q * targetAmplitude(beta, x)
```

with `q < 1 / 2`;
- a unit visible-cluster witness whenever the enlarged finite-height
  right-edge cluster is nonempty.

## Contradiction

If the enlarged cluster were nonempty, the global actual transfer would
produce a far witness

```text
|relativeError(x)| >= (1 / 2) * targetAmplitude(beta, x)
```

at arbitrarily large scales. Eventual positivity of the target amplitude and
`q < 1 / 2` contradict the assumed upper bound.

The enlarged cluster is therefore empty, so its right-edge subcluster is
empty. The existing finset characterization gives
`FiniteHeightRightEdgeZeroFree beta H`.

## Boundary

The result is quantitatively bidirectional at the globally optimized height,
but the visible-cluster unit witness remains conditional. No unconditional
anti-cancellation theorem is claimed.
