# Dynamic-boundary PNT upper transfer

## Statement

Define `DynamicBoundaryPackageCoefficientCap beta H C` to mean that the
coefficient mass of the moving equal-real-part package is eventually at most
`C`.

If the full explicit-formula residual is

```text
o(x^(beta - 1))
```

and this cap holds, then for every `eta > 0`,

```text
|relativeChebyshevPsi0Error(m)|
  < (C + eta) * m^(beta - 1)
```

for all sufficiently large natural `m`.

The automatic theorem discharges the residual using the same height schedule,
Carlson strip margin, right-edge hypotheses, and contour certificate as the
lower transfer.

## Honest remaining upper-side bridge

The current theorem does not claim that zero density alone proves a uniform
coefficient cap.  Existing boundary-mass comparisons in the repository are
primarily lower bounds on finite cluster coefficient mass.  An automatic cap
requires a separate argument that dominates the moving package by a summable
global boundary-zero weight, including real-ordinate zeros.

This distinction prevents a one-sided comparison from being silently used in
the wrong direction.

## Unified role

The lower transfer consumes a far witness for the same moving package and
preserves its coefficient up to arbitrary loss.  The upper transfer consumes a
uniform coefficient cap for that package and enlarges it by arbitrary `eta`.
Both use the identical explicit-formula residual theorem.
