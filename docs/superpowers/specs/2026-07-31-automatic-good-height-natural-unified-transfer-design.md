# Automatic good-height natural unified transfer design

## Scope

The available uniform good-height theorem controls the explicit-formula
remainder only at natural evaluation points.  This stack keeps that domain
exact and combines it with the selected-height two-height zero tail.

## Automatic height envelope

The selected height is

```text
selection.height (x ^ alpha - 1).
```

For large `x`, the base is at least `8`; `selection.height_mem` then gives

```text
x ^ alpha - 1 <= H x <= x ^ alpha.
```

Hence `H` is eventually nonnegative and satisfies the stack41 polynomial
envelope condition automatically.

## Natural-point residual

- Stack41 gives real-variable full-tail decay, hence natural-point decay by
  sampling.
- The signed complement is dominated by the full-tail norm.
- The closed real-axis term also samples from its real-variable limit.
- `selectedUniformGoodHeight_actualNaturalRemainderCertificate` supplies the
  contour input at natural points.

## Output

Given a natural-point far witness for the visible cluster main, the result
returns:

- the existing fixed-rate natural-point PNT convergence;
- a half-target-amplitude far witness for the actual real PNT error.

## Boundary

The visible-cluster natural-point witness and the explicit high-layer cap
remain assumptions.  No real-variable remainder claim is made.
