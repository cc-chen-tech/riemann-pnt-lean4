# Actual Dynamic-Boundary Reciprocal Transfer Design

## Goal

Propagate the Stack150 reciprocal low-layer estimate through the exact
explicit formula and the existing upper/lower transfer machinery, replacing
the old margin `sigma - beta + alpha + epsilon < 0` by
`sigma - beta + epsilon < 0` in the actual PNT transfer.

## Architecture

The existing transfer already separates into reusable components:

1. positive zero complement;
2. real-ordinate complement;
3. closed real-axis term;
4. selected-height contour remainder;
5. package coefficient cap and package main witness.

Stack150 changes only component 1. This stack builds a parallel chain rather
than editing the old one:

```text
reciprocal positive tail
  -> signed complement negligible
  -> explicit-formula residual negligible
  -> automatic upper and witness transfer
  -> bidirectional and coefficient-cap facades.
```

## Improved interface

The height assumptions remain:

```text
H(m) <= m^alpha eventually
H(m) -> infinity
0 < alpha.
```

They are still needed for selected-height and contour control. The low-layer
power margin is now independent of `alpha`:

```text
0 < epsilon
sigma - beta + epsilon < 0.
```

This strict margin implies `sigma < beta`, so the existing Carlson package
coefficient cap remains automatic.

## Claim boundary

The upper conclusion is unconditional under the stated right-edge and
selected-height inputs. Lower conclusions remain conditional on a far witness
for the moving visible package. This stack does not construct that witness,
prove RH, or prove an unconditional Omega theorem. It does not modify
protected, Sharp, or VK-edge modules.
