# Moving Right-Edge Unified Transfer Design

## Goal

Connect the moving right-edge complementary-zero estimate to the actual PNT
lower-transfer machine with no zero-free or outside-cap hypothesis.

## Fixed-parameter transfer

Let

```text
H(x) = selectedUniformGoodHeight alpha selection x
```

and use the moving exceptional cluster with real-part threshold `tau`.
The actual relative PNT error splits exactly into:

- the moving visible-cluster main;
- the closed real-axis term;
- the selected-height contour remainder;
- the moving outside-cluster complement.

The last three terms are negligible relative to
`targetZeroPowerAmplitude beta`. Therefore a far unit-amplitude natural-point
witness for the moving main yields a far half-amplitude witness for the actual
PNT error.

## Automatic parameters

For `2 / 3 < beta < 1`, use the existing two-height parameter selector with
the purely numerical anchor `1 / 2`. The condition

```text
1 / 2 < (3 * beta - 1) / 2
```

follows from `2 / 3 < beta`.

The system then returns:

- `1 / 2 < sigma < tau < beta`;
- `1 - beta < alpha`;
- all low-layer, high-strip, and contour margins.

No zero-location cap is supplied. Zeros with real part at least `tau` enter
the moving main, while Carlson controls the complement.

## Unified output

For every good-height selection, a moving-main witness gives:

- natural-point relative PNT convergence to zero;
- an actual half-target-amplitude far witness.

## Boundary

The sole lower-direction input is now the moving visible-cluster
anti-cancellation witness. Proving that witness is the remaining oscillation
problem.
