# Prescribed-cap joint feasibility design

## Goal

Strengthen joint two-height feasibility so a prescribed global zero real-part
ceiling `theta` lies strictly below the selected Carlson strip endpoint
`tau`, while retaining one common `alpha` and all four negative margins.

## Hypothesis

The exact useful range is

`theta < (3 * beta - 1) / 2`

with `2 / 3 < beta < 1`.

## Construction

1. Choose `sigma` between `1 / 2` and `(3 * beta - 1) / 2`.
2. The balanced Carlson slope is below `1 / 2`, so its admissible `tau`
   ceiling is strictly above `(3 * beta - 1) / 2`.
3. Choose `tau` between `max sigma theta` and that admissible ceiling.
4. Choose one `alpha` below the low-layer, Carlson, and unit ceilings.
5. Generate the balanced cuts and positive margins as in stack44.

## Downstream consequence

If every relevant outside-cluster zero satisfies `rho.re <= theta`, the new
fact `theta < tau` immediately supplies the selected-height strip cap.

This module proves only the numerical statement; the global zero real-part
bound remains an explicit analytic input.

