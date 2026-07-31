# Boundary-captured moving-seed signed PNT transfer

## Objective

Compose the target-line finite-seed selector, the cancellation-free boundary
extension budget, and the signed moving-seed explicit-formula transfer.

Given `0 < q < c`, the finite capture is chosen so that

`2 * boundaryMass < c - q`.

The moving extension therefore costs strictly less than `(c - q)` times the
target amplitude.  Positive and negative visible-main witnesses of coefficient
`c` for the captured cluster transfer to signed actual PNT witnesses of
coefficient `q / 2`.

## Automatic parameters

For `2 / 3 < beta < 1`, reuse the joint two-height parameter selector to
produce `sigma`, `tau`, `alpha`, and the low/high splitting parameters.  The
same `sigma` controls the finite Carlson capture and the residual boundary
mass; the selected good-height schedule uses `alpha`.

## Theorem chain

1. Select all admissible two-height parameters.
2. Enlarge the original seed to a target-line Carlson capture cluster.
3. Use the exact remaining boundary gap as the positive loss parameter in the
   full outside absolute-mass estimate.
4. Dominate the moving right-edge extension and remove the normalization using
   positivity of the target amplitude.
5. Apply the signed moving-seed transfer with loss `c - q`; its net coefficient
   is `q`, and the explicit-formula transfer contributes the final factor
   `1 / 2`.

## Claim boundary

The theorem requires positive and negative visible-main witnesses for the
captured cluster.  It does not derive those witnesses from the original seed,
does not prove an unconditional `Omega` theorem, and does not imply RH.

