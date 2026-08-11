# Global real-part bound unified transfer design

## Goal

Turn a global real-part upper bound for positive nontrivial zeta zeros into
the complete automatic complement estimate used by the natural-point unified
PNT transfer.

## Analytic input

Assume:

- `2 / 3 < beta < 1`;
- `theta < (3 * beta - 1) / 2`;
- every nontrivial zero with positive imaginary part has real part at most
  `theta`.

## Transfer chain

1. Stack47 chooses `sigma`, `tau`, and `alpha` with `theta < tau < beta` and
   all low-layer/Carlson margins.
2. Membership in the selected outside-cluster positive-zero finset supplies
   nontrivial-zero status and positive imaginary part.
3. The global bound gives `rho.re <= theta < tau`, closing the strip cap.
4. Adjoining fixed real-ordinate zeros closes the real-axis residual.
5. The automatic good-height explicit-formula transfer leaves only the
   visible-cluster natural-point target-amplitude witness.

## Result boundary

The theorem returns fixed-rate natural-point relative PNT convergence and
half-target-amplitude oscillation transfer. It does not construct the
visible-cluster witness and does not assert an unconditional global zeta-zero
real-part bound.
