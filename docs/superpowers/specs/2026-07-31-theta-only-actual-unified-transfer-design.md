# Theta-Only Actual Unified Transfer Design

## Goal

Run the actual globally optimized transfer from a prescribed real-part cap
without requiring the caller to choose `beta`, `sigma`, `tau`, `alpha`, or
any epsilon loss.

## Input

- `1 / 2 < theta < 1`;
- a conjugation-invariant base cluster;
- a global bound `rho.re <= theta` for positive nontrivial zeros.

## Automatic parameter chain

1. Invert the improved threshold to obtain the unique boundary
   `betaBoundary` with
   `thetaGlobal(betaBoundary) = theta`.
2. Select
   `beta = (betaBoundary + 1) / 2`, so
   `theta < thetaGlobal(beta)`.
3. Use the improved-cap theorem to select a positive contour loss `eta`.
4. Select the unique globally optimal density threshold `sigma`.
5. Construct `tau`, balanced cuts, and strict margins.
6. Run the actual selected-good-height explicit-formula transfer at
   `alpha = globalCeiling(beta, theta) - eta`.

## Result

The theorem returns every selected parameter and its defining relation. For
every good-height selection, a visible-cluster witness at the selected
target exponent implies:

- natural-point relative PNT error convergence;
- an actual half-target-amplitude far witness.

## Boundary

All numerical optimization is automatic and auditable. The visible-cluster
anti-cancellation witness remains explicit.
