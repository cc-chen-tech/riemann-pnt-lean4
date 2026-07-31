# Cubic Strict Theta-Only Actual Transfer Design

## Goal

Run the actual Pintz-Carlson-explicit-formula transfer with the cubic-strict
target exponent rather than the asymptotically coarse midpoint selector.

## Inputs

- `1 / 2 < theta < 1`;
- a conjugation-invariant finite zero cluster;
- a global positive-zero real-part bound `rho.re <= theta`;
- the existing visible-cluster natural-point witness.

## Automatic chain

The cubic-strict selector supplies a target `beta` satisfying

```text
betaBoundary < beta < betaMidpoint < 1
```

and

```text
theta < jointTwoHeightImprovedGlobalCapThreshold beta.
```

The existing improved-cap transfer then selects:

- a strict loss `eta`;
- the globally optimal density threshold `sigma`;
- an intermediate strip endpoint `tau`;
- the outer truncation exponent `alpha`;
- a uniform good-height transfer for the actual zeta kernel and actual PNT
  error.

## Output

The theorem returns all selected parameters and their defining equalities,
including the pointwise improvement over the midpoint target. For each
good-height selection, a visible-cluster witness yields:

- natural-point relative PNT error tending to zero;
- a half-target-amplitude far witness at the cubic-strict exponent.

## Boundary

The target exponent now has cubic rather than linear slack, but the
visible-cluster anti-cancellation witness remains explicit. This module does
not prove an unconditional oscillation theorem or RH.
