# Improved Cap Automatic Reverse Zero-Free Design

## Goal

Complete the quantitative reverse direction throughout the strictly enlarged
real-part cap range.

## Inputs

- the improved cap hypothesis
  `theta < jointTwoHeightImprovedGlobalCapThreshold beta`;
- a global positive-zero real-part bound `rho.re <= theta`;
- an eventual actual relative-error coefficient `q < 1 / 2`;
- a unit visible-cluster witness whenever the enlarged finite-height
  right-edge cluster is nonempty.

## Construction

Stack63 automatically selects:

- a positive strict loss inside the global contour gap;
- the unique globally optimal density threshold;
- a compatible strip endpoint;
- the actual forward transfer at `alpha = globalCeiling - eta`.

If the enlarged right-edge cluster were nonempty, that transfer would produce
a half-target-amplitude far witness. The eventual `q < 1 / 2` upper bound
excludes it. Cluster emptiness then implies
`FiniteHeightRightEdgeZeroFree beta H`.

## Boundary

This theorem makes the improved-cap framework quantitatively bidirectional.
The visible-cluster witness remains conditional; no unconditional
anti-cancellation or RH conclusion is claimed.
