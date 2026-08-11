# Optimal common outer-height exponent design

## Goal

Replace existential outer-height choices by an explicit optimal ceiling for
the common low-layer and Carlson two-height transfer.

## Definitions

For fixed `beta`, `sigma`, and `tau`, define

`C = min 1 (min (2 * (beta - sigma)) ((beta - tau) / a(sigma)))`,

where `a(sigma)` is the balanced Carlson slope.

An outer exponent `alpha` is feasible when:

- `alpha <= 1`;
- `alpha / 2 + sigma - beta < 0`;
- the balanced target-amplitude Carlson exponent is negative.

## Correct optimality statement

The unit cap is closed while the two exponent constraints are strict.
Therefore the exact statement is:

- every `alpha < C` is feasible;
- every feasible `alpha` satisfies `alpha <= C`;
- a contour-compatible feasible exponent exists exactly when
  `1 - beta < C`.

Thus `C` is the supremal common outer-height exponent even when the endpoint
`alpha = 1` is attainable.

## Explicit feasibility criterion

For `1 / 2 < sigma < 1`, the contour floor lies below `C` exactly when:

- `0 < beta`;
- `sigma < (3 * beta - 1) / 2`;
- `a(sigma) * (1 - beta) + tau - beta < 0`.

This identifies the precise truncation-height obstruction rather than merely
constructing one midpoint witness.
