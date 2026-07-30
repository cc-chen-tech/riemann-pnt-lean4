# Near-optimal truncation parameters design

## Goal

Turn the optimized prescribed-cap ceiling into explicit parameter witnesses
usable by the actual transfer theorems.

## Fixed-exponent margin extraction

For a feasible fixed outer exponent `alpha`, set:

- `gammaLow = alpha / 2`;
- `gammaHigh = carlsonTwoHeightBalancedCut sigma alpha`;
- `epsilonLow` to half the negative balanced low exponent;
- `epsilonHigh` to half the negative balanced Carlson exponent.

This yields all positivity, cut, and four strict-margin facts required by the
existing two-height transfer.

## Near-optimal choice

Let

`C = jointTwoHeightPrescribedCapOuterExponentCeiling beta sigma theta`.

For every

`0 < eta < C - (1 - beta)`,

choose

`alpha = C - eta`.

Then `1 - beta < alpha < C`. The optimized-ceiling theorem constructs an
endpoint `tau` above both `sigma` and `theta`, and the fixed-exponent theorem
constructs both cuts and margins.

## Result

The output is a complete transfer-ready parameter tuple whose outer-height
exponent is exactly `eta` below the proven supremum.

