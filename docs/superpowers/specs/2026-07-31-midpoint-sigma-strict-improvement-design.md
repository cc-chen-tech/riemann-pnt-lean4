# Midpoint Sigma Strict Improvement Design

## Goal

Prove a concrete improvement obtained by optimizing the density threshold
`sigma`, rather than adding another facade around the existing transfer.

## Arithmetic observation

Assume

```text
1 / 2 < theta < beta < 1
```

and choose

```text
sigma = ((1 / 2) + theta) / 2.
```

Then `1 / 2 < sigma < theta`. Relative to the cap-aligned baseline
`2 * (beta - theta)`:

- the low-layer ceiling `2 * (beta - sigma)` is strictly larger because
  `sigma < theta`;
- the Carlson ceiling is strictly larger because
  `max sigma theta = theta` and the balanced slope is strictly below `1 / 2`.

The unit cap is also strictly above the baseline because
`theta > 1 / 2` and `beta < 1`.

## Theorem chain

1. Define the explicit midpoint density threshold.
2. Prove it lies strictly between `1 / 2` and `theta`.
3. Prove the prescribed-cap outer-height ceiling at the midpoint is strictly
   larger than `2 * (beta - theta)`.
4. Under `theta < (3 * beta - 1) / 2`, choose `alpha` halfway between the
   baseline and the improved ceiling.
5. Construct `tau` and return
   `IsJointTwoHeightOuterExponentFeasible beta sigma tau alpha`.

The output is numerical input for the existing strict-margin constructor and
therefore for the actual transfer chain.

## Boundary

This slice proves a strict explicit improvement. It does not claim that the
midpoint is the globally maximizing density threshold. Determining the exact
optimizer requires balancing the decreasing low-layer ceiling against the
increasing Carlson ceiling on `1 / 2 < sigma < theta`.
