# Automatic joint-parameter unified transfer design

## Goal

Consume the joint numerical feasibility theorem to remove all separate
low-layer and Carlson margin parameters from the public automatic
good-height unified transfer interface.

## Interface boundary

The theorem returns `sigma`, `tau`, and `alpha` with:

- `1 / 2 < sigma < tau < beta`;
- `1 - beta < alpha`;
- `0 < alpha <= 1`.

For these automatically chosen parameters it packages a transfer implication
whose remaining inputs are exactly:

- the selected-height strip cap from `sigma` to `tau`;
- the real-ordinate complementary-zero bound;
- the visible-cluster natural-point target-amplitude witness.

The balanced cuts and strict margins are hidden internal witnesses.

## Data flow

1. Apply `exists_jointTwoHeightTargetAmplitudeParameters`.
2. Retain `sigma`, `tau`, and `alpha` in the public existential result.
3. Use the hidden cuts, epsilons, and four negative exponent inequalities to
   instantiate `unified_automaticGoodHeight_twoHeight_naturalTargetTransfer`.
4. Return the existing pair of conclusions:
   fixed-rate natural-point relative PNT convergence and half-target-amplitude
   oscillation transfer.

## Non-claims

This theorem does not prove the strip cap, the real-ordinate bound, or the
visible-cluster witness. It does not modify the complementary-zero or
sharp-oscillation developments.

