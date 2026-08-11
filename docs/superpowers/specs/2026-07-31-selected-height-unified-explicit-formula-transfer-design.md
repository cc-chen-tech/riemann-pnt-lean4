# Selected-height unified explicit-formula transfer design

## Scope

This stack replaces the fixed polynomial remainder certificate in stack40
with an actual selected-height certificate while retaining the polynomial
height only as the zero-density envelope.

## Inputs

- `H x` is eventually nonnegative and at most `x ^ alpha`;
- stack36/37 two-height margins hold;
- the selected outside-cluster high layer has real-part cap `tau`;
- the cluster is conjugation invariant and the real-ordinate residual lies
  strictly left of `beta`;
- `ActualSelectedHeightExplicitFormulaRemainderCertificate alpha H`;
- the visible selected-height cluster has a far target-amplitude witness.

## Transfer

Stack41 gives full selected-height zero-tail negligibility.  The signed
complement is dominated by that norm.  The closed real-axis and selected
remainder terms are negligible by existing theorems.  The exact explicit
formula at height `H x` then feeds the existing unified upper/lower transfer.

## Output

One theorem returns:

- fixed-rate natural-point PNT convergence;
- a half-target-amplitude far witness for the actual relative PNT error.

## Boundary

The good-height certificate and visible-cluster witness remain explicit
inputs.  This stack makes their height parameter consistent with the
two-height zero-tail proof.
