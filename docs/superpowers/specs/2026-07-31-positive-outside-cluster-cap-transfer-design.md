# Positive Outside-Cluster Cap Transfer Design

## Problem

The existing automatic reverse chain assumes a global real-part cap on every
positive-ordinate nontrivial zero. Its automatically selected target satisfies
`theta < beta`, so the cap already excludes every nonreal right-edge zero.
Only the separately adjoined real-ordinate slice remains nontrivial.

That interface is therefore too strong for a genuine exceptional-zero reverse
argument.

## New cap

Define

```text
PositiveOutsideClusterRealPartCap S theta
```

to mean that every positive-ordinate nontrivial zero outside the distinguished
finite cluster `S` has real part at most `theta`.

Zeros in `S` are deliberately exempt. In particular, `S` may contain zeros
with real part at or beyond the target exponent `beta`.

## Transfer chain

For `2 / 3 < beta < 1` and the usual Carlson feasibility inequality:

1. select the same automatic two-height parameters `sigma`, `tau`, `alpha`;
2. adjoin every real-ordinate nontrivial zero to `S`;
3. lift the positive outside-cluster cap from `S` to the enlarged cluster;
4. use the cap to close the selected-height high strip;
5. use the adjoin construction to make the real-ordinate outside residual
   empty;
6. run the existing automatic-good-height actual PNT bidirectional transfer.

## Output

The theorem returns actual relative PNT decay and the half-target-amplitude
lower transfer, conditional on the same visible-cluster witness as before.

## Significance

Unlike the global-cap theorem, this interface does not assume away the target
cluster. It is the correct input for a nonvacuous exceptional-cluster reverse
theorem.

## Boundary

The outside-cluster cap is still a mathematical hypothesis. This PR does not
derive it from Carlson density and does not prove visible-cluster
anti-cancellation.
