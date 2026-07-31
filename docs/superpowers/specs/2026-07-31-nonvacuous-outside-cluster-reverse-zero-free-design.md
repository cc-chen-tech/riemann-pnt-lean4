# Nonvacuous Outside-Cluster Reverse Zero-Free Design

## Goal

Derive finite-height right-edge zero freedom without assuming a real-part cap
on the target right-edge cluster itself.

## Exceptional cluster

For target exponent `beta` and height `H`, let

```text
S = rightEdgeNontrivialZerosFinset beta H.
```

Assume only

```text
PositiveOutsideClusterRealPartCap S theta.
```

This constrains positive-ordinate zeros outside `S`, but deliberately permits
members of `S` with real part at least `beta`. The desired conclusion
`S = empty` is therefore not contained in the cap hypothesis.

## Reverse chain

1. Run the stack76 automatic actual transfer with exceptional cluster `S`.
2. Enlarge `S` by the finite real-ordinate zero slice.
3. If the enlarged cluster is nonempty, use the visible-cluster input to
   obtain a unit target-amplitude main witness.
4. The actual transfer preserves half of that amplitude in the true PNT error.
5. An eventual actual-error upper coefficient `q < 1 / 2` contradicts the far
   half-amplitude witness.
6. The enlarged cluster is empty, hence `S` is empty and
   `FiniteHeightRightEdgeZeroFree beta H` follows.

## Significance

The previous global-cap reverse already excluded all nonreal right-edge zeros
because it assumed `rho.re <= theta < beta` for every positive zero. This
theorem removes that circularity: target-cluster zeros are genuine exceptions
until the PNT-error contradiction excludes them.

## Boundary

The positive outside-cluster cap and visible-cluster witness remain explicit
hypotheses. The theorem is nonvacuous but not unconditional.
