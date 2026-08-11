# Real-ordinate-closed automatic transfer design

## Goal

Remove the real-ordinate complementary-zero hypothesis from the automatic
joint-parameter transfer by enlarging the visible cluster with the fixed
finite set of real-ordinate nontrivial zeros.

## Construction

Given a conjugation-invariant cluster `S`, use

`actualCarlsonAdjoinRealOrdinateZeros S`.

The existing finite-cluster API proves:

- conjugation invariance is preserved;
- `realOrdinateNontrivialZerosOutsideClusterFinset 0` of the enlarged cluster
  is empty.

Instantiate stack45 with this enlarged cluster. The empty residual supplies
the real-ordinate bound for every `beta`.

## Remaining inputs

The selected-height strip cap and visible-cluster natural-point witness remain
explicit and must both refer to the enlarged cluster. No claim is made that
either input follows from the adjunction operation.
