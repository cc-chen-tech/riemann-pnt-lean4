# Variable-Boundary Positive-Tail Index Bridge Design

## Goal

Prove the concrete missing bridge from the finite high positive-zero family at
the current height to stack101's visible Carlson `tsum`, then derive the
positive-tail low/high split required by stack105.

## Method

Map `actualHighPositiveZeroSubtypeFinset` through the existing Carlson index
embedding. Every mapped zero is visible at the current height and lies outside
the moving package. Its normalized kernel therefore equals the corresponding
visible Carlson term. Summability follows from stack101's weight domination,
so `Summable.sum_le_tsum` bounds the finite sum. A finite low/high partition
and the triangle inequality then yield `positive <= low + visible`.

## Claim boundary

This closes the high-strip indexing bridge. Decay of the explicit low-strip
majorant remains separate. The result does not construct a moving main witness,
prove both signs, or imply RH.
