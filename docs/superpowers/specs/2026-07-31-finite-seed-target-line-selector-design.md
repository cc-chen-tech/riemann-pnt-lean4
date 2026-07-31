# Finite-seed Carlson target-line selector

## Objective

Turn the existing zero-supported finite-seed Carlson transfer cluster into a
cluster accepted by the moving-seed transfer interface.  Every member of the
final cluster must be a nontrivial zeta zero with real part exactly `beta`.

## Construction

1. Use `exists_zeroSupportedExtension_actualCarlsonFiniteSeedGapTransferCluster`
   to obtain a conjugation-stable transfer cluster `T` containing the seed.
2. Define the final cluster as
   `actualCarlsonBoundaryClusterPart beta T`.
3. The original target-line seed survives this filter.
4. Zero support for new members comes from the zero-supported extension
   certificate; real part `beta` is supplied by the boundary filter.
5. The outside real-part cap survives: a zero removed from `T` is outside the
   original seed and is therefore still bounded by the original cap.
6. Real-ordinate residual zeros are strictly left of `beta`: if such a zero
   lies in `T` at equality it would have survived the filter; if it lies
   outside `T`, the previous selector's strict certificate applies.
7. Boundary filtering preserves the Carlson boundary mass exactly, hence the
   strict coefficient gap is unchanged.

## Claim boundary

This selector does not construct positive or negative oscillation witnesses.
It only produces a finite target-line main cluster with all certificates
needed by later cancellation-free moving-extension and signed-transfer steps.

