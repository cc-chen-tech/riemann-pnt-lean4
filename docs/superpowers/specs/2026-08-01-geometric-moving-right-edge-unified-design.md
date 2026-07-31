# Geometric Moving Right-Edge Unified Transfer Design

## Objective

Remove the Carlson-indexed visible right-edge hypothesis from the canonical
good-height moving transfer.  Replace it by the direct finite-zero statement
`IsVariableBoundaryRightEdge H beta`.

## Construction

For an `ActualCarlsonPositiveZeroIndex sigma`,
`actualCarlsonPositiveZero_spec` supplies an actual nontrivial zeta zero with
positive imaginary part.  If its absolute ordinate is visible below `H(m)`,
it belongs to `positiveNontrivialZerosFinset (H(m))`.  The geometric right-edge
hypothesis therefore bounds its real part by `beta(m)`, exactly producing
`IsIndexedVariableBoundaryVisibleRightEdge`.

Add a facade over the Stack 113 theorem that performs this conversion and
otherwise preserves every assumption and conclusion.

## Public declarations

- `IsVariableBoundaryRightEdge.toIndexedVisible`
- `actualMonotoneGeometricVariableBoundaryCanonicalGoodHeightUnifiedUpperSignedOmega`

## Claim boundary

This bridge removes an indexing artifact; it does not construct `beta`, prove
sampled monotonicity, supply an eventual lower anchor, or prove either signed
main-term witness.  It is not an unconditional Omega theorem and does not imply
RH.  No protected complementary-bound or Sharp/VK-edge module is modified.

## Verification

Compile implementation, contract, and axiom audit directly and sequentially.
The audit allowlist is `propext`, `Classical.choice`, and `Quot.sound`.
