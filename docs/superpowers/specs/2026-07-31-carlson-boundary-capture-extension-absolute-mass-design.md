# Carlson boundary capture for extension absolute mass

## Objective

Replace stack86's pointwise strict condition `Re rho < beta` by the natural
non-strict cap `Re rho <= beta`.  Residual zeros on the boundary do not decay
after normalization by `x^(beta - 1)`; their dyadic reciprocal mass is instead
made arbitrarily small by finite cluster capture.

## Theorem chain

1. Bound the complete finite positive-ordinate absolute mass by the canonical
   low layer plus the non-strict Carlson kernel tail.
2. Combine low-layer decay with convergence of that tail to
   `actualCarlsonOutsideClusterBoundaryMass beta S`.
3. Use conjugation and strict decay of the real-ordinate slice to bound the
   complete outside absolute mass by twice the boundary mass, up to any
   positive loss.
4. Dominate every moving finite extension by the complete outside absolute
   mass.
5. Apply the finite seed gap-transfer cluster theorem to choose a
   conjugation-stable enlargement whose residual extension budget is strictly
   below a prescribed gap `c - q`.

## Claim boundary

This closes a cancellation-free upper bound for residual moving extensions.
It does not prove that a visible oscillation witness for the original seed
survives after adding boundary zeros to the main cluster.  Any signed PNT
transfer must use a witness for the enlarged captured cluster, or separately
prove such witness stability.

