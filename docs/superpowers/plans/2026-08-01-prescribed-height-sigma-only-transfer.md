# Prescribed-height sigma-only transfer implementation plan

1. Define the alpha-dependent anchor, inner exponent, reciprocal low-layer
   slack, selected height, running boundary, visible main, and amplitude.
2. Prove the anchor lies strictly between all fixed obstructions and one.
3. Prove `1 - beta_alpha <= alpha / 2` and construct the strict contour window
   below the prescribed outer exponent `alpha`.
4. Derive selected-height cofinality, the `x^alpha` ceiling, and the actual
   natural-point contour-remainder certificate.
5. Install these facts in the reciprocal monotone variable-boundary unified
   upper and conditional signed transfer.
6. Compile the implementation, contract, and axiom audit serially.
7. Publish documentation and Lean code as separate commits in a chained Draft
   PR based on Stack155.
