# Near-optimal sigma-only transfer implementation plan

1. Import the Stack153 sigma-only facade and Stack154 contour-infimum module.
2. Define `delta`-parameterized inner/outer exponents, selected height, running
   boundary, visible main, and target amplitude.
3. Reuse the automatic reciprocal anchor proof and the near-optimal contour
   window theorem to establish all arithmetic side conditions.
4. Prove selected-height cofinality, the polynomial ceiling, and the actual
   natural-point contour-remainder certificate.
5. Prove arbitrary positive tolerance admits a selected-height window within
   that tolerance of `1 - beta0`.
6. Apply the reciprocal monotone variable-boundary unified transfer with the
   new height.
7. Compile the implementation, contract, and axiom audit with one low-priority
   Lean process at a time.
8. Publish design and implementation as separate commits in a chained Draft
   PR based on Stack154.
