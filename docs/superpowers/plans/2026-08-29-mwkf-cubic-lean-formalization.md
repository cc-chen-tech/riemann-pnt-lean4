# MWKF cubic route Lean implementation plan

1. Add failing contract tests for gcd extraction, the shifted equation,
   Mobius convolution, finite shell aggregation, and final reassembly.
2. Implement `MWKFCubicStructural.lean` using only proved Mathlib arithmetic
   function, gcd, and finite-sum lemmas.
3. Implement `MWKFCubicAggregation.lean` using `IsLittleO.sum`, multiplication
   by the identity scale, and exact algebraic substitution.
4. Add axiom-audit modules and run the focused Lean checks.
5. Update the proof-status documentation with a machine-checked dependency
   table.  Do not call the final analytic theorem Lean-formalized until the
   MRSTT input itself has a checked implementation.
6. Commit, push, and open a ready-for-review stacked PR based on PR #483.
