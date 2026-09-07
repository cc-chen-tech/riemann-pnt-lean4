# MWKF cubic route Lean implementation plan

1. Add failing contract tests for gcd extraction, the shifted equation,
   Mobius convolution, finite shell aggregation, and final reassembly.
2. Implement `MWKFCubicStructural.lean` using only proved Mathlib arithmetic
   function, gcd, and finite-sum lemmas.
3. Implement `MWKFCubicAggregation.lean` using `IsLittleO.sum`, multiplication
   by the identity scale, and exact algebraic substitution.
4. Add axiom-audit modules and run the focused Lean checks.
5. Update the proof-status documentation with a machine-checked dependency
   table. Do not claim the asymptotic proved or Lean-formalized until the
   actual main-term limit and full-weight remainder estimate have valid
   proofs and checked implementations. Parent-PR completion labels are not
   evidence of those proofs.
6. Commit, push, and open a ready-for-review stacked PR based on PR #483.

Review gate (2026-08-30): the stacked base does not authorize incorporating
#483's disputed analytic claims into main. Freeze independently verified
local Lean results and audit their minimal main-relative dependencies before
integration. Only the limit order actually needed by the final expression
is required; arbitrary exchanges of depth and height are not a goal.
