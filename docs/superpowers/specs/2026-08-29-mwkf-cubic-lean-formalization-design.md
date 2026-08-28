# MWKF cubic route: Lean formalization design

## Goal

Formalize the exact, repository-local implication chain used by the cubic
complementary-divisor proof of the `N = floor(T^3)` mollified second moment.
No theorem may contain `sorry` or `admit`, and no analytic input may be hidden
behind a newly declared `axiom`.

## Boundary of the first stacked PR

The first PR proves the parts that can be checked against the current Mathlib
dependency without first constructing a new automorphic-forms library:

1. exact gcd extraction `d = q*r`, `e = q*s`, `(r,s)=1`;
2. exact shifted/complementary-divisor equation equivalences;
3. the finite Mobius level recombination `((mu * mu) * 1)(n) = mu(n)`;
4. disjoint finite-shell reindexing and finite sums of little-o terms;
5. the algebraic final reassembly from an exact decomposition, main-term
   asymptotic, and remainder little-o statement.

The cubic MRSTT decorrelation input is not currently present in Mathlib.  It
will therefore be named as a hypothesis of an implication theorem, never as a
global axiom and never as an unconditional Lean theorem.  Replacing that
hypothesis by a checked theorem requires a subsequent automorphic/ergodic
formalization layer.

## Module layout

- `PrimeNumberTheorem.MWKFCubicStructural`: finite arithmetic and reindexing.
- `PrimeNumberTheorem.MWKFCubicAggregation`: little-o aggregation and final
  asymptotic reassembly.
- matching contract and axiom-audit modules under `Test/`.

## Verification contract

- focused `lake env lean` for every new module and test;
- `#print axioms` audit for every public theorem;
- repository scan forbidding `sorry`, `admit`, and `axiom` in the new files;
- `git diff --check`.
