# MWKF cubic route: Lean formalization design

## Goal

Formalize independently valid local steps and the exact implication chain
for the `N = floor(T^3)` mollified second moment. The parent cubic proof
candidate has unresolved normalization and outer-aggregation issues; its
completion certificate is not a mathematical input.
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

The required full-weight cubic Mobius decorrelation estimate is not proved
here. Naming an MRSTT route does not establish its applicability. The actual
main-term limit and remainder little-o statement remain local hypotheses,
never global axioms. Removing these hypotheses requires a valid analytic
proof with all physical normalizations and outer sums, followed by its Lean
formalization; it is not merely a missing library translation.

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
