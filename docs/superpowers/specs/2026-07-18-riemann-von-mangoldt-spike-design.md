# Riemann-von Mangoldt Feasibility Spike Design

## Objective

Establish the smallest verified Lean 4 bridge needed to justify further work on
the Riemann-von Mangoldt formula. The spike must connect a multiplicity-weighted
one-sided zeta zero count to a rectangle boundary integral of the logarithmic
derivative of the completed zeta function, and expose the exact Gamma-factor
decomposition needed for the later main-term calculation.

This is a feasibility gate, not a commitment to prove the full asymptotic
formula in this branch.

## Scope

The spike has exactly three mathematical deliverables:

1. A standard one-sided zero-counting function `riemannZeroCount T`, counting
   nontrivial zeta zeros with `0 < Im rho` and `Im rho <= T`, with analytic
   multiplicity.
2. A proved rectangle argument-principle identity for the project completed
   zeta function between two pole-free good heights. The residue sum must be
   identified with `riemannZeroCount T - riemannZeroCount U` (or the equivalent
   natural-number equality before casting).
3. A proved exact logarithmic-derivative decomposition of completed zeta into
   the zeta logarithmic derivative, the two elementary factors, and the Gamma
   factor. No asymptotic estimate is required in this spike.

Every exported result must be a Lean theorem with a proof. The branch must not
introduce a `def ... : Prop` target as a substitute for any deliverable.

## Chosen Route

Use the existing project-specific finite-principal-part machinery rather than
building a general argument principle for arbitrary meromorphic functions.
The relevant proved template is:

- `PrimeNumberTheorem.ExplicitFormulaResidues.
  exists_finite_explicitFormulaIntegrand_analytic_regularized_remainder`;
- `MathlibAux.boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn`;
- the assembly pattern in `PrimeNumberTheorem/FirstOrderExplicitFormula.lean`.

For completed zeta, form the finite divisor support on a compact rectangle,
subtract at every zero the simple principal part

```text
(z - rho)^(-1) * analyticOrderNatAt completedZeta rho,
```

and use `toMeromorphicNFOn` to obtain one analytic remainder on the rectangle.
This directly proves the boundary integral identity without depending on the
unproved general predicate
`MathlibAux.rectangleIntegral_meromorphic_eq_residue_sum`.

## Rectangle Geometry

Do not start at height zero. The spike uses two heights `U < T` satisfying the
existing `ExplicitFormulaAux.goodHeight` predicate and takes the rectangle

```text
0 <= Re s <= 1,   U <= Im s <= T.
```

This choice has three advantages:

- the horizontal edges contain no nontrivial zeta zeros by `goodHeight`;
- the vertical edges contain no completed-zeta zeros, using zeta nonvanishing
  on `Re s = 1` and the completed-zeta functional equation for `Re s = 0`;
- the interior zeros are exactly the nontrivial zeta zeros whose ordinates lie
  strictly between `U` and `T`.

The eventual all-height Riemann-von Mangoldt formula can recover arbitrary
heights using monotonicity and the existing local `O(log T)` zero-count bound.
That extension is explicitly outside this spike.

## Components

### Zero count

Create a focused module under `PrimeNumberTheorem/RiemannVonMangoldt/` defining
`riemannZeroCount : Real -> Nat` from `nontrivialZerosFinset`. Prove:

- a membership-normal-form lemma for the filtered finset;
- nonnegativity and monotonicity;
- a finite-sum expression for the count difference between two heights;
- compatibility with `analyticOrderNatAt riemannZeta`.

The definition must count multiplicity, not merely distinct zeros.

### Completed zeta core

Reuse `RiemannHypothesis.completedZeta`; do not add a competing xi definition.
Prove the minimal facts needed by the contour argument:

- completed zeta is entire;
- on `0 < Re s < 1`, completed zeta vanishes exactly when zeta vanishes;
- multiplicities agree there;
- completed zeta has no zeros on `Re s = 0` or `Re s = 1`;
- its logarithmic derivative has residue equal to the analytic zero
  multiplicity.

If importing `RiemannExplorer` creates an avoidable dependency cycle, move the
existing definition and its functional equation to a small core module and
leave a compatibility import. Do not duplicate the definition.

### Rectangle count identity

Adapt the existing explicit-formula regularization pattern specifically to
`logDeriv RiemannHypothesis.completedZeta`. The exported theorem must state an
actual equality between:

- `MathlibAux.boundaryRectIntegral` of the completed-zeta logarithmic
  derivative on the good-height rectangle; and
- `2 * pi * I` times the cast of the multiplicity count in its interior.

A second theorem may rewrite the interior multiplicity sum as
`riemannZeroCount T - riemannZeroCount U` under the ordered good-height
hypotheses. This is part of the same deliverable, not an additional research
target.

### Gamma decomposition

Prove an exact pointwise identity away from `0`, `1`, and zeta zeros. The
preferred normal form is mathematically equivalent to

```text
logDeriv xi(s)
  = 1 / s + 1 / (s - 1)
    - (log pi) / 2
    + (1 / 2) * digamma(s / 2)
    + logDeriv zeta(s).
```

Use the repository's existing `GammaR`, `digamma`, and completed-zeta APIs.
The exact syntactic normal form may follow existing lemmas if that avoids
unnecessary algebraic conversion.

## Verification

Add contract modules to the default Lake target that check the exact public
signatures. Add an axiom-audit module using `#print axioms` for the three final
theorem surfaces. Verification is:

```bash
lake -Kjobs=1 build PrimeNumberTheorem.RiemannVonMangoldt
lake -Kjobs=1 build Test.RiemannVonMangoldtContract
lake -Kjobs=1 build Test.RiemannVonMangoldtAxiomAudit
./scripts/verify-baseline.sh
```

The source scan must show no new `sorry`, `admit`, or `axiom`. The final axiom
surface may contain only the repository's existing foundational allowlist
(`propext`, `Classical.choice`, and `Quot.sound`).

## Feasibility Decision

Continue toward the full Riemann-von Mangoldt asymptotic only if all three
deliverables compile and pass the axiom audit.

Stop the unified-paper route and retain separate Hardy and PNT publication
paths if the project-specific completed-zeta regularization cannot produce the
rectangle count identity without adding an unproved interface or a new axiom.

## Explicit Non-goals

- the full Riemann-von Mangoldt asymptotic;
- an `O(log T)` bound for zeta boundary argument variation;
- extension from good heights to every real height;
- Hardy-Littlewood, Selberg, or positive-proportion zero results;
- a general-purpose argument principle for all meromorphic functions;
- new zero-free regions, zero-density estimates, or RH implications;
- paper restructuring or new publication claims.
