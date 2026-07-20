# Li Criterion Chain

This document scopes the Li-criterion route to RH (roadmap Route A, combined
with the Route C xi-function foundation).  The first stage is now implemented
in Lean: a canonical xi-function API and the Li-criterion statement layer.
The Li–RH equivalence itself and the zero-sum representation of the Li
coefficients remain `def ... : Prop` targets.

Design documents:

- `docs/research/xi-definition-audit.md`
  audit of the local completed-zeta definitions against Mathlib's
  `completedRiemannZeta` / `completedRiemannZeta₀`;
- `docs/research/li-criterion-note.md`
  the staged Li-criterion design (predicate, xi-derivative definition,
  generating-function route) and its dependency list.

## Current Lean Anchors (proved in this stage)

All declarations live in the `RiemannExplorer` namespace.  Axiom audits are in
`Test/XiFunctionAxiomAudit.lean`; every proof below depends only on
`propext`, `Classical.choice`, and `Quot.sound`.

| Lean name | Current role in this chain |
| --- | --- |
| `xiFunction` | Canonical entire xi function, defined as `(1/2)·s·(s-1)·completedRiemannZeta₀ s - (1/2)·(s-1) + (1/2)·s`; the affine correction is exactly the pole-cancellation of `completedRiemannZeta_eq`. |
| `xiFunction_eq_completedZeta` | Definitional bridge to the legacy `RiemannHypothesis.completedZeta`; new work uses `xiFunction`. |
| `xiFunction_one_sub` | Functional equation `ξ(s) = ξ(1 - s)`, proved from `completedRiemannZeta₀_one_sub`. |
| `xiFunction_zero`, `xiFunction_one` | Classical values `ξ(0) = ξ(1) = 1/2`. |
| `differentiable_xiFunction` | `ξ` is entire (differentiable on all of `ℂ`), from `differentiable_completedZeta₀`. |
| `xiFunction_eq_half_mul_completed` | Bridge to Mathlib's meromorphic `completedRiemannZeta` for `s ≠ 0, 1`. |
| `xiFunction_eq_classical`, `xiFunction_eq_classical_of_one_lt_re` | Classical form `ξ(s) = (1/2)·s·(s-1)·Gammaℝ(s)·ζ(s)`, in particular for `1 < s.re`. |
| `xiFunction_eq_zero_iff`, `xiFunction_eq_zero_iff_isNontrivialZero` | In the critical strip, `ξ(s) = 0 ↔ ζ(s) = 0 ↔ IsNontrivialZero s`. |
| `riemannHypothesis_iff_xi_zeros_on_critical_line` | RH (as `RiemannHypothesis.Statement`) is equivalent to: every strip zero of `ξ` has real part `1/2`. |
| `xiFunction_conj` | Schwarz symmetry `ξ(conj s) = conj (ξ s)`, via `HardyTheorem.completedRiemannZeta₀_conj_eq`. |
| `xiFunction_critical_line_real` | `ξ(1/2 + it)` is real-valued for real `t`. |
| `liCoefficient` | Li coefficients in xi-derivative form: `(1/(n-1)!) · dⁿ/dsⁿ [s^(n-1)·log ξ(s)]` at `s = 1`. |
| `liCoefficient_zero`, `liCoefficient_zero_real`, `liCoefficient_zero_im` | Sanity checks: `λ₀ = log ξ(1) = log(1/2) ∈ ℝ`. |
| `li_criterion_iff_rh_target_of_directions` | Proved reduction: the two one-direction targets imply the iff target. |

## Current Target Assessment

The chain now carries five `def ... : Prop` targets (all in
`RiemannExplorer/LiCriterion.lean`):

| Target | Shape | Why it is still open |
| --- | --- | --- |
| `LiCriterionHolds` | `∀ n ≥ 1, (liCoefficient n).im = 0 ∧ 0 < (liCoefficient n).re` | Equivalent to RH; cannot be proved unconditionally. |
| `li_criterion_implies_rh_target` | `LiCriterionHolds → RiemannHypothesis.Statement` | Needs the zero-sum representation and zero-exclusion arguments. |
| `rh_implies_li_criterion_target` | `RiemannHypothesis.Statement → LiCriterionHolds` | Under RH each paired zero term has positive real part; needs the zero-sum representation plus convergence control. |
| `li_criterion_iff_rh_target` | `LiCriterionHolds ↔ RiemannHypothesis.Statement` | The Li 1997 / Bombieri–Lagarias 1999 equivalence; follows once both directions are proved (`li_criterion_iff_rh_target_of_directions`). |
| `li_zero_sum_representation_target` | `∀ n ≥ 1, liCoefficient n = ∑' ρ, paired conjugate zero terms` | Needs Hadamard-product / log-derivative machinery; counted over distinct zeros without analytic multiplicity (convention must be aligned before promotion). |

## Dependencies For The Next Stage

- Hadamard factorization for entire functions of finite order (Mathlib-level
  blocker, shared with Route C).
- Analytic-log branch control for `log ξ` in a nonvanishing neighborhood of
  `s = 1` (`Complex.log` is used in the current definition; the analytic
  properties need a local analytic-log abstraction).
- Zero-sum machinery over nontrivial zeros, with an explicit convention for
  distinct zeros versus analytic multiplicity
  (cf. `PrimeNumberTheorem.NontrivialZeroMultiplicity`).
- The stage-3 generating-function identity
  `log ξ(1/(1-z)) = const + Σ (λ_n / n) z^n`, which may offer a
  formal-power-series route to the equivalence.

## Numerical Evidence Boundary

`experiments/rh/li_coefficients.py` computes empirical truncated Li
coefficients from a zero fixture.  Those values are numerical evidence only:
they do not imply RH and must not be cited as proof.

## Verification

```bash
lake build RiemannExplorer.XiFunction RiemannExplorer.LiCriterion
lake build Test.XiFunctionAxiomAudit
```

All three must succeed; the audit output must list only `propext`,
`Classical.choice`, and `Quot.sound` for every declaration.
