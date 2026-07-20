# Li Criterion Chain

This document scopes the Li-criterion route to RH (roadmap Route A, combined
with the Route C xi-function foundation).  Four stages are now implemented
in Lean: a canonical xi-function API, the Li-criterion statement layer, two
unconditional inputs — the reality of the Li coefficients and the
convergence of the paired zero series — and two further proved slices:
**term-wise nonnegativity of the paired zero terms under RH**, and the
**convergence of the paired Mittag-Leffler series** in the `ξ'/ξ`
partial-fraction expansion.  The Li–RH equivalence itself and the
zero-sum representation of the Li coefficients remain `def ... : Prop`
targets; for the latter, the right-hand side is now a *genuinely convergent*
series (`summable_li_zero_sum_terms`), and for the former, RH is now proved
to imply `0 ≤ (liCoefficient n).re` *modulo* that same representation
(`liCoefficient_re_nonneg_of_representation_of_rh`).  The missing analytic
ingredient for the representation is exactly the `ξ'/ξ` partial-fraction
expansion (Hadamard-factorization level); its right-hand paired series is
proved convergent (`summable_xiPairedMittagLefflerTerm`).

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
| `deriv_schwarzSymmetricOn`, `schwarzSymmetric_iteratedDeriv`, `iteratedDeriv_schwarz_real` | General Schwarz-symmetry propagation: on open conjugate-stable sets, symmetry passes to all iterated derivatives; iterated derivatives at real points are real (`SchwarzSymmetric.lean`). |
| `liCoefficient_im`, `liCoefficient_is_real` | **Unconditional reality**: `(liCoefficient n).im = 0` for every `n`, via `Complex.log` branch control on `xiPosReSet = ξ ⁻¹' {w | 0 < w.re}` (`LiReality.lean`). |
| `liCriterionHolds_iff_re_pos` | `LiCriterionHolds` reduces to the pure real inequality `0 < (liCoefficient n).re` for all `n ≥ 1` — the imaginary half is discharged unconditionally. |
| `norm_one_sub_one_sub_pow_sub_le` | Binomial remainder bound `‖1 - (1-w)ⁿ - n·w‖ ≤ 4·(3/2)ⁿ·‖w‖²` for `‖w‖ ≤ 1/2` (`LiZeroSumConvergence.lean`, Part A). |
| `summable_norm_inv_sq_upperZeros` | `Σ ‖ρ‖⁻²` over upper half-plane nontrivial zeros converges: low/high split at `‖ρ‖ = 2`, fixed finite low part, dyadic-shell counting from `N(T) ≤ C·T·(1 + log(T+6))` (Part B). |
| `norm_liPairedTerm_le` | Paired-term bound `‖liPairedTerm n ρ‖ ≤ (2n + 8·(3/2)ⁿ)·‖ρ‖⁻²` for `‖ρ‖ ≥ 2`: pairing collapses the non-summable `n/ρ` terms to `2n·ρ.re/‖ρ‖²` with `|ρ.re| ≤ 1` (Part C). |
| `summable_liPairedTerm`, `summable_li_zero_sum_terms` | **Unconditional convergence** of the paired zero series in `li_zero_sum_representation_target` for every `n`. |
| `liPairedTerm_eq_ofReal_two_mul_re`, `liPairedTerm_im`, `liPairedTerm_re` | Each paired term is real (unconditionally), with `(liPairedTerm n ρ).re = 2·(1 - Re((1-1/ρ)ⁿ))` (`LiPositivity.lean`). |
| `norm_one_sub_inv_of_re_eq_half` | On the critical line, `‖1 - 1/ρ‖ = 1` (since `1 - 1/ρ = (ρ-1)/ρ` and `‖ρ-1‖ = ‖ρ‖` when `ρ.re = 1/2`). |
| `liPairedTerm_re_nonneg_of_rh` | **Term-wise nonnegativity under RH**: `(liPairedTerm n ρ).re ≥ 0` — the formal `1 - cos(nθ) ≥ 0`. |
| `tsum_liPairedTerm_re_nonneg_of_rh` | Under RH the (convergent) paired zero series has nonnegative real part. |
| `liCoefficient_re_nonneg_of_representation_of_rh` | **Conditional reduction**: if `li_zero_sum_representation_target` holds, then RH implies `0 ≤ (liCoefficient n).re` for all `n ≥ 1`. |
| `xiPairedMittagLefflerTerm_eq` | Algebraic decomposition of the paired `ξ'/ξ` Mittag-Leffler term: `2(s - ↑ρ.re)/((s-ρ)(s-conjρ)) + ↑(2·ρ.re/normSq ρ)` (`XiPartialFraction.lean`). |
| `norm_xiPairedMittagLefflerTerm_le` | Bound `‖·‖ ≤ (8·(‖s‖+1) + 2)·‖ρ‖⁻²` for `‖ρ‖ ≥ 2`, `2‖s‖ ≤ ‖ρ‖`, `|ρ.re| ≤ 1` (via `‖s-ρ‖ ≥ ‖ρ‖/2`). |
| `summable_xiPairedMittagLefflerTerm` | **Unconditional convergence**, for each fixed `s`, of the paired Mittag-Leffler series over upper half-plane zeros — the convergence half of the `ξ'/ξ` partial-fraction expansion. |

## Current Target Assessment

The chain now carries five `def ... : Prop` targets (all in
`RiemannExplorer/LiCriterion.lean`):

| Target | Shape | Why it is still open |
| --- | --- | --- |
| `LiCriterionHolds` | `∀ n ≥ 1, (liCoefficient n).im = 0 ∧ 0 < (liCoefficient n).re` | Equivalent to RH; cannot be proved unconditionally.  The `.im = 0` half is now proved unconditionally (`liCoefficient_im`); by `liCriterionHolds_iff_re_pos` only real positivity remains. |
| `li_criterion_implies_rh_target` | `LiCriterionHolds → RiemannHypothesis.Statement` | Needs the zero-sum representation and zero-exclusion arguments. |
| `rh_implies_li_criterion_target` | `RiemannHypothesis.Statement → LiCriterionHolds` | Reduced by `liCoefficient_re_nonneg_of_representation_of_rh` to exactly two gaps: (i) the zero-sum representation `li_zero_sum_representation_target` (whose series is proved convergent, `summable_li_zero_sum_terms`), and (ii) strict positivity `0 <` — the paired series is a sum of `2·(1 - cos(nθ_ρ))` terms, so vanishing forces `(1-1/ρ)ⁿ = 1` at every zero, which has at most `n-1` solutions, contradicting Hardy's infinitude of critical-line zeros. |
| `li_criterion_iff_rh_target` | `LiCriterionHolds ↔ RiemannHypothesis.Statement` | The Li 1997 / Bombieri–Lagarias 1999 equivalence; follows once both directions are proved (`li_criterion_iff_rh_target_of_directions`). |
| `li_zero_sum_representation_target` | `∀ n ≥ 1, liCoefficient n = ∑' ρ, paired conjugate zero terms` | The right-hand series is now proved convergent for every `n` (`summable_li_zero_sum_terms`), and the paired series on the `ξ'/ξ` side is proved convergent (`summable_xiPairedMittagLefflerTerm`).  The remaining gaps are exactly: (i) the removable-singularity argument that `ξ'/ξ - B - Σ_ρ [1/(s-ρ) + 1/ρ]` is entire; (ii) the growth order `≤ 1` of `ξ` (Gamma-factor bounds + Phragmén–Lindelöf), forcing that entire difference to be constant; (iii) identification of the quotient constant `B = ξ'(0)/ξ(0)`; (iv) pairing convention (`ρ ↔ conj ρ` here vs classical `ρ ↔ 1 - ρ`); (v) counted over distinct zeros without analytic multiplicity (convention must be aligned before promotion). |

## Dependencies For The Next Stage

- Hadamard factorization for entire functions of finite order, or at least
  the `ξ'/ξ` partial-fraction expansion over the zeros (Mathlib-level
  blocker, shared with Route C).  The convergence half of the expansion is
  now proved (`summable_xiPairedMittagLefflerTerm`); what remains is the
  identity itself, via (i) the removable-singularity step, (ii) the growth
  order `≤ 1` of `ξ` (Gamma-factor bounds + Phragmén–Lindelöf; cf. the
  existing `ZeroFreeRegion.PhragmenLindelofZeta` tooling), and (iii) the
  quotient-constant identification.
- Strict positivity of the paired Li series: `tsum = 0` would force
  `(1-1/ρ)ⁿ = 1` at every upper half-plane zero (at most `n-1` roots of
  unity solutions), contradicting Hardy's theorem that infinitely many
  zeros lie on the critical line.
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
lake build RiemannExplorer.XiFunction RiemannExplorer.LiCriterion \
  RiemannExplorer.SchwarzSymmetric RiemannExplorer.LiReality \
  RiemannExplorer.LiZeroSumConvergence RiemannExplorer.LiPositivity \
  RiemannExplorer.XiPartialFraction
lake build Test.XiFunctionAxiomAudit
```

All must succeed; the audit output must list only `propext`,
`Classical.choice`, and `Quot.sound` for every declaration.
