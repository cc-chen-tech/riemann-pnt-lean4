/-
Copyright (c) 2026 Riemann PNT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Truncated Explicit Formula — Main Target

## Purpose

This file declares the project-internal target statement for the
"truncated von Mangoldt explicit formula" main target.  The target
locks the signature of the asymptotic identity

```
  ψ₀(x) = x − ∑_{|Im ρ| ≤ T} m(ρ)x^ρ / ρ − log(2π) − (1/2) log(1 − 1/x²)
          + O_x(log²(xT) / T)
```

where `m(ρ)` is the analytic multiplicity of the zero and `ψ₀` is the
midpoint-convention Chebyshev-`ψ` (declared as
`PrimeNumberTheorem.ExplicitFormulaAux.chebyshevPsi0`), `ρ` ranges
over the nontrivial zeros of `ζ` with `|Im ρ| ≤ T`, and the trailing
`O_x(log²(xT) / T)` is the pointwise-in-`x` error term.

## Target predicate and proof

The `def ... : Prop` declaration locks the pointwise-in-`x`, uniform-in-height
quantifier order.  The theorem `explicitFormulaTruncatedTarget_proved` below
now proves this predicate unconditionally.  Its large-height input is the
completed quantitative contour calculation; the bounded interval `2 ≤ T < 8`
is absorbed by a finite zero-sum bound.

## Inventory

### 1 core def and its theorem
- `ExplicitFormulaTruncatedTarget` — the main asymptotic-identity
  predicate.
- `explicitFormulaTruncatedTarget_proved` — its unconditional proof.

### 1 simple lemma (identity check)
- `explicitFormulaTruncated_of` — repackages an assumption of the target,
  making clear that this file does not prove the target unconditionally.

## Dependencies (already proved / already declared)

- `PrimeNumberTheorem.chebyshevPsi0` (parent namespace) and
  `PrimeNumberTheorem.ExplicitFormulaAux.chebyshevPsi0`
  (re-exposed in the prior `ExplicitFormulaAux` module).
- `PrimeNumberTheorem.ExplicitFormulaAux.jumpVonMangoldt`.
- `PrimeNumberTheorem.finiteNontrivialZeroSumWithMultiplicity`.
- `PrimeNumberTheorem.ExplicitFormulaAux.chebyshevPsi0_eq_chebyshevPsi_off_primePowers`.
- `PrimeNumberTheorem.finite_nontrivial_zeros_bounded_height`.
- `MathlibAux.RectangleResidue.rectangleIntegral_meromorphic_eq_residue_sum`
  (upstream interface — used by the future residue / contour glue;
  not imported here, only cross-referenced in this doc-comment).
-/

import Mathlib
import PrimeNumberTheorem
import PrimeNumberTheorem.ExplicitFormulaAux
import PrimeNumberTheorem.ExplicitFormulaAllHeights
import PrimeNumberTheorem.ZetaDerivativeZero

open Complex
open scoped ArithmeticFunction BigOperators

-- This file declares a `def ... : Prop` target rather than an exported theorem.
-- For each fixed `x`, one constant must control every admissible height `T`.

namespace PrimeNumberTheorem
namespace ExplicitFormulaTruncated

/-! ## Truncated explicit formula main target (interface placeholder) -/

/-- Truncated von Mangoldt explicit formula — main asymptotic-identity
predicate.

This is the central "explicit formula" target of the B chain.  In
asymptotic form it states

```
  ψ₀(x) = x − ∑_{|Im ρ| ≤ T} m(ρ)x^ρ / ρ
          − log(2π) − (1/2) log(1 − 1/x²)
          + O_x(log²(xT) / T)
```

where:

* `ψ₀` is the midpoint-convention Chebyshev-`ψ`
  (`PrimeNumberTheorem.ExplicitFormulaAux.chebyshevPsi0`,
  re-exposed from the parent `PrimeNumberTheorem.chebyshevPsi0`);
* the sum ranges over nontrivial zeros of `ζ` with `|Im ρ| ≤ T` and
  weights each distinct zero by `analyticOrderNatAt riemannZeta ρ`;
* the trailing pointwise `O_x(log²(xT) / T)` is the contour-shift error
  estimate obtained from
  `MathlibAux.RectangleResidue.rectangleIntegral_meromorphic_eq_residue_sum`
  (the upstream interface) by balancing the main term against the
  residue sum on a rectangle of half-height `T`.

The quantifier order is essential: for each fixed `x`, one constant `C` controls
all `T ≥ 2`.  A constant uniform in both `x` and `T` with only an
`x * log²(x) / T` error would contradict the jump discontinuities of `ψ₀`,
while putting `∃ C` after fixed `T,x` would make the estimate vacuous.

The predicate is kept as a named interface; it is discharged below by
`explicitFormulaTruncatedTarget_proved`. -/
def ExplicitFormulaTruncatedTarget : Prop :=
  ∀ x : ℝ, 2 ≤ x → ∃ C > (0 : ℝ), ∀ T : ℝ, 2 ≤ T →
    ‖((ExplicitFormulaAux.chebyshevPsi0 x : ℂ) -
      ((x : ℂ)
        - PrimeNumberTheorem.finiteNontrivialZeroSumWithMultiplicity x T
        - (Real.log (2 * Real.pi) : ℂ)
        - (1 / 2 : ℂ) * (Real.log (1 - x ^ (-2 : ℝ)) : ℂ)))‖
      ≤ C * x / T * (Real.log (x * T)) ^ 2

/-! ## Compatibility repackaging lemma -/

/-- Repackage a supplied truncated explicit formula target. -/
lemma explicitFormulaTruncated_of (h : ExplicitFormulaTruncatedTarget) :
    ExplicitFormulaTruncatedTarget :=
  h

/-! ## Proof of the target -/

/-- The multiplicity-aware approximation has the classical `log(2π)`
normalization. -/
lemma explicitFormulaApproxWithMultiplicity_eq_log_two_pi (x T : ℝ) :
    explicitFormulaApproxWithMultiplicity x T =
      (x : ℂ) - finiteNontrivialZeroSumWithMultiplicity x T -
        (Real.log (2 * Real.pi) : ℂ) -
        (1 / 2 : ℂ) * (Real.log (1 - x ^ (-2 : ℝ)) : ℂ) := by
  simp only [explicitFormulaApproxWithMultiplicity,
    deriv_riemannZeta_zero_div_riemannZeta_zero]

/-- On the compact initial height interval, the explicit-formula
approximation is bounded by a fixed finite zero sum. -/
lemma exists_norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_of_le_eight
    (x : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, T ≤ 8 →
      ‖explicitFormulaApproxWithMultiplicity x T - (chebyshevPsi0 x : ℂ)‖ ≤ K := by
  classical
  let Z : ℝ := ∑ ρ ∈ nontrivialZerosFinset 8,
    ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖
  let K : ℝ := Z +
    ‖explicitFormulaApproxWithMultiplicity x 8 - (chebyshevPsi0 x : ℂ)‖
  have hZ : 0 ≤ Z := by
    dsimp [Z]
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro T hT8
  have hnew :=
    norm_explicitFormulaApproxWithMultiplicity_sub_le_new_zeros_sum_norm
      (x := x) hT8
  have hsum :
      (∑ ρ ∈ (nontrivialZerosFinset 8 \ nontrivialZerosFinset T),
          ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖) ≤ Z := by
    dsimp [Z]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun ρ _hρ8 _hρdiff => norm_nonneg _)
  calc
    ‖explicitFormulaApproxWithMultiplicity x T - (chebyshevPsi0 x : ℂ)‖ =
        ‖(explicitFormulaApproxWithMultiplicity x T -
            explicitFormulaApproxWithMultiplicity x 8) +
          (explicitFormulaApproxWithMultiplicity x 8 -
            (chebyshevPsi0 x : ℂ))‖ := by congr 1 <;> ring
    _ ≤ ‖explicitFormulaApproxWithMultiplicity x T -
          explicitFormulaApproxWithMultiplicity x 8‖ +
        ‖explicitFormulaApproxWithMultiplicity x 8 -
          (chebyshevPsi0 x : ℂ)‖ := norm_add_le _ _
    _ ≤ Z + ‖explicitFormulaApproxWithMultiplicity x 8 -
          (chebyshevPsi0 x : ℂ)‖ := add_le_add (hnew.trans hsum) le_rfl
    _ = K := rfl

/-- The project target for the pointwise truncated explicit formula.  The
large-height estimate is the quantitative all-height contour theorem; the
compact interval `2 ≤ T < 8` is absorbed into the fixed constant. -/
theorem explicitFormulaTruncatedTarget_proved : ExplicitFormulaTruncatedTarget := by
  classical
  intro x hx
  have hx1 : 1 < x := by linarith
  rcases
      _root_.PrimeNumberTheorem.ExplicitFormulaResidues.exists_norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_log_sq_div
        hx1 with
    ⟨C₀, hC₀, hlarge⟩
  rcases
      exists_norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_of_le_eight x with
    ⟨K, hK, hsmall⟩
  let ℓ : ℝ := Real.log 4
  let C : ℝ := 1 + 4 * C₀ + 4 * K / ℓ ^ 2
  have hℓ : 0 < ℓ := by
    dsimp [ℓ]
    exact Real.log_pos (by norm_num)
  have hC : 0 < C := by
    dsimp [C]
    have : 0 ≤ 4 * K / ℓ ^ 2 := by positivity
    positivity
  refine ⟨C, hC, ?_⟩
  intro T hT
  have hTpos : 0 < T := by linarith
  rw [show
      (x : ℂ) - finiteNontrivialZeroSumWithMultiplicity x T -
          (Real.log (2 * Real.pi) : ℂ) -
          (1 / 2 : ℂ) * (Real.log (1 - x ^ (-2 : ℝ)) : ℂ) =
        explicitFormulaApproxWithMultiplicity x T by
    exact (explicitFormulaApproxWithMultiplicity_eq_log_two_pi x T).symm]
  rw [norm_sub_rev]
  by_cases hT8 : 8 ≤ T
  · have hxt : T + 8 ≤ x * T := by nlinarith
    have hxtpos : 0 < x * T := mul_pos (by linarith) hTpos
    have hlogle : Real.log (T + 8) ≤ Real.log (x * T) :=
      Real.log_le_log (by linarith) hxt
    have honele : 1 ≤ Real.log (x * T) := by
      apply (Real.le_log_iff_exp_le hxtpos).2
      exact Real.exp_one_lt_three.le.trans (by nlinarith)
    have hL : 0 ≤ 1 + Real.log (T + 8) := by
      have : 0 ≤ Real.log (T + 8) := Real.log_nonneg (by linarith)
      linarith
    have hlog0 : 0 ≤ Real.log (x * T) := by linarith
    have hLsq : (1 + Real.log (T + 8)) ^ 2 ≤
        4 * (Real.log (x * T)) ^ 2 := by
      have hLle : 1 + Real.log (T + 8) ≤ 2 * Real.log (x * T) := by linarith
      nlinarith
    have hCge : 4 * C₀ ≤ C := by
      dsimp [C]
      have : 0 ≤ 4 * K / ℓ ^ 2 := by positivity
      linarith
    have hCx : 4 * C₀ ≤ C * x := by
      apply hCge.trans
      have hxone : 1 ≤ x := by linarith
      simpa using mul_le_mul_of_nonneg_left hxone hC.le
    calc
      ‖explicitFormulaApproxWithMultiplicity x T - (chebyshevPsi0 x : ℂ)‖ ≤
          C₀ * (1 + Real.log (T + 8)) ^ 2 / T := hlarge T hT8
      _ ≤ (4 * C₀) * (Real.log (x * T)) ^ 2 / T := by
        apply div_le_div_of_nonneg_right _ hTpos.le
        have := mul_le_mul_of_nonneg_left hLsq hC₀
        nlinarith
      _ ≤ (C * x) * (Real.log (x * T)) ^ 2 / T := by
        apply div_le_div_of_nonneg_right _ hTpos.le
        exact mul_le_mul_of_nonneg_right hCx (sq_nonneg _)
      _ = C * x / T * (Real.log (x * T)) ^ 2 := by ring
  · have hT8' : T ≤ 8 := le_of_not_ge hT8
    have hbound := hsmall T hT8'
    have hxt4 : 4 ≤ x * T := by nlinarith
    have hxtpos : 0 < x * T := mul_pos (by linarith) hTpos
    have hlog4le : ℓ ≤ Real.log (x * T) := by
      dsimp [ℓ]
      exact Real.log_le_log (by norm_num) hxt4
    have hlog0 : 0 ≤ Real.log (x * T) := Real.log_nonneg (by linarith)
    have hlogsq : ℓ ^ 2 ≤ (Real.log (x * T)) ^ 2 := by nlinarith
    have hratio : (1 / 4 : ℝ) ≤ x / T := by
      apply (le_div_iff₀ hTpos).2
      nlinarith
    have hClow : 4 * K / ℓ ^ 2 ≤ C := by
      dsimp [C]
      nlinarith
    calc
      ‖explicitFormulaApproxWithMultiplicity x T - (chebyshevPsi0 x : ℂ)‖ ≤ K :=
        hbound
      _ = (4 * K / ℓ ^ 2) * (1 / 4) * ℓ ^ 2 := by
        field_simp [ne_of_gt hℓ]
      _ ≤ C * (x / T) * (Real.log (x * T)) ^ 2 := by
        gcongr
      _ = C * x / T * (Real.log (x * T)) ^ 2 := by ring

/-! ## Converse route toward power-scale PNT error barriers -/

/-- Route interface from the truncated explicit formula target to the
power-scale converse used by the `Re(s)=1/3` bridge.

This keeps two dependencies explicit:
1. the future proof of a pointwise-in-`x`, uniform-in-height truncated
   explicit-formula bound;
2. the future oscillation/converse argument extracting a zero-free half-plane
   from a `ψ(x)-x = O(x^θ)` bound with `θ < β`.

It is intentionally a `Prop` interface, not a theorem asserting either
dependency unconditionally. -/
def ExplicitFormulaTruncatedConverseRoute (β : ℝ) : Prop :=
  ExplicitFormulaTruncatedTarget →
    PrimeNumberTheorem.ExplicitFormulaConversePowerTarget β

/-- Repackage a truncated-explicit-formula converse route as the power
converse target used by the main PNT bridge. -/
lemma explicitFormulaConversePower_of_truncated_route
    {β : ℝ}
    (hroute : ExplicitFormulaTruncatedConverseRoute β)
    (hexplicit : ExplicitFormulaTruncatedTarget) :
    PrimeNumberTheorem.ExplicitFormulaConversePowerTarget β :=
  hroute hexplicit

/-- Repackage a truncated-explicit-formula converse route as the right-half
zero-exclusion route interface used by the `ψ`-error bridges. -/
lemma psiPowerErrorBelowLineExcludesZerosRightOf_of_truncated_route
    {β : ℝ}
    (hroute : ExplicitFormulaTruncatedConverseRoute β)
    (hexplicit : ExplicitFormulaTruncatedTarget) :
    PrimeNumberTheorem.PsiPowerErrorBelowLineExcludesZerosRightOf β :=
  PrimeNumberTheorem.psiPowerErrorBelowLineExcludesZerosRightOf_of_explicit_formula_converse_power
    (explicitFormulaConversePower_of_truncated_route hroute hexplicit)

/-- One-step conditional bridge from a future truncated-formula converse route
and a `ψ` power saving below `2/3` to no zeros on `Re(s)=2/3`. -/
theorem no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route
    (hroute : ExplicitFormulaTruncatedConverseRoute (2 / 3))
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBelowLine (2 / 3)) :
    PrimeNumberTheorem.NoZerosOnVerticalLine (2 / 3) :=
  PrimeNumberTheorem.no_zeros_on_vertical_line_of_explicit_formula_converse_power
    (by norm_num) (by norm_num)
    (explicitFormulaConversePower_of_truncated_route hroute hexplicit)
    herror

/-- Concrete `ψ`-error version of the truncated explicit-formula bridge to
no zeros on `Re(s)=2/3`. -/
theorem no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route_below_two_thirds
    (hroute : ExplicitFormulaTruncatedConverseRoute (2 / 3))
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBelowTwoThirds) :
    PrimeNumberTheorem.NoZerosOnVerticalLine (2 / 3) :=
  no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route
    hroute hexplicit
    (PrimeNumberTheorem.psiPowerErrorBelowLine_two_thirds_of_below_two_thirds
      herror)

/-- One-step conditional bridge from a future truncated-formula converse route
and a `ψ` power saving below `2/3` to no zeros on `Re(s)=1/3`. -/
theorem no_zeros_on_one_third_of_truncated_explicit_formula_converse_route
    (hroute : ExplicitFormulaTruncatedConverseRoute (2 / 3))
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBelowLine (2 / 3)) :
    PrimeNumberTheorem.NoZerosOnVerticalLine (1 / 3) :=
  PrimeNumberTheorem.no_zeros_on_one_third_of_explicit_formula_converse_power
    (explicitFormulaConversePower_of_truncated_route hroute hexplicit)
    herror

/-- Concrete `ψ`-error version of the truncated explicit-formula bridge to
no zeros on `Re(s)=1/3`. -/
theorem no_zeros_on_one_third_of_truncated_explicit_formula_converse_route_below_two_thirds
    (hroute : ExplicitFormulaTruncatedConverseRoute (2 / 3))
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBelowTwoThirds) :
    PrimeNumberTheorem.NoZerosOnVerticalLine (1 / 3) :=
  no_zeros_on_one_third_of_truncated_explicit_formula_converse_route
    hroute hexplicit
    (PrimeNumberTheorem.psiPowerErrorBelowLine_two_thirds_of_below_two_thirds
      herror)

/-- Reflected-line version of the truncated explicit-formula bridge. -/
theorem no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hroute : ExplicitFormulaTruncatedConverseRoute β)
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBelowLine β) :
    PrimeNumberTheorem.NoZerosOnVerticalLine (1 - β) :=
  PrimeNumberTheorem.no_zeros_on_reflected_line_of_explicit_formula_converse_power
    hβ_pos hβ_lt_one
    (explicitFormulaConversePower_of_truncated_route hroute hexplicit)
    herror

/-- Concrete `θ < 2/3` reflected-line version of the truncated
explicit-formula bridge for any boundary `β >= 2/3`. -/
theorem no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_below_two_thirds
    {β : ℝ} (hβ_two_thirds : (2 / 3 : ℝ) ≤ β) (hβ_lt_one : β < 1)
    (hroute : ExplicitFormulaTruncatedConverseRoute β)
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBelowTwoThirds) :
    PrimeNumberTheorem.NoZerosOnVerticalLine (1 - β) :=
  no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 3) hβ_two_thirds)
    hβ_lt_one hroute hexplicit
    (PrimeNumberTheorem.psiPowerErrorBelowLine_of_below_two_thirds_of_two_thirds_le
      hβ_two_thirds herror)

/-- Power-saving version of the truncated explicit-formula route: an
`O(x^(β - δ))` input excludes zeros on `Re(s)=β`, assuming the truncated
explicit-formula converse route at `β`. -/
theorem no_zeros_on_vertical_line_of_truncated_explicit_formula_converse_route_saving
    {β delta : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hdelta_pos : 0 < delta) (hθ_nonneg : 0 ≤ β - delta)
    (hroute : ExplicitFormulaTruncatedConverseRoute β)
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBound (β - delta)) :
    PrimeNumberTheorem.NoZerosOnVerticalLine β :=
  PrimeNumberTheorem.no_zeros_on_vertical_line_of_explicit_formula_converse_power_bound_sub_delta
    hβ_pos hβ_lt_one hdelta_pos hθ_nonneg
    (explicitFormulaConversePower_of_truncated_route hroute hexplicit)
    herror

/-- Reflected-line power-saving version of the truncated explicit-formula
route. -/
theorem no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_saving
    {β delta : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hdelta_pos : 0 < delta) (hθ_nonneg : 0 ≤ β - delta)
    (hroute : ExplicitFormulaTruncatedConverseRoute β)
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBound (β - delta)) :
    PrimeNumberTheorem.NoZerosOnVerticalLine (1 - β) :=
  PrimeNumberTheorem.no_zeros_on_reflected_line_of_explicit_formula_converse_power_bound_sub_delta
    hβ_pos hβ_lt_one hdelta_pos hθ_nonneg
    (explicitFormulaConversePower_of_truncated_route hroute hexplicit)
    herror

/-- Existence-form power-saving version of the truncated explicit-formula
route. -/
theorem not_exists_nontrivial_zero_on_line_of_truncated_explicit_formula_converse_route_saving
    {β delta : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hdelta_pos : 0 < delta) (hθ_nonneg : 0 ≤ β - delta)
    (hroute : ExplicitFormulaTruncatedConverseRoute β)
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBound (β - delta)) :
    ¬ ∃ s : ℂ, RiemannHypothesis.IsNontrivialZero s ∧ s.re = β :=
  PrimeNumberTheorem.not_exists_nontrivial_zero_on_line_of_no_zeros_on_vertical_line
    (no_zeros_on_vertical_line_of_truncated_explicit_formula_converse_route_saving
      hβ_pos hβ_lt_one hdelta_pos hθ_nonneg hroute hexplicit herror)

/-- Reflected-line existence-form power-saving version of the truncated
explicit-formula route. -/
theorem not_exists_nontrivial_zero_on_reflected_line_of_truncated_explicit_formula_converse_route_saving
    {β delta : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hdelta_pos : 0 < delta) (hθ_nonneg : 0 ≤ β - delta)
    (hroute : ExplicitFormulaTruncatedConverseRoute β)
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBound (β - delta)) :
    ¬ ∃ s : ℂ, RiemannHypothesis.IsNontrivialZero s ∧ s.re = 1 - β :=
  PrimeNumberTheorem.not_exists_nontrivial_zero_on_line_of_no_zeros_on_vertical_line
    (no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_saving
      hβ_pos hβ_lt_one hdelta_pos hθ_nonneg hroute hexplicit herror)

/-- Concrete `O(x^(2/3 - δ))` version of the truncated explicit-formula bridge
to no zeros on `Re(s)=2/3`. -/
theorem no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route_saving
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ (2 / 3 : ℝ))
    (hroute : ExplicitFormulaTruncatedConverseRoute (2 / 3))
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBound ((2 / 3 : ℝ) - delta)) :
    PrimeNumberTheorem.NoZerosOnVerticalLine (2 / 3) :=
  no_zeros_on_vertical_line_of_truncated_explicit_formula_converse_route_saving
    (β := 2 / 3) (delta := delta)
    (by norm_num) (by norm_num) hdelta_pos (by linarith)
    hroute hexplicit herror

/-- Concrete `O(x^(2/3 - δ))` version of the truncated explicit-formula bridge
to no zeros on `Re(s)=1/3`. -/
theorem no_zeros_on_one_third_of_truncated_explicit_formula_converse_route_saving
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ (2 / 3 : ℝ))
    (hroute : ExplicitFormulaTruncatedConverseRoute (2 / 3))
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBound ((2 / 3 : ℝ) - delta)) :
    PrimeNumberTheorem.NoZerosOnVerticalLine (1 / 3) := by
  simpa [show (1 : ℝ) - 2 / 3 = 1 / 3 by norm_num] using
    no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_saving
      (β := 2 / 3) (delta := delta)
      (by norm_num) (by norm_num) hdelta_pos (by linarith)
      hroute hexplicit herror

/-- Concrete `O(x^(2/3 - δ))` existence-form bridge to no nontrivial zeros
on `Re(s)=2/3`. -/
theorem not_exists_nontrivial_zero_on_two_thirds_of_truncated_explicit_formula_converse_route_saving
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ (2 / 3 : ℝ))
    (hroute : ExplicitFormulaTruncatedConverseRoute (2 / 3))
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBound ((2 / 3 : ℝ) - delta)) :
    ¬ ∃ s : ℂ, RiemannHypothesis.IsNontrivialZero s ∧ s.re = 2 / 3 :=
  not_exists_nontrivial_zero_on_line_of_truncated_explicit_formula_converse_route_saving
    (β := 2 / 3) (delta := delta)
    (by norm_num) (by norm_num) hdelta_pos (by linarith)
    hroute hexplicit herror

/-- Concrete `O(x^(2/3 - δ))` existence-form bridge to no nontrivial zeros
on `Re(s)=1/3`. -/
theorem not_exists_nontrivial_zero_on_one_third_of_truncated_explicit_formula_converse_route_saving
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ (2 / 3 : ℝ))
    (hroute : ExplicitFormulaTruncatedConverseRoute (2 / 3))
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBound ((2 / 3 : ℝ) - delta)) :
    ¬ ∃ s : ℂ, RiemannHypothesis.IsNontrivialZero s ∧ s.re = 1 / 3 := by
  simpa [show (1 : ℝ) - 2 / 3 = 1 / 3 by norm_num] using
    not_exists_nontrivial_zero_on_reflected_line_of_truncated_explicit_formula_converse_route_saving
      (β := 2 / 3) (delta := delta)
      (by norm_num) (by norm_num) hdelta_pos (by linarith)
      hroute hexplicit herror

/-- Monotone-error version of the truncated explicit-formula route: a `ψ`
power saving below a smaller boundary `β` feeds a truncated route at any larger
boundary `γ`. -/
theorem no_zeros_on_vertical_line_of_truncated_explicit_formula_converse_route_mono_error
    {β γ : ℝ} (hβγ : β ≤ γ) (hγ_pos : 0 < γ) (hγ_lt_one : γ < 1)
    (hroute : ExplicitFormulaTruncatedConverseRoute γ)
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBelowLine β) :
    PrimeNumberTheorem.NoZerosOnVerticalLine γ :=
  PrimeNumberTheorem.no_zeros_on_vertical_line_of_psi_power_error_bridge_mono_error
    hβγ hγ_pos hγ_lt_one
    (psiPowerErrorBelowLineExcludesZerosRightOf_of_truncated_route
      hroute hexplicit)
    herror

/-- Reflected-line monotone-error version of the truncated explicit-formula
route. -/
theorem no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_mono_error
    {β γ : ℝ} (hβγ : β ≤ γ) (hγ_pos : 0 < γ) (hγ_lt_one : γ < 1)
    (hroute : ExplicitFormulaTruncatedConverseRoute γ)
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBelowLine β) :
    PrimeNumberTheorem.NoZerosOnVerticalLine (1 - γ) :=
  PrimeNumberTheorem.no_zeros_on_reflected_line_of_psi_power_error_bridge_mono_error
    hβγ hγ_pos hγ_lt_one
    (psiPowerErrorBelowLineExcludesZerosRightOf_of_truncated_route
      hroute hexplicit)
    herror

/-- Existence-form monotone-error version of the truncated explicit-formula
route. -/
theorem not_exists_nontrivial_zero_on_line_of_truncated_explicit_formula_converse_route_mono_error
    {β γ : ℝ} (hβγ : β ≤ γ) (hγ_pos : 0 < γ) (hγ_lt_one : γ < 1)
    (hroute : ExplicitFormulaTruncatedConverseRoute γ)
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBelowLine β) :
    ¬ ∃ s : ℂ, RiemannHypothesis.IsNontrivialZero s ∧ s.re = γ :=
  PrimeNumberTheorem.not_exists_nontrivial_zero_on_line_of_no_zeros_on_vertical_line
    (no_zeros_on_vertical_line_of_truncated_explicit_formula_converse_route_mono_error
      hβγ hγ_pos hγ_lt_one hroute hexplicit herror)

/-- Reflected-line existence-form monotone-error version of the truncated
explicit-formula route. -/
theorem not_exists_nontrivial_zero_on_reflected_line_of_truncated_explicit_formula_converse_route_mono_error
    {β γ : ℝ} (hβγ : β ≤ γ) (hγ_pos : 0 < γ) (hγ_lt_one : γ < 1)
    (hroute : ExplicitFormulaTruncatedConverseRoute γ)
    (hexplicit : ExplicitFormulaTruncatedTarget)
    (herror : PrimeNumberTheorem.PsiPowerErrorBelowLine β) :
    ¬ ∃ s : ℂ, RiemannHypothesis.IsNontrivialZero s ∧ s.re = 1 - γ :=
  PrimeNumberTheorem.not_exists_nontrivial_zero_on_line_of_no_zeros_on_vertical_line
    (no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_mono_error
      hβγ hγ_pos hγ_lt_one hroute hexplicit herror)

end ExplicitFormulaTruncated
end PrimeNumberTheorem
