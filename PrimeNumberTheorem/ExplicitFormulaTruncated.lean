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

## Why a `def ... : Prop` target

The current declaration is intentionally a **target**, not a theorem:
a `def ... : Prop` with a real mathematical body.  Its purpose is to
(a) lock the pointwise-in-`x`, uniform-in-height quantifier order, (b) let
downstream code (`import PrimeNumberTheorem.ExplicitFormulaTruncated`) use the
name as a typed predicate, and (c) avoid exporting an unproved theorem.

The actual explicit-formula proof is **deliberately deferred** to a
later phase: building it from scratch in Lean 4.29.1 / Mathlib 4.29.1
requires Perron's formula on a vertical contour + the rectangle
contour integral ↔ residue-sum gluing
(`MathlibAux.RectangleResidue.rectangleIntegral_meromorphic_eq_residue_sum`
in the upstream interface), both of which are far beyond the
15-minute window of this interface task.  See
`docs/explicit-formula-chain.md` §"Truncated explicit formula
main target" for the intended future body.

## Inventory

### 1 core def (Prop target)
- `ExplicitFormulaTruncatedTarget` — the main asymptotic-identity
  predicate.

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

**This is NOT a `theorem`** — it is a `def` returning `Prop`.  The
repository tracks it as an unproved target whose eventual proof should
combine Perron's formula with the rectangle residue interface. -/
def ExplicitFormulaTruncatedTarget : Prop :=
  ∀ x : ℝ, 2 ≤ x → ∃ C > (0 : ℝ), ∀ T : ℝ, 2 ≤ T →
    ‖((ExplicitFormulaAux.chebyshevPsi0 x : ℂ) -
      ((x : ℂ)
        - PrimeNumberTheorem.finiteNontrivialZeroSumWithMultiplicity x T
        - (Real.log (2 * Real.pi) : ℂ)
        - (1 / 2 : ℂ) * (Real.log (1 - x ^ (-2 : ℝ)) : ℂ)))‖
      ≤ C * x / T * (Real.log (x * T)) ^ 2

/-! ## Assumption-repackaging lemma -/

/-- Repackage an assumed truncated explicit formula target.

This lemma is intentionally conditional: the file records the target shape but
does not prove Perron's formula or the rectangle residue chain. -/
lemma explicitFormulaTruncated_of (h : ExplicitFormulaTruncatedTarget) :
    ExplicitFormulaTruncatedTarget :=
  h

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

/-- One-step conditional bridge from a future truncated explicit formula route
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

/-- One-step conditional bridge from a future truncated explicit formula route
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
