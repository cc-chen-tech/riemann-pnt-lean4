/-
Copyright (c) 2026 Riemann PNT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Truncated Explicit Formula — Main Target

## Purpose

This file declares the project-internal target statement for the
"truncated von Mangoldt explicit formula" main target.  The target
locks the signature of the asymptotic identity

```
  ψ₀(x) = x − ∑_{|ρ| ≤ T} x^ρ / ρ − log(2π) − (1/2) log(1 − 1/x²)
          + O(x / T · log²(x))
```

where `ψ₀` is the midpoint-convention Chebyshev-`ψ` (declared as
`PrimeNumberTheorem.ExplicitFormulaAux.chebyshevPsi0`), `ρ` ranges
over the nontrivial zeros of `ζ` with `|Im ρ| ≤ T`, and the trailing
`O(x / T · log²(x))` is the error term.

## Why a `def ... : Prop` target

The current declaration is intentionally a **target**, not a theorem:
a `def ... : Prop` with a real mathematical body.  Its purpose is to
(a) lock the argument list (`T`, `hT`, `x`, `hx`), (b) let downstream
code (`import PrimeNumberTheorem.ExplicitFormulaTruncated`) use the
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
- `PrimeNumberTheorem.ExplicitFormulaAux.zeroMultiplicity`.
- `PrimeNumberTheorem.ExplicitFormulaAux.finiteNontrivialZeroSum`.
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
-- The parameter list is the public contract the rest of the project imports.
-- Disable the unused-variable linter because the proof witnesses `hT` and `hx`
-- exist to lock that contract even when the Prop body only needs `T` and `x`.
set_option linter.unusedVariables false

namespace PrimeNumberTheorem
namespace ExplicitFormulaTruncated

/-! ## Truncated explicit formula main target (interface placeholder) -/

/-- Truncated von Mangoldt explicit formula — main asymptotic-identity
predicate.

This is the central "explicit formula" target of the B chain.  In
asymptotic form it states

```
  ψ₀(x) = x − ∑_{|Im ρ| ≤ T} x^ρ / ρ
          − log(2π) − (1/2) log(1 − 1/x²)
          + O(x / T · log²(x))
```

where:

* `ψ₀` is the midpoint-convention Chebyshev-`ψ`
  (`PrimeNumberTheorem.ExplicitFormulaAux.chebyshevPsi0`,
  re-exposed from the parent `PrimeNumberTheorem.chebyshevPsi0`);
* the sum ranges over nontrivial zeros of `ζ` with
  `|Im ρ| ≤ T`, i.e. the Finset
  `PrimeNumberTheorem.ExplicitFormulaAux.finiteNontrivialZeroSum T`
  (an alias for `PrimeNumberTheorem.nontrivialZerosFinset T`, the
  output of `PrimeNumberTheorem.finite_nontrivial_zeros_bounded_height`);
* the trailing `O(x / T · log²(x))` is the contour-shift error
  estimate obtained from
  `MathlibAux.RectangleResidue.rectangleIntegral_meromorphic_eq_residue_sum`
  (the upstream interface) by balancing the main term against the
  residue sum on a rectangle of half-height `T`.

**Parameters**:
- `T : ℝ` — truncation height bounding the imaginary parts of
  the zeros that contribute to the residue sum.
- `hT : 0 < T` — explicit witness that the truncation height is
  positive (so the rectangle is non-degenerate and the residue
  sum is well-defined).
- `x : ℝ` — the argument at which the asymptotic identity is
  evaluated.
- `hx : 0 < x` — explicit witness that `x` is positive
  (so `x^ρ` is well-defined and the log-terms are real).

**This is NOT a `theorem`** — it is a `def` returning `Prop`.  The
repository tracks it as an unproved target whose eventual proof should
combine Perron's formula with the rectangle residue interface. -/
def ExplicitFormulaTruncatedTarget (T : ℝ) (hT : 0 < T) (x : ℝ) (hx : 0 < x) : Prop :=
  ∃ C > (0 : ℝ),
    ‖((ExplicitFormulaAux.chebyshevPsi0 x : ℂ) -
      ((x : ℂ)
        - (∑ ρ ∈ ExplicitFormulaAux.finiteNontrivialZeroSum T,
            (x : ℂ) ^ ρ / ρ)
        - (Real.log (2 * Real.pi) : ℂ)
        - (1 / 2 : ℂ) * (Real.log (1 - x ^ (-2 : ℝ)) : ℂ)))‖
      ≤ C * x / T * (Real.log x) ^ 2

/-! ## Assumption-repackaging lemma -/

/-- Repackage an assumed truncated explicit formula target.

This lemma is intentionally conditional: the file records the target shape but
does not prove Perron's formula or the rectangle residue chain. -/
lemma explicitFormulaTruncated_of (T : ℝ) (hT : 0 < T) (x : ℝ) (hx : 0 < x)
    (h : ExplicitFormulaTruncatedTarget T hT x hx) :
    ExplicitFormulaTruncatedTarget T hT x hx :=
  h

/-! ## Converse route toward power-scale PNT error barriers -/

/-- Route interface from the truncated explicit formula target to the
power-scale converse used by the `Re(s)=1/3` bridge.

This keeps two dependencies explicit:
1. the future proof of the truncated explicit formula for all admissible
   heights and positive `x`;
2. the future oscillation/converse argument extracting a zero-free half-plane
   from a `ψ(x)-x = O(x^θ)` bound with `θ < β`.

It is intentionally a `Prop` interface, not a theorem asserting either
dependency unconditionally. -/
def ExplicitFormulaTruncatedConverseRoute (β : ℝ) : Prop :=
  (∀ T : ℝ, ∀ hT : 0 < T, ∀ x : ℝ, ∀ hx : 0 < x,
      ExplicitFormulaTruncatedTarget T hT x hx) →
    PrimeNumberTheorem.ExplicitFormulaConversePowerTarget β

/-- Repackage a truncated-explicit-formula converse route as the power
converse target used by the main PNT bridge. -/
lemma explicitFormulaConversePower_of_truncated_route
    {β : ℝ}
    (hroute : ExplicitFormulaTruncatedConverseRoute β)
    (hexplicit : ∀ T : ℝ, ∀ hT : 0 < T, ∀ x : ℝ, ∀ hx : 0 < x,
      ExplicitFormulaTruncatedTarget T hT x hx) :
    PrimeNumberTheorem.ExplicitFormulaConversePowerTarget β :=
  hroute hexplicit

/-- Repackage a truncated-explicit-formula converse route as the right-half
zero-exclusion route interface used by the `ψ`-error bridges. -/
lemma psiPowerErrorBelowLineExcludesZerosRightOf_of_truncated_route
    {β : ℝ}
    (hroute : ExplicitFormulaTruncatedConverseRoute β)
    (hexplicit : ∀ T : ℝ, ∀ hT : 0 < T, ∀ x : ℝ, ∀ hx : 0 < x,
      ExplicitFormulaTruncatedTarget T hT x hx) :
    PrimeNumberTheorem.PsiPowerErrorBelowLineExcludesZerosRightOf β :=
  PrimeNumberTheorem.psiPowerErrorBelowLineExcludesZerosRightOf_of_explicit_formula_converse_power
    (explicitFormulaConversePower_of_truncated_route hroute hexplicit)

/-- One-step conditional bridge from a future truncated explicit formula route
and a `ψ` power saving below `2/3` to no zeros on `Re(s)=2/3`. -/
theorem no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route
    (hroute : ExplicitFormulaTruncatedConverseRoute (2 / 3))
    (hexplicit : ∀ T : ℝ, ∀ hT : 0 < T, ∀ x : ℝ, ∀ hx : 0 < x,
      ExplicitFormulaTruncatedTarget T hT x hx)
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
    (hexplicit : ∀ T : ℝ, ∀ hT : 0 < T, ∀ x : ℝ, ∀ hx : 0 < x,
      ExplicitFormulaTruncatedTarget T hT x hx)
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
    (hexplicit : ∀ T : ℝ, ∀ hT : 0 < T, ∀ x : ℝ, ∀ hx : 0 < x,
      ExplicitFormulaTruncatedTarget T hT x hx)
    (herror : PrimeNumberTheorem.PsiPowerErrorBelowLine (2 / 3)) :
    PrimeNumberTheorem.NoZerosOnVerticalLine (1 / 3) :=
  PrimeNumberTheorem.no_zeros_on_one_third_of_explicit_formula_converse_power
    (explicitFormulaConversePower_of_truncated_route hroute hexplicit)
    herror

/-- Concrete `ψ`-error version of the truncated explicit-formula bridge to
no zeros on `Re(s)=1/3`. -/
theorem no_zeros_on_one_third_of_truncated_explicit_formula_converse_route_below_two_thirds
    (hroute : ExplicitFormulaTruncatedConverseRoute (2 / 3))
    (hexplicit : ∀ T : ℝ, ∀ hT : 0 < T, ∀ x : ℝ, ∀ hx : 0 < x,
      ExplicitFormulaTruncatedTarget T hT x hx)
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
    (hexplicit : ∀ T : ℝ, ∀ hT : 0 < T, ∀ x : ℝ, ∀ hx : 0 < x,
      ExplicitFormulaTruncatedTarget T hT x hx)
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
    (hexplicit : ∀ T : ℝ, ∀ hT : 0 < T, ∀ x : ℝ, ∀ hx : 0 < x,
      ExplicitFormulaTruncatedTarget T hT x hx)
    (herror : PrimeNumberTheorem.PsiPowerErrorBelowTwoThirds) :
    PrimeNumberTheorem.NoZerosOnVerticalLine (1 - β) :=
  no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 3) hβ_two_thirds)
    hβ_lt_one hroute hexplicit
    (PrimeNumberTheorem.psiPowerErrorBelowLine_of_below_two_thirds_of_two_thirds_le
      hβ_two_thirds herror)

end ExplicitFormulaTruncated
end PrimeNumberTheorem
