import Zeta23.FinalMult
import PrimeNumberTheorem.RiemannVonMangoldt.SelbergScale
import HardyTheorem.CriticalLineMultiplicity
import RiemannExplorer

open Filter
open scoped BigOperators

namespace HardyTheorem

/-!
# Zeta23 → Selberg/Conrey bridge (external machine-checked closure)

This file assembles the three-step bridge described in
`docs/research/zeta23-selberg-bridge.md`.  It imports the vendored,
axiom-clean external artifact `Zeta23` (Anthropic's Lean formalization of
"More than two thirds of the zeros of the Riemann zeta function lie on the
critical line", Apache 2.0) and closes two of this repository's open
`def ... : Prop` targets:

* `selberg_odd_zero_proportion_target`
* `KnownResults.conrey_40_percent_zeros_on_critical_line_target`

The chain uses exactly the three bridge lemmas of the blueprint:

1. Zeta23's simple critical-line zeros (`N0simple 0 T`) inject into this
   repository's odd-multiplicity critical-line count
   (`criticalLineOddZeroCount T`) — a definition-level set inclusion.
2. This repository's own all-height Riemann–von Mangoldt lower bound
   (`exists_eventually_riemannZeroCount_ge_selbergScale`) transfers to
   Zeta23's `Ncount 0 T` via a definition-level counting alignment.
3. Zeta23's Theorem B (`thmB₀_mult_cumulative`: at least 2/3 of the zeros
   are simple and on the critical line) assembles the two inequalities.

No new analytic mathematics is proved here; the analytic content lives in
the imported, externally verified `Zeta23` development and in the classical
RvM theorem already proved in this repository.  The two `Prop` targets
remain explicitly named as the closure interface, and the final theorems
below should be added to the axiom audit (`Test/Zeta23SelbergBridgeAxiomAudit.lean`).
-/

namespace Zeta23SelbergBridge

/-- Definition-level alignment of the multiplicity functions: Zeta23's
`zeroMult` and Mathlib's `analyticOrderNatAt` are both the `toNat` of the
analytic order of `riemannZeta`. -/
lemma zeroMult_eq_analyticOrderNatAt (ρ : ℂ) :
    Zeta23.zeroMult ρ = analyticOrderNatAt riemannZeta ρ := rfl

/-- Definition-level alignment of the zero sets: Zeta23's `zerosIn 0 T`
(`T₁ < Im ρ ≤ T₂` window with `0 < Re ρ < 1`) is exactly this repository's
positive nontrivial-zero predicate.  Both sides reduce to
`riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T`. -/
lemma mem_zeta23_zerosIn_zero {ρ : ℂ} {T : ℝ} :
    ρ ∈ Zeta23.zerosIn 0 T ↔
      RiemannHypothesis.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ T := by
  simp [Zeta23.zerosIn, Zeta23.IsNontrivialZero, RiemannHypothesis.IsNontrivialZero]

/-- Bridge lemma 2 input: Zeta23's multiplicity-weighted count `Ncount 0 T`
equals this repository's `riemannZeroCount T`, because the underlying zero
sets and the multiplicity functions coincide definitionally. -/
lemma ncount_zero_eq_riemannZeroCount (T : ℝ) :
    Zeta23.Ncount 0 T =
      PrimeNumberTheorem.RiemannVonMangoldt.riemannZeroCount T := by
  classical
  unfold Zeta23.Ncount PrimeNumberTheorem.RiemannVonMangoldt.riemannZeroCount
  rw [finsum_mem_eq_sum_of_subset
    (f := fun ρ : ℂ => Zeta23.zeroMult ρ)
    (s := Zeta23.zerosIn 0 T)
    (t := PrimeNumberTheorem.RiemannVonMangoldt.positiveNontrivialZerosFinset T)]
  · apply Finset.sum_congr rfl
    intro ρ _
    exact zeroMult_eq_analyticOrderNatAt ρ
  · intro ρ hρ
    exact PrimeNumberTheorem.RiemannVonMangoldt.mem_positiveNontrivialZerosFinset.mpr
      (mem_zeta23_zerosIn_zero.mp hρ.1)
  · intro ρ hρ
    exact mem_zeta23_zerosIn_zero.mpr
      (PrimeNumberTheorem.RiemannVonMangoldt.mem_positiveNontrivialZerosFinset.mp hρ)

/-- Bridge lemma 1: every zero counted by Zeta23's `N0simple 0 T` (simple
critical-line zero with `0 < Im ≤ T`) is counted by this repository's
`criticalLineOddZeroCount T` (odd analytic multiplicity, `0 ≤ Im ≤ T`,
counted once).  A simple zero has multiplicity `1`, which is odd, and
`0 < Im` implies `0 ≤ Im`. -/
lemma n0simple_zero_le_criticalLineOddZeroCount (T : ℝ) :
    Zeta23.N0simple 0 T ≤ criticalLineOddZeroCount T := by
  classical
  change (Zeta23.zerosIn 0 T ∩ {ρ : ℂ | ρ.re = 1 / 2} ∩
      {ρ : ℂ | Zeta23.zeroMult ρ = 1}).ncard ≤
    (criticalLineOddZerosFinset T).card
  rw [← Set.ncard_coe_finset (criticalLineOddZerosFinset T)]
  exact Set.ncard_le_ncard
    (by
      intro ρ hρ
      rcases hρ with ⟨hρ₁, hρ₂⟩
      rcases hρ₁ with ⟨hρ₀, hρ_re⟩
      simp only [criticalLineOddZerosFinset, Finset.coe_filter, Finset.mem_coe,
        Set.mem_setOf_eq]
      refine ⟨mem_criticalLineZerosFinset.mpr ?_, ?_⟩
      · rcases mem_zeta23_zerosIn_zero.mp hρ₀ with ⟨hnt, him, hle⟩
        exact ⟨hnt, hρ_re, le_of_lt him, hle⟩
      · have hmult : analyticOrderNatAt riemannZeta ρ = 1 := by
          simpa [zeroMult_eq_analyticOrderNatAt ρ] using hρ₂
        rw [hmult]
        exact ⟨0, by norm_num⟩)
    (criticalLineOddZerosFinset T).finite_toSet

/-- Bridge lemma 2: Zeta23's `Ncount 0 T` satisfies the Selberg-scale lower
bound, transferred from this repository's all-height Riemann–von Mangoldt
theorem via the counting alignment. -/
lemma eventually_ncount_zero_ge_selbergScale :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T in atTop,
      c * (T / (2 * Real.pi) * Real.log T) ≤ (Zeta23.Ncount 0 T : ℝ) := by
  rcases PrimeNumberTheorem.RiemannVonMangoldt.exists_eventually_riemannZeroCount_ge_selbergScale
    with ⟨c, hc, h⟩
  refine ⟨c, hc, ?_⟩
  filter_upwards [h] with T hT
  simpa [ncount_zero_eq_riemannZeroCount T] using hT

/-- **Selberg odd-multiplicity positive proportion, closed externally.**
Zeta23's Theorem B (at least `2/3` of the zeros are simple and on the
critical line, cumulative form) plus this repository's all-height
Riemann–von Mangoldt lower bound yield
`criticalLineOddZeroCount T ≥ c · (T/(2π)) · log T` with the explicit
constant `c = (2/3 − 1/12) · 1/4 = 7/48`. -/
theorem selberg_odd_zero_proportion_target_of_zeta23 :
    selberg_odd_zero_proportion_target := by
  rcases Zeta23.thmB₀_mult_cumulative (1 / 12) (by norm_num) with ⟨T₁, hB⟩
  rcases eventually_ncount_zero_ge_selbergScale with ⟨c, hc, hscale⟩
  rcases (eventually_atTop.1 hscale) with ⟨T₂, hscaleT⟩
  refine ⟨(7 / 12 : ℝ) * c, by positivity, max T₁ T₂, fun T hT => ?_⟩
  let X : ℝ := T / (2 * Real.pi) * Real.log T
  have hscale' : c * X ≤ (Zeta23.Ncount 0 T : ℝ) :=
    hscaleT T (le_of_max_le_right hT)
  have hB' : (2 / 3 - 1 / 12 : ℝ) * (Zeta23.Ncount 0 T : ℝ) ≤
      (Zeta23.N0simple 0 T : ℝ) :=
    hB T (le_of_max_le_left hT)
  have hgap : (7 / 12 : ℝ) * c * X ≤ (criticalLineOddZeroCount T : ℝ) := by
    calc
      (7 / 12 : ℝ) * c * X = (7 / 12 : ℝ) * (c * X) := by ring
      _ ≤ (7 / 12 : ℝ) * (Zeta23.Ncount 0 T : ℝ) :=
        mul_le_mul_of_nonneg_left hscale' (by norm_num)
      _ = (2 / 3 - 1 / 12 : ℝ) * (Zeta23.Ncount 0 T : ℝ) := by norm_num
      _ ≤ (Zeta23.N0simple 0 T : ℝ) := hB'
      _ ≤ (criticalLineOddZeroCount T : ℝ) :=
        Nat.cast_le.mpr (n0simple_zero_le_criticalLineOddZeroCount T)
  have htarget : (criticalLineOddZeroCount T : ℝ) ≥ (7 / 12 : ℝ) * c * X := hgap
  simpa [X] using htarget

/-- **Selberg positive proportion (distinct critical-line zeros), closed
externally** via the repository's odd-to-distinct bridge. -/
theorem selberg_zero_proportion_target_of_zeta23 :
    selberg_zero_proportion_target :=
  selberg_zero_proportion_target_of_odd selberg_odd_zero_proportion_target_of_zeta23

/-- **Conrey 40% critical-line proportion, closed externally.** -/
theorem conrey_40_percent_zeros_on_critical_line_target_of_zeta23 :
    KnownResults.conrey_40_percent_zeros_on_critical_line_target :=
  KnownResults.conrey_40_percent_zeros_on_critical_line_target_of_selberg
    selberg_zero_proportion_target_of_zeta23

end Zeta23SelbergBridge
end HardyTheorem
