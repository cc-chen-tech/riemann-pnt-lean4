import HardyTheorem.CriticalLineMultiplicity
import PrimeNumberTheorem.RiemannVonMangoldt.ZeroCount

open Complex Filter Topology
open scoped BigOperators

namespace HardyTheorem

/-!
# The multiplicity-sensitive target for Conrey's two-fifths theorem

Conrey's numerator counts simple zeta zeros on the critical line, while the
Riemann--von Mangoldt denominator counts all positive-height nontrivial zeros
with analytic multiplicity.  This file defines both sides using the same
ambient finset, so their height conventions agree exactly.
-/

/-- Nontrivial zeta zeros with `0 < Im ρ ≤ T` which lie on the critical line
and have analytic multiplicity exactly one. -/
noncomputable def positiveCriticalLineSimpleZerosFinset (T : ℝ) : Finset ℂ :=
  (PrimeNumberTheorem.RiemannVonMangoldt.positiveNontrivialZerosFinset T).filter
    fun ρ => ρ.re = 1 / 2 ∧ analyticOrderNatAt riemannZeta ρ = 1

lemma mem_positiveCriticalLineSimpleZerosFinset {T : ℝ} {ρ : ℂ} :
    ρ ∈ positiveCriticalLineSimpleZerosFinset T ↔
      RiemannHypothesis.IsNontrivialZero ρ ∧
        0 < ρ.im ∧ ρ.im ≤ T ∧ ρ.re = 1 / 2 ∧
        analyticOrderNatAt riemannZeta ρ = 1 := by
  classical
  simp only [positiveCriticalLineSimpleZerosFinset, Finset.mem_filter,
    PrimeNumberTheorem.RiemannVonMangoldt.mem_positiveNontrivialZerosFinset]
  aesop

/-- Conrey's `N₀*(T)`: the number of positive-height simple critical-line
zeros up to height `T`.  Each zero occurs once because it is simple. -/
noncomputable def positiveCriticalLineSimpleZeroCount (T : ℝ) : ℕ :=
  (positiveCriticalLineSimpleZerosFinset T).card

lemma positiveCriticalLineSimpleZerosFinset_subset {U T : ℝ} (hUT : U ≤ T) :
    positiveCriticalLineSimpleZerosFinset U ⊆
      positiveCriticalLineSimpleZerosFinset T := by
  intro ρ hρ
  rw [mem_positiveCriticalLineSimpleZerosFinset] at hρ ⊢
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.1.trans hUT,
    hρ.2.2.2.1, hρ.2.2.2.2⟩

lemma positiveCriticalLineSimpleZeroCount_mono {U T : ℝ} (hUT : U ≤ T) :
    positiveCriticalLineSimpleZeroCount U ≤
      positiveCriticalLineSimpleZeroCount T := by
  classical
  exact Finset.card_le_card
    (positiveCriticalLineSimpleZerosFinset_subset hUT)

lemma positiveCriticalLineSimpleZerosFinset_subset_positiveNontrivialZerosFinset
    (T : ℝ) :
    positiveCriticalLineSimpleZerosFinset T ⊆
      PrimeNumberTheorem.RiemannVonMangoldt.positiveNontrivialZerosFinset T :=
  Finset.filter_subset _ _

/-- The simple critical-line count is bounded by the full Riemann--von
Mangoldt count, whose summands are analytic multiplicities. -/
lemma positiveCriticalLineSimpleZeroCount_le_riemannZeroCount (T : ℝ) :
    positiveCriticalLineSimpleZeroCount T ≤
      PrimeNumberTheorem.RiemannVonMangoldt.riemannZeroCount T := by
  classical
  rw [positiveCriticalLineSimpleZeroCount, Finset.card_eq_sum_ones,
    PrimeNumberTheorem.RiemannVonMangoldt.riemannZeroCount]
  calc
    ∑ ρ ∈ positiveCriticalLineSimpleZerosFinset T, 1 =
        ∑ ρ ∈ positiveCriticalLineSimpleZerosFinset T,
          analyticOrderNatAt riemannZeta ρ := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      exact (mem_positiveCriticalLineSimpleZerosFinset.mp hρ).2.2.2.2.symm
    _ ≤ ∑ ρ ∈
        PrimeNumberTheorem.RiemannVonMangoldt.positiveNontrivialZerosFinset T,
          analyticOrderNatAt riemannZeta ρ :=
      Finset.sum_le_sum_of_subset
        (positiveCriticalLineSimpleZerosFinset_subset_positiveNontrivialZerosFinset T)

/-- Genuine multiplicity-sensitive formulation of Conrey's strict two-fifths
theorem.  The eventual inequality avoids dividing by `N(T)` at small heights
where the denominator may vanish. -/
def conreyTwoFifthsSimpleZerosTarget : Prop :=
  ∃ c : ℝ, 2 / 5 < c ∧
    ∀ᶠ T in atTop,
      c * (PrimeNumberTheorem.RiemannVonMangoldt.riemannZeroCount T : ℝ) ≤
        (positiveCriticalLineSimpleZeroCount T : ℝ)

end HardyTheorem
