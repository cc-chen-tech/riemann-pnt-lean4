import PrimeNumberTheorem.CarlsonHalfRangeShellCount
import PrimeNumberTheorem.ZeroDensityCount

/-! Closed real-threshold zero counts and the unconditional Carlson shell recurrence.
Multiplicity is the actual analytic order of `riemannZeta`. -/

open Complex Filter
open scoped BigOperators

namespace PrimeNumberTheorem.ZeroDensity

noncomputable def zeroDensityClosedZerosFinset (sigma T : ℝ) : Finset ℂ :=
  (nontrivialZerosFinset T).filter fun rho => 0 < rho.im ∧ sigma ≤ rho.re

lemma mem_zeroDensityClosedZerosFinset {rho : ℂ} {sigma T : ℝ} :
    rho ∈ zeroDensityClosedZerosFinset sigma T ↔
      RiemannHypothesis.IsNontrivialZero rho ∧ 0 < rho.im ∧ rho.im ≤ T ∧ sigma ≤ rho.re := by
  simp only [zeroDensityClosedZerosFinset, Finset.mem_filter, mem_nontrivialZerosFinset]
  constructor
  · rintro ⟨⟨hz, hh⟩, hi, hr⟩
    exact ⟨hz, hi, by simpa [abs_of_pos hi] using hh, hr⟩
  · rintro ⟨hz, hi, hh, hr⟩
    exact ⟨⟨hz, by simpa [abs_of_pos hi] using hh⟩, hi, hr⟩

noncomputable def zeroDensityClosedCount (sigma T : ℝ) : ℕ :=
  ∑ rho ∈ zeroDensityClosedZerosFinset sigma T, analyticOrderNatAt riemannZeta rho

theorem zeroDensityClosedCount_mono_height {sigma U T : ℝ} (hUT : U ≤ T) :
    zeroDensityClosedCount sigma U ≤ zeroDensityClosedCount sigma T := by
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.zero_le _)
  intro rho hrho
  obtain ⟨hz, hi, hh, hr⟩ := mem_zeroDensityClosedZerosFinset.mp hrho
  exact mem_zeroDensityClosedZerosFinset.mpr ⟨hz, hi, hh.trans hUT, hr⟩

theorem zeroDensityCount_le_closedCount (sigma T : ℝ) :
    zeroDensityCount sigma T ≤ zeroDensityClosedCount sigma T := by
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.zero_le _)
  intro rho hrho
  obtain ⟨hz, hi, hh, hr⟩ := mem_zeroDensityZerosFinset.mp hrho
  exact mem_zeroDensityClosedZerosFinset.mpr ⟨hz, hi, hh, hr.le⟩

theorem zeroDensityClosedCount_le_globalZeroMultiplicity (sigma T : ℝ) :
    (zeroDensityClosedCount sigma T : ℝ) ≤ ExplicitFormulaAux.globalZeroMultiplicity T := by
  simp only [zeroDensityClosedCount, Nat.cast_sum, ExplicitFormulaAux.globalZeroMultiplicity]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => Nat.cast_nonneg _)

theorem zeroDensityClosedCount_step_eq {sigma U T : ℝ} (hUT : U ≤ T) :
    zeroDensityClosedCount sigma T = zeroDensityClosedCount sigma U +
      ∑ rho ∈ (zeroDensityClosedZerosFinset sigma T).filter (fun rho => U < rho.im),
        analyticOrderNatAt riemannZeta rho := by
  classical
  have hlow : (zeroDensityClosedZerosFinset sigma T).filter (fun rho => rho.im ≤ U) =
      zeroDensityClosedZerosFinset sigma U := by
    ext rho
    simp only [Finset.mem_filter, mem_zeroDensityClosedZerosFinset]
    constructor
    · rintro ⟨⟨hz, hi, _, hr⟩, hh⟩
      exact ⟨hz, hi, hh, hr⟩
    · rintro ⟨hz, hi, hh, hr⟩
      exact ⟨⟨hz, hi, hh.trans hUT, hr⟩, hh⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (zeroDensityClosedZerosFinset sigma T) (fun rho => rho.im ≤ U)
    (fun rho => analyticOrderNatAt riemannZeta rho)
  simpa only [hlow, not_le, zeroDensityClosedCount] using hsplit.symm

theorem exists_eventually_closedCount_twoThirds_step_le :
    ∃ K > (0 : ℝ), ∀ᶠ U : ℝ in atTop,
      (zeroDensityClosedCount (2 / 3) (9 * U / 8) : ℝ) ≤
        (zeroDensityClosedCount (2 / 3) U : ℝ) +
          K * U ^ (8 / 9 - 1 / 400 : ℝ) * (1 + Real.log U) ^ 6 := by
  classical
  obtain ⟨K, hK, hbound⟩ := CarlsonZeroDensity.exists_eventually_halfRange_shellFamilyCount_le
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (0 : ℝ)] with U hbound hU
  let S := (zeroDensityClosedZerosFinset (2 / 3) (9 * U / 8)).filter (fun rho => U < rho.im)
  have hS : ∀ rho ∈ S, RiemannHypothesis.IsNontrivialZero rho ∧
      (2 / 3 : ℝ) ≤ rho.re ∧ U ≤ rho.im ∧ rho.im ≤ 9 * U / 8 := by
    intro rho hrho
    obtain ⟨hmem, hh⟩ := Finset.mem_filter.mp hrho
    obtain ⟨hz, _, ht, hr⟩ := mem_zeroDensityClosedZerosFinset.mp hmem
    exact ⟨hz, hr, hh.le, ht⟩
  have hsplit := zeroDensityClosedCount_step_eq (sigma := (2 / 3 : ℝ))
    (by linarith only [hU] : U ≤ 9 * U / 8)
  rw [hsplit, Nat.cast_add, Nat.cast_sum]
  exact add_le_add_right (hbound S hS) _

end PrimeNumberTheorem.ZeroDensity
