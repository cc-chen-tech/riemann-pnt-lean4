import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Set MeasureTheory Complex
open scoped Interval

namespace MathlibAux

private theorem norm_integral_nonneg_log_power {f : ℝ → ℂ} {A D b M K : ℝ}
    (_hA : 0 ≤ A) (hD : 0 ≤ D) (hb : 0 < b) (hM : 1 ≤ M) (hK : M ≤ K)
    (hf : ContinuousOn f (Icc 0 K))
    (hlow : ∀ t ∈ Icc 0 M, ‖f t‖ ≤ A / (b + t))
    (hhigh : ∀ t ∈ Icc M K, ‖f t‖ ≤ D * t ^ (-3 / 2 : ℝ)) :
    ‖∫ t in (0 : ℝ)..K, f t‖ ≤ A * Real.log (1 + M / b) + 2 * D := by
  have hM0 : 0 ≤ M := by linarith
  have hK0 : 0 ≤ K := hM0.trans hK
  have hlo : ContinuousOn (fun t : ℝ => A / (b + t)) (Icc 0 M) := by
    intro t ht
    exact (continuousAt_const.div (continuousAt_const.add continuousAt_id)
      (by change b + t ≠ 0; linarith [ht.1])).continuousWithinAt
  have hhi : ContinuousOn (fun t : ℝ => D * t ^ (-3 / 2 : ℝ)) (Icc M K) := by
    intro t ht
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const t _
      (Or.inl (by linarith [ht.1])))).continuousWithinAt
  have hil : IntervalIntegrable f volume 0 M := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hM0]
    exact hf.mono (Icc_subset_Icc le_rfl hK)
  have hih : IntervalIntegrable f volume M K := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hK]
    exact hf.mono (Icc_subset_Icc hM0 le_rfl)
  have hlowIntegral : (∫ t in (0 : ℝ)..M, A / (b + t)) = A * Real.log (1 + M / b) := by
    simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_left, add_zero]
    rw [integral_inv_of_pos hb (by linarith)]
    congr 2
    field_simp
  have hhighIntegral : (∫ t in M..K, D * t ^ (-3 / 2 : ℝ)) ≤ 2 * D := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inr ⟨by norm_num, notMem_uIcc_of_lt (by linarith) (by linarith)⟩)]
    norm_num
    have hMn := Real.rpow_le_one_of_one_le_of_nonpos hM (by norm_num : (-1 / 2 : ℝ) ≤ 0)
    have hKn := Real.rpow_nonneg hK0 (-1 / 2 : ℝ)
    nlinarith only [hMn, hKn, hD]
  rw [← intervalIntegral.integral_add_adjacent_intervals hil hih]
  calc
    _ ≤ ‖∫ t in (0 : ℝ)..M, f t‖ + ‖∫ t in M..K, f t‖ := norm_add_le _ _
    _ ≤ (∫ t in (0 : ℝ)..M, A / (b + t)) + ∫ t in M..K, D * t ^ (-3 / 2 : ℝ) := by
      apply add_le_add
      · apply intervalIntegral.norm_integral_le_of_norm_le hM0
        · exact Filter.Eventually.of_forall (fun t ht => hlow t ⟨ht.1.le, ht.2⟩)
        · apply ContinuousOn.intervalIntegrable
          simpa [uIcc_of_le hM0] using hlo
      · apply intervalIntegral.norm_integral_le_of_norm_le hK
        · exact Filter.Eventually.of_forall (fun t ht => hhigh t ⟨ht.1.le, ht.2⟩)
        · apply ContinuousOn.intervalIntegrable
          simpa [uIcc_of_le hK] using hhi
    _ ≤ _ := by rw [hlowIntegral]; linarith

/-- A logarithmic core and two integrable power tails, retaining the core's
width loss. The function need not be even; reflection is used only to bound it. -/
theorem norm_integral_le_log_power_majorants {f : ℝ → ℂ} {A D b M K : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hb : 0 < b) (hM : 1 ≤ M) (hK : M ≤ K)
    (hf : ContinuousOn f (Icc (-K) K))
    (hlow : ∀ t ∈ Icc (-M) M, ‖f t‖ ≤ A / (b + |t|))
    (hhigh : ∀ t ∈ Icc (-K) K, M ≤ |t| → ‖f t‖ ≤ D * |t| ^ (-3 / 2 : ℝ)) :
    ‖∫ t in (-K)..K, f t‖ ≤ 2 * A * Real.log (1 + M / b) + 4 * D := by
  have hK0 : 0 ≤ K := by linarith
  have hpos : ContinuousOn f (Icc 0 K) := hf.mono (Icc_subset_Icc (by linarith) le_rfl)
  have hneg : ContinuousOn (fun t => f (-t)) (Icc 0 K) := by
    apply hf.comp continuous_neg.continuousOn
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hr := norm_integral_nonneg_log_power hA hD hb hM hK hpos
    (fun t ht => by simpa [abs_of_nonneg ht.1] using hlow t ⟨by linarith [ht.1], ht.2⟩)
    (fun t ht => by
      have ht0 : 0 ≤ t := by linarith [ht.1]
      simpa [abs_of_nonneg ht0] using hhigh t ⟨by linarith [ht.1], ht.2⟩
        (by simpa [abs_of_nonneg ht0] using ht.1))
  have hl := norm_integral_nonneg_log_power hA hD hb hM hK hneg
    (fun t ht => by
      simpa [abs_neg, abs_of_nonneg ht.1] using hlow (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    (fun t ht => by
      have ht0 : 0 ≤ t := by linarith [ht.1]
      simpa [abs_neg, abs_of_nonneg ht0] using hhigh (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
        (by simpa [abs_neg, abs_of_nonneg ht0] using ht.1))
  rw [intervalIntegral.integral_comp_neg, neg_zero] at hl
  have hil : IntervalIntegrable f volume (-K) 0 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith : -K ≤ 0)]
    exact hf.mono (Icc_subset_Icc le_rfl hK0)
  have hir : IntervalIntegrable f volume 0 K := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hK0] using hpos
  rw [← intervalIntegral.integral_add_adjacent_intervals hil hir]
  exact (norm_add_le _ _).trans (by linarith)

end MathlibAux
