import HardyTheorem.SelbergFirstMomentParameter
import MathlibAux.SlidingWindowFirstMoment

open Complex MeasureTheory Set
open scoped Interval

namespace HardyTheorem

/-! # Selberg S4b: the sliding absolute first moment -/

/-- Selberg S4b for the actual cutoff.  The dyadic localization of S4a makes
the endpoint bookkeeping exact: if `H ≤ T/2`, the interior `[H,T]` already
contains the complete S4a interval `[T/2,T]`. -/
theorem exists_pos_rpow_three_quarters_selbergSlidingFirstMoment_lower :
    ∃ c T0 : ℝ, 0 < c ∧ 2 ≤ T0 ∧
      ∀ T H : ℝ, T0 ≤ T → 0 ≤ H → H ≤ T / 2 →
        c * (H * T ^ (3 / 4 : ℝ)) ≤
          ∫ t in 0..T,
            ∫ u in t..t + H,
              |selbergCompletedMollifiedF (1 / T)
                (selbergFirstMomentCutoff T) u| := by
  obtain ⟨c, T0, hc, hT0, hdyadic⟩ :=
    exists_pos_rpow_three_quarters_selbergFirstMomentCutoff_lower
  refine ⟨c, T0, hc, hT0, ?_⟩
  intro T H hT hH hHT
  have hTpos : 0 < T := zero_lt_two.trans_le (hT0.trans hT)
  let g : ℝ → ℝ := fun u =>
    |selbergCompletedMollifiedF (1 / T) (selbergFirstMomentCutoff T) u|
  have hg : Continuous g :=
    (continuous_selbergCompletedMollifiedF
      (1 / T) (selbergFirstMomentCutoff T)).abs
  have hinterior :
      (∫ u in T / 2..T, g u) ≤ ∫ u in H..T, g u := by
    apply intervalIntegral.integral_mono_interval hHT (by linarith) le_rfl
    · exact Filter.Eventually.of_forall fun _ => abs_nonneg _
    · exact hg.intervalIntegrable _ _
  have hslide := MathlibAux.length_mul_integral_interior_le_integral_slidingWindow
    (T := T) (H := H) hg (fun _ => abs_nonneg _) hH (by linarith [hHT])
  calc
    c * (H * T ^ (3 / 4 : ℝ)) = H * (c * T ^ (3 / 4 : ℝ)) := by ring
    _ ≤ H * (∫ u in T / 2..T, g u) :=
      mul_le_mul_of_nonneg_left (hdyadic T hT) hH
    _ ≤ H * (∫ u in H..T, g u) :=
      mul_le_mul_of_nonneg_left hinterior hH
    _ ≤ ∫ t in 0..T, ∫ u in t..t + H, g u := hslide

end HardyTheorem
