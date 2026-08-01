import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicDynamicLeftHighPolylog

namespace PrimeNumberTheorem

open Set
open scoped Interval

/-- The scalar cubic tail is uniformly integrable: extending the outer height
does not introduce any positive power of that height. -/
theorem integral_rpow_neg_three_le_half_inv_sq
    {T H : ℝ} (hT : 0 < T) (hTH : T ≤ H) :
    0 ≤ (∫ t : ℝ in T..H, t ^ (-3 : ℝ)) ∧
      (∫ t : ℝ in T..H, t ^ (-3 : ℝ)) ≤ 1 / (2 * T ^ 2) := by
  have hzero : (0 : ℝ) ∉ [[T, H]] := by
    rw [uIcc_of_le hTH]
    simp only [mem_Icc, not_and_or]
    left
    linarith
  have hexact := integral_rpow (a := T) (b := H) (r := (-3 : ℝ))
    (Or.inr ⟨by norm_num, hzero⟩)
  have hH : 0 < H := hT.trans_le hTH
  constructor
  · apply intervalIntegral.integral_nonneg hTH
    intro t ht
    exact Real.rpow_nonneg (by linarith [ht.1]) _
  · rw [hexact]
    have hHrpow : 0 ≤ H ^ (-2 : ℝ) := Real.rpow_nonneg hH.le _
    have hdrop : (T ^ (-2 : ℝ) - H ^ (-2 : ℝ)) / 2 ≤
        T ^ (-2 : ℝ) / 2 := by linarith
    calc
      (H ^ ((-3 : ℝ) + 1) - T ^ ((-3 : ℝ) + 1)) / ((-3 : ℝ) + 1) =
          (T ^ (-2 : ℝ) - H ^ (-2 : ℝ)) / 2 := by norm_num; ring
      _ ≤ T ^ (-2 : ℝ) / 2 := hdrop
      _ = 1 / (2 * T ^ 2) := by
        rw [Real.rpow_neg (by positivity : 0 ≤ T), Real.rpow_two]
        field_simp [hT.ne']

end PrimeNumberTheorem
