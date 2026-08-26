import MathlibAux.LogMeanSquare

open MeasureTheory Set

namespace HardyTheorem

/-!
# The constant-exact mean-square bridge in Conrey's Littlewood argument

These lemmas contain only the logarithmic arithmetic--geometric mean step.
They do not state or assume the long mollified mean-square theorem.
-/

/-- A nonvanishing complex boundary function's logarithmic integral is
controlled, with exact normalization, by its second moment. -/
theorem complex_log_interval_integral_le_log_mean_normSq
    {F : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hF : ContinuousOn F (Icc a b))
    (hF0 : ∀ t ∈ Icc a b, F t ≠ 0) :
    2 * (∫ t in a..b, Real.log ‖F t‖) ≤
      (b - a) * Real.log ((∫ t in a..b, ‖F t‖ ^ 2) / (b - a)) := by
  have hnormSq_cont : ContinuousOn (fun t => ‖F t‖ ^ 2) (Icc a b) :=
    hF.norm.pow 2
  have hnormSq_pos : ∀ t ∈ Icc a b, 0 < ‖F t‖ ^ 2 := by
    intro t ht
    exact pow_pos (norm_pos_iff.mpr (hF0 t ht)) _
  have h := MathlibAux.integral_log_le_length_mul_log_mean
    hab hnormSq_cont hnormSq_pos
  simpa only [Real.log_pow, Nat.cast_ofNat,
    intervalIntegral.integral_const_mul] using h

/-- Inserting a second-moment upper bound costs no extra constant in the
Littlewood logarithmic boundary estimate. -/
theorem complex_log_interval_integral_le_of_normSq_integral_le
    {F : ℝ → ℂ} {a b C : ℝ} (hab : a < b) (hC : 0 < C)
    (hF : ContinuousOn F (Icc a b))
    (hF0 : ∀ t ∈ Icc a b, F t ≠ 0)
    (hM2 : (∫ t in a..b, ‖F t‖ ^ 2) ≤ C * (b - a)) :
    2 * (∫ t in a..b, Real.log ‖F t‖) ≤ (b - a) * Real.log C := by
  have hlength : 0 < b - a := sub_pos.mpr hab
  have hnormSq_cont : ContinuousOn (fun t => ‖F t‖ ^ 2) (Icc a b) :=
    hF.norm.pow 2
  have hnormSq_pos : ∀ t ∈ Icc a b, 0 < ‖F t‖ ^ 2 := by
    intro t ht
    exact pow_pos (norm_pos_iff.mpr (hF0 t ht)) _
  have hM2_pos : 0 < ∫ t in a..b, ‖F t‖ ^ 2 :=
    intervalIntegral.integral_pos hab hnormSq_cont
      (fun t ht => (hnormSq_pos t (Ioc_subset_Icc_self ht)).le)
      ⟨a, left_mem_Icc.mpr hab.le, hnormSq_pos a (left_mem_Icc.mpr hab.le)⟩
  have hmean_pos : 0 < (∫ t in a..b, ‖F t‖ ^ 2) / (b - a) :=
    div_pos hM2_pos hlength
  have hmean_le : (∫ t in a..b, ‖F t‖ ^ 2) / (b - a) ≤ C :=
    (div_le_iff₀ hlength).mpr (by simpa [mul_comm] using hM2)
  calc
    2 * (∫ t in a..b, Real.log ‖F t‖) ≤
        (b - a) * Real.log ((∫ t in a..b, ‖F t‖ ^ 2) / (b - a)) :=
      complex_log_interval_integral_le_log_mean_normSq hab hF hF0
    _ ≤ (b - a) * Real.log C :=
      mul_le_mul_of_nonneg_left
        ((Real.log_le_log_iff hmean_pos hC).mpr hmean_le) hlength.le

end HardyTheorem
