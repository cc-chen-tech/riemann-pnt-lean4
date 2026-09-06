import HardyTheorem.SelbergS12PerronBound

open scoped BigOperators

namespace HardyTheorem

/-!
# Selberg S12: optimizing the absolute-convergence line

For `Y ≥ e`, choose `epsilon = 1 / log Y`.  Then `epsilon ≤ 1` and the
otherwise costly factor `Y^epsilon` is exactly `e`.
-/

theorem exists_norm_selbergS12WeightedCoprimeSum_optimized_le :
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ (r : ℕ) [NeZero r] (theta : ℝ) (Y : ℕ),
        0 ≤ theta → Real.exp 1 ≤ (Y : ℝ) →
        ‖selbergS12WeightedCoprimeSum r theta Y‖ ≤
          E * ((Y : ℝ) ^ theta) /
              Real.sqrt (theta + (Real.log (Y : ℝ))⁻¹) *
            Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := by
  rcases exists_norm_selbergS12WeightedCoprimeSum_le with ⟨D, hD, hgeneral⟩
  let E : ℝ := D * Real.exp 1
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  refine ⟨E, hE, ?_⟩
  intro r _ theta Y htheta hYexp
  have hYpos : (0 : ℝ) < Y := (Real.exp_pos 1).trans_le hYexp
  have hYnat : 0 < Y := by exact_mod_cast hYpos
  have hYone : (Y : ℝ) ≠ 1 := by
    intro h
    rw [h] at hYexp
    have := Real.exp_one_gt_d9
    linarith
  have hlog : 1 ≤ Real.log (Y : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hYexp
  have hlogpos : 0 < Real.log (Y : ℝ) := zero_lt_one.trans_le hlog
  have hepsilon : 0 < (Real.log (Y : ℝ))⁻¹ := inv_pos.mpr hlogpos
  have hepsilon1 : (Real.log (Y : ℝ))⁻¹ ≤ 1 := by
    exact (inv_le_one₀ hlogpos).2 hlog
  have h := hgeneral r theta (Real.log (Y : ℝ))⁻¹ Y
    htheta hepsilon hepsilon1 hYnat
  rw [Real.rpow_add hYpos,
    Real.rpow_inv_log hYpos hYone] at h
  calc
    ‖selbergS12WeightedCoprimeSum r theta Y‖ ≤
        D * ((Y : ℝ) ^ theta * Real.exp 1) /
            Real.sqrt (theta + (Real.log (Y : ℝ))⁻¹) *
          Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := h
    _ = E * ((Y : ℝ) ^ theta) /
            Real.sqrt (theta + (Real.log (Y : ℝ))⁻¹) *
          Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := by
      dsimp [E]
      ring

/-- The standard S12 form for the large-`Y` range.  This is the bound used
in Selberg's arithmetic energy estimate. -/
theorem exists_norm_selbergS12WeightedCoprimeSum_s12_le :
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ (r : ℕ) [NeZero r] (theta : ℝ) (Y : ℕ),
        0 ≤ theta → Real.exp 1 ≤ (Y : ℝ) →
        ‖selbergS12WeightedCoprimeSum r theta Y‖ ≤
          E * ((Y : ℝ) ^ theta) * Real.sqrt (Real.log (Y : ℝ)) *
            Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := by
  rcases exists_norm_selbergS12WeightedCoprimeSum_optimized_le with
    ⟨E, hE, hoptimized⟩
  refine ⟨E, hE, ?_⟩
  intro r _ theta Y htheta hYexp
  have hlog : 0 < Real.log (Y : ℝ) :=
    Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hYexp)
  have hinv : 0 < (Real.log (Y : ℝ))⁻¹ := inv_pos.mpr hlog
  have hsqrtLe :
      Real.sqrt (Real.log (Y : ℝ))⁻¹ ≤
        Real.sqrt (theta + (Real.log (Y : ℝ))⁻¹) := by
    exact Real.sqrt_le_sqrt (by linarith)
  have hsqrtInvPos : 0 < Real.sqrt (Real.log (Y : ℝ))⁻¹ :=
    Real.sqrt_pos.2 hinv
  have hreciprocal :
      1 / Real.sqrt (theta + (Real.log (Y : ℝ))⁻¹) ≤
        Real.sqrt (Real.log (Y : ℝ)) := by
    calc
      1 / Real.sqrt (theta + (Real.log (Y : ℝ))⁻¹) ≤
          1 / Real.sqrt (Real.log (Y : ℝ))⁻¹ := by
        exact one_div_le_one_div_of_le hsqrtInvPos hsqrtLe
      _ = Real.sqrt (Real.log (Y : ℝ)) := by
        rw [Real.sqrt_inv]
        field_simp
  have h := hoptimized r theta Y htheta hYexp
  have hreciprocal' :
      (Real.sqrt (theta + (Real.log (Y : ℝ))⁻¹))⁻¹ ≤
        Real.sqrt (Real.log (Y : ℝ)) := by
    simpa only [one_div] using hreciprocal
  calc
    ‖selbergS12WeightedCoprimeSum r theta Y‖ ≤
        E * ((Y : ℝ) ^ theta) /
            Real.sqrt (theta + (Real.log (Y : ℝ))⁻¹) *
          Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := h
    _ ≤ E * ((Y : ℝ) ^ theta) * Real.sqrt (Real.log (Y : ℝ)) *
          Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := by
      rw [div_eq_mul_inv]
      gcongr

end HardyTheorem
