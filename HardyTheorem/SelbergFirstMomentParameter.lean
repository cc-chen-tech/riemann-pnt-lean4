import HardyTheorem.SelbergFirstMomentLower

open Complex MeasureTheory Set Filter
open scoped Interval

namespace HardyTheorem

/-!
# The fixed Selberg first-moment parameter

We now make the paper choice `X = floor (T^(1/32))`.  The exponent is kept
literal so that the horizontal contour cost has exponent
`1/32 + 1/2 = 17/32 < 1`.  This module proves the two eventual absorption
inequalities required by `SelbergFirstMomentLower` and hence closes S4a for
the actual integer mollifier length.
-/

/-- The integer mollifier length used throughout the final Selberg
specialization. -/
noncomputable def selbergFirstMomentCutoff (T : ℝ) : ℕ :=
  Nat.floor (T ^ (1 / 32 : ℝ))

/-- The fixed right-edge remainder and the `X sqrt T` horizontal error are
both eventually at most `T / 8` for `X = floor (T^(1/32))`. -/
theorem eventually_selbergFirstMomentCutoff_absorbs_contour_errors
    {C : ℝ} (hC : 0 < C) :
    ∀ᶠ T : ℝ in atTop,
      2 ≤ selbergFirstMomentCutoff T ∧
      16 / Real.log 2 ≤ T / 8 ∧
      2 * C * selbergFirstMomentCutoff T * Real.sqrt (T / 2) ≤ T / 8 := by
  have hcutoffLarge : ∀ᶠ T : ℝ in atTop,
      (2 : ℝ) ≤ T ^ (1 / 32 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 32)).eventually_ge_atTop 2
  have hpowerLarge : ∀ᶠ T : ℝ in atTop,
      16 * C ≤ T ^ (15 / 32 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 15 / 32)).eventually_ge_atTop
      (16 * C)
  have hTOne : ∀ᶠ T : ℝ in atTop, (1 : ℝ) ≤ T := eventually_ge_atTop 1
  have hfixedLarge : ∀ᶠ T : ℝ in atTop,
      128 / Real.log 2 ≤ T := eventually_ge_atTop (128 / Real.log 2)
  filter_upwards [hcutoffLarge, hpowerLarge, hTOne, hfixedLarge]
    with T hcutoff hpower hT1 hfixed
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have hX : 2 ≤ selbergFirstMomentCutoff T := by
    unfold selbergFirstMomentCutoff
    exact Nat.le_floor hcutoff
  have hfixed' : 16 / Real.log 2 ≤ T / 8 := by
    have hreorder : 128 / Real.log 2 = 8 * (16 / Real.log 2) := by ring
    rw [hreorder] at hfixed
    linarith
  have hXupper : (selbergFirstMomentCutoff T : ℝ) ≤
      T ^ (1 / 32 : ℝ) := by
    unfold selbergFirstMomentCutoff
    exact Nat.floor_le (Real.rpow_nonneg (le_of_lt hTpos) _)
  have hsqrt : Real.sqrt (T / 2) ≤ T ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt (by linarith)
  have hproduct : (selbergFirstMomentCutoff T : ℝ) * Real.sqrt (T / 2) ≤
      T ^ (17 / 32 : ℝ) := by
    calc
      (selbergFirstMomentCutoff T : ℝ) * Real.sqrt (T / 2) ≤
          T ^ (1 / 32 : ℝ) * T ^ (1 / 2 : ℝ) := by
        exact mul_le_mul hXupper hsqrt (Real.sqrt_nonneg _) (by positivity)
      _ = T ^ (17 / 32 : ℝ) := by
        rw [← Real.rpow_add hTpos]
        norm_num
  have hscaled : 2 * C * (selbergFirstMomentCutoff T : ℝ) *
      Real.sqrt (T / 2) ≤ 2 * C * T ^ (17 / 32 : ℝ) := by
    calc
      2 * C * (selbergFirstMomentCutoff T : ℝ) * Real.sqrt (T / 2) =
          (2 * C) * ((selbergFirstMomentCutoff T : ℝ) *
            Real.sqrt (T / 2)) := by ring
      _ ≤ (2 * C) * T ^ (17 / 32 : ℝ) :=
        mul_le_mul_of_nonneg_left hproduct (by positivity)
      _ = 2 * C * T ^ (17 / 32 : ℝ) := rfl
  have hpowers : T ^ (15 / 32 : ℝ) * T ^ (17 / 32 : ℝ) = T := by
    rw [← Real.rpow_add hTpos]
    norm_num
  have hdom := mul_le_mul_of_nonneg_right hpower
    (Real.rpow_nonneg hTpos.le (17 / 32 : ℝ))
  rw [hpowers] at hdom
  refine ⟨hX, hfixed', hscaled.trans ?_⟩
  linarith

/-- Selberg S4a for the actual integer cutoff and the paper tilt
`delta = 1 / T`: the absolute completed first moment on the dyadic interval
has the required `T^(3/4)` lower bound. -/
theorem exists_pos_rpow_three_quarters_selbergFirstMomentCutoff_lower :
    ∃ c T0 : ℝ, 0 < c ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T →
        c * T ^ (3 / 4 : ℝ) ≤
          ∫ t in T / 2..T,
            |selbergCompletedMollifiedF (1 / T)
              (selbergFirstMomentCutoff T) t| := by
  obtain ⟨c, C, Tbase, hc, hC, hTbase, hfirstMoment⟩ :=
    exists_pos_rpow_three_quarters_firstMoment_of_horizontal_absorption
  have hparam := eventually_selbergFirstMomentCutoff_absorbs_contour_errors hC
  obtain ⟨Tparam, hparamAfter⟩ := Filter.eventually_atTop.1 hparam
  refine ⟨c, max Tbase Tparam, hc, hTbase.trans (le_max_left _ _), ?_⟩
  intro T hT
  have hbase : Tbase ≤ T := (le_max_left _ _).trans hT
  have hTpos : 0 < T := zero_lt_two.trans_le (hTbase.trans hbase)
  have hparamT : Tparam ≤ T := (le_max_right _ _).trans hT
  rcases hparamAfter T hparamT with ⟨hX, hfixed, hhorizontal⟩
  exact hfirstMoment T (1 / T) (selbergFirstMomentCutoff T)
    hbase hX (one_div_nonneg.mpr hTpos.le) le_rfl hfixed hhorizontal

/-- The paper-form S4a statement on `[0,T]`.  It follows from the dyadic
theorem because the integrand is continuous and nonnegative. -/
theorem exists_pos_rpow_three_quarters_selbergFirstMomentCutoff_zero_T_lower :
    ∃ c T0 : ℝ, 0 < c ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T →
        c * T ^ (3 / 4 : ℝ) ≤
          ∫ t in 0..T,
            |selbergCompletedMollifiedF (1 / T)
              (selbergFirstMomentCutoff T) t| := by
  obtain ⟨c, T0, hc, hT0, hdyadic⟩ :=
    exists_pos_rpow_three_quarters_selbergFirstMomentCutoff_lower
  refine ⟨c, T0, hc, hT0, ?_⟩
  intro T hT
  have hTpos : 0 < T := zero_lt_two.trans_le (hT0.trans hT)
  let f : ℝ → ℝ := fun t =>
    |selbergCompletedMollifiedF (1 / T) (selbergFirstMomentCutoff T) t|
  have hfint : IntervalIntegrable f volume 0 T :=
    (continuous_selbergCompletedMollifiedF
      (1 / T) (selbergFirstMomentCutoff T)).abs.intervalIntegrable _ _
  have hmono : (∫ t in T / 2..T, f t) ≤ ∫ t in 0..T, f t := by
    apply intervalIntegral.integral_mono_interval
      (by linarith) (by linarith) le_rfl
    · exact Filter.Eventually.of_forall fun _ => abs_nonneg _
    · exact hfint
  exact (hdyadic T hT).trans hmono

end HardyTheorem
