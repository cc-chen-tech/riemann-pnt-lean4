import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Uniform approximation of shifted autocorrelations

This module bounds the error made when a continuous real function is replaced
by a uniformly close model inside a shifted autocorrelation integral.  The
common control interval contains both `[A, B]` and its translate by `τ`.
-/

open MeasureTheory Set

namespace MathlibAux

/-- A point of `[A, B]` belongs to the interval containing `[A, B]` and its
translate by `τ`. -/
theorem mem_autocorrelationControlInterval
    {A B τ x : ℝ} (hx : x ∈ Icc A B) :
    x ∈ Icc (min A (A + τ)) (max B (B + τ)) := by
  constructor
  · exact (min_le_left A (A + τ)).trans (mem_Icc.mp hx).1
  · exact (mem_Icc.mp hx).2.trans (le_max_left B (B + τ))

/-- The translate by `τ` of a point of `[A, B]` belongs to the interval
containing `[A, B]` and its translate. -/
theorem add_mem_autocorrelationControlInterval
    {A B τ x : ℝ} (hx : x ∈ Icc A B) :
    x + τ ∈ Icc (min A (A + τ)) (max B (B + τ)) := by
  constructor
  · refine (min_le_right A (A + τ)).trans ?_
    simpa [add_comm] using add_le_add_right (mem_Icc.mp hx).1 τ
  · have hxb : x + τ ≤ B + τ := by
      simpa [add_comm] using add_le_add_right (mem_Icc.mp hx).2 τ
    exact hxb.trans (le_max_right B (B + τ))

/-- Uniform approximation on the interval containing `[A, B]` and its
translate by `τ` controls the corresponding shifted autocorrelation.

The factor `2 * M * eps` comes from
`F x * F (x + τ) - P x * P (x + τ) =
  (F x - P x) * F (x + τ) + P x * (F (x + τ) - P (x + τ))`.
-/
theorem abs_integral_mul_shift_sub_mul_shift_le_of_continuousOn
    {F P : ℝ → ℝ} {A B τ eps M : ℝ}
    (hF : ContinuousOn F
      (Icc (min A (A + τ)) (max B (B + τ))))
    (hP : ContinuousOn P
      (Icc (min A (A + τ)) (max B (B + τ))))
    (hAB : A ≤ B) (heps : 0 ≤ eps) (hM : 0 ≤ M)
    (happrox : ∀ x ∈ Icc (min A (A + τ)) (max B (B + τ)),
      |F x - P x| ≤ eps)
    (hFbound : ∀ x ∈ Icc (min A (A + τ)) (max B (B + τ)), |F x| ≤ M)
    (hPbound : ∀ x ∈ Icc (min A (A + τ)) (max B (B + τ)), |P x| ≤ M) :
    |(∫ x in A..B, F x * F (x + τ)) -
        ∫ x in A..B, P x * P (x + τ)| ≤
      (B - A) * (2 * M * eps) := by
  let f : ℝ → ℝ := fun x => F x * F (x + τ)
  let p : ℝ → ℝ := fun x => P x * P (x + τ)
  have hdomain :
      Set.uIcc A B = Icc A B := uIcc_of_le hAB
  have hbaseMaps :
      MapsTo (fun x : ℝ => x) (Set.uIcc A B)
        (Icc (min A (A + τ)) (max B (B + τ))) := by
    intro x hx
    exact mem_autocorrelationControlInterval
      (by simpa only [hdomain] using hx)
  have hshiftMaps :
      MapsTo (fun x : ℝ => x + τ) (Set.uIcc A B)
        (Icc (min A (A + τ)) (max B (B + τ))) := by
    intro x hx
    exact add_mem_autocorrelationControlInterval
      (by simpa only [hdomain] using hx)
  have hFbase : ContinuousOn F (Set.uIcc A B) :=
    hF.mono hbaseMaps
  have hPbase : ContinuousOn P (Set.uIcc A B) :=
    hP.mono hbaseMaps
  have hFshift : ContinuousOn (fun x : ℝ => F (x + τ))
      (Set.uIcc A B) := by
    simpa only [Function.comp_def] using
      hF.comp (continuous_id.add continuous_const).continuousOn hshiftMaps
  have hPshift : ContinuousOn (fun x : ℝ => P (x + τ))
      (Set.uIcc A B) := by
    simpa only [Function.comp_def] using
      hP.comp (continuous_id.add continuous_const).continuousOn hshiftMaps
  have hf_cont : ContinuousOn f (Set.uIcc A B) := by
    dsimp only [f]
    exact hFbase.mul hFshift
  have hp_cont : ContinuousOn p (Set.uIcc A B) := by
    dsimp only [p]
    exact hPbase.mul hPshift
  have hf_int : IntervalIntegrable f volume A B := hf_cont.intervalIntegrable
  have hp_int : IntervalIntegrable p volume A B := hp_cont.intervalIntegrable
  have hpoint : ∀ x ∈ Set.uIoc A B, ‖f x - p x‖ ≤ 2 * M * eps := by
    intro x hx
    have hxIcc : x ∈ Icc A B := by
      rw [uIoc_of_le hAB] at hx
      exact ⟨hx.1.le, hx.2⟩
    have hxControl := mem_autocorrelationControlInterval (τ := τ) hxIcc
    have hxShiftControl := add_mem_autocorrelationControlInterval (τ := τ) hxIcc
    have hfirst :
        |F x - P x| * |F (x + τ)| ≤ eps * M :=
      mul_le_mul (happrox x hxControl) (hFbound (x + τ) hxShiftControl)
        (abs_nonneg _) heps
    have hsecond :
        |P x| * |F (x + τ) - P (x + τ)| ≤ M * eps :=
      mul_le_mul (hPbound x hxControl) (happrox (x + τ) hxShiftControl)
        (abs_nonneg _) hM
    calc
      ‖f x - p x‖ =
          |(F x - P x) * F (x + τ) +
            P x * (F (x + τ) - P (x + τ))| := by
            simp only [Real.norm_eq_abs, f, p]
            congr 1
            ring
      _ ≤ |(F x - P x) * F (x + τ)| +
          |P x * (F (x + τ) - P (x + τ))| := abs_add_le _ _
      _ = |F x - P x| * |F (x + τ)| +
          |P x| * |F (x + τ) - P (x + τ)| := by
            rw [abs_mul, abs_mul]
      _ ≤ eps * M + M * eps := add_le_add hfirst hsecond
      _ = 2 * M * eps := by ring
  have hnorm :
      ‖∫ x in A..B, f x - p x‖ ≤ (2 * M * eps) * |B - A| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  calc
    |(∫ x in A..B, F x * F (x + τ)) -
        ∫ x in A..B, P x * P (x + τ)| =
        ‖∫ x in A..B, f x - p x‖ := by
          rw [intervalIntegral.integral_sub hf_int hp_int]
          rfl
    _ ≤ (2 * M * eps) * |B - A| := hnorm
    _ = (B - A) * (2 * M * eps) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hAB)]
      ring

/-- The global-continuity version is a direct corollary of the localized
statement above. -/
theorem abs_integral_mul_shift_sub_mul_shift_le
    {F P : ℝ → ℝ} (hF : Continuous F) (hP : Continuous P)
    {A B τ eps M : ℝ} (hAB : A ≤ B) (heps : 0 ≤ eps) (hM : 0 ≤ M)
    (happrox : ∀ x ∈ Icc (min A (A + τ)) (max B (B + τ)),
      |F x - P x| ≤ eps)
    (hFbound : ∀ x ∈ Icc (min A (A + τ)) (max B (B + τ)), |F x| ≤ M)
    (hPbound : ∀ x ∈ Icc (min A (A + τ)) (max B (B + τ)), |P x| ≤ M) :
    |(∫ x in A..B, F x * F (x + τ)) -
        ∫ x in A..B, P x * P (x + τ)| ≤
      (B - A) * (2 * M * eps) :=
  abs_integral_mul_shift_sub_mul_shift_le_of_continuousOn
    hF.continuousOn hP.continuousOn hAB heps hM happrox hFbound hPbound

end MathlibAux
