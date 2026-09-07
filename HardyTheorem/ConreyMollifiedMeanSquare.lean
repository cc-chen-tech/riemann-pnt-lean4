import HardyTheorem.ConreyMollifiedRectangleZeros
import HardyTheorem.ConreyLittlewoodMeanSquare
import MathlibAux.VerticalLogIntegrable

/-!
Jensen for the actual mollified product, allowing zeros on the shifted
left edge. The finite zero set, almost-everywhere nonvanishing and log
integrability are constructed. No mollified mean-square bound is assumed
or proved here: the right side retains the actual second-moment integral.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace HardyTheorem

/-- The actual left logarithmic integral is bounded by the actual positive
second moment, with exact interval-length normalization. -/
theorem conreyMollified_logNorm_meanSquare_bounds
    {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (hsigma : 0 < sigma0) (hsigmaHalf : sigma0 ≤ 1 / 2)
    (hA : 1 / 2 < A) (hU : 0 < U) (hUT : U < T)
    (hbottom : ∀ z ∈ (Icc sigma0 A ×ℂ Icc U T), z.im = U →
      conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P z ≠ 0) :
    0 < (∫ t in U..T,
      ‖conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P ((sigma0 : ℂ) + I * t)‖ ^ 2) ∧
      2 * (∫ t in U..T, Real.log
        ‖conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P ((sigma0 : ℂ) + I * t)‖) ≤
        (T - U) * Real.log ((∫ t in U..T,
          ‖conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P ((sigma0 : ℂ) + I * t)‖ ^ 2) /
          (T - U)) := by
  classical
  let F := conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P
  have hrect : ([[sigma0, A]] ×ℂ [[U, T]] : Set ℂ) = Icc sigma0 A ×ℂ Icc U T := by
    rw [uIcc_of_le (hsigmaHalf.trans hA.le), uIcc_of_le hUT.le]
  have hf : AnalyticOnNhd ℂ F ([[sigma0, A]] ×ℂ [[U, T]]) := by
    intro z hz
    rw [hrect] at hz
    have hz1 : z ≠ 1 := by
      intro heq
      have him := hz.2.1
      simp only [heq, Complex.one_im] at him
      linarith
    exact (analyticAt_conreyDegreeOneV1_of_re_pos_of_ne_one
      (g := g) (g0 := g0) (g1 := g1) (L := L) (hsigma.trans_le hz.1.1) hz1).mul
      (analyticOnNhd_conreyMollifier Y sigma0 P z (by simp))
  have hzmem : ∀ t ∈ Icc U T,
      (sigma0 : ℂ) + I * t ∈ ([[sigma0, A]] ×ℂ [[U, T]] : Set ℂ) := by
    intro t ht
    rw [hrect]
    simpa [mem_reProdIm] using
      And.intro (show sigma0 ∈ Icc sigma0 A from ⟨le_rfl, hsigmaHalf.trans hA.le⟩) ht
  have hcont : ContinuousOn (fun t : ℝ => F ((sigma0 : ℂ) + I * t)) (Icc U T) := by
    intro t ht
    have hparam : Continuous (fun t : ℝ => (sigma0 : ℂ) + I * t) := by fun_prop
    exact ((hf _ (hzmem t ht)).continuousAt.comp
      (f := fun y : ℝ => (sigma0 : ℂ) + I * y) hparam.continuousAt).continuousWithinAt
  have hlog := MathlibAux.intervalIntegrable_log_norm_vertical_of_analyticOnNhd
    hf (left_mem_uIcc : sigma0 ∈ [[sigma0, A]])
  obtain ⟨K, hK, _, _⟩ := exists_conreyMollified_rectangle_zero_finset
    hg hY hP1 hsigma hsigmaHalf hU hbottom
  let heights : Finset ℝ := K.image Complex.im
  have hne : ∀ᵐ t : ℝ ∂volume.restrict (Ioc U T), F ((sigma0 : ℂ) + I * t) ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      heights.countable_toSet.ae_notMem (volume.restrict (Ioc U T))] with t ht hnot
    intro hz0
    have hzK : (sigma0 : ℂ) + I * t ∈ K := by
      apply (hK _).mpr
      simpa only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, add_im, mul_im, one_mul, zero_add] using
        And.intro (le_refl sigma0)
          ⟨hsigmaHalf.trans hA.le, ht.1.le, ht.2, hz0⟩
    apply hnot
    exact Finset.mem_image.mpr ⟨(sigma0 : ℂ) + I * t, hzK, by simp⟩
  exact complex_log_interval_integral_bounds_of_ae_ne_zero hUT hcont hlog hne

end HardyTheorem
