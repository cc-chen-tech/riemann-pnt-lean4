import HardyTheorem.ConreyHorizontalArgument
import HardyTheorem.ConreyRightArgument
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-! Actual eta logarithmic derivatives and the archimedean/right-edge
argument estimates. Every integral split has proved integrability. -/

open Complex Set Filter MeasureTheory Topology

namespace HardyTheorem

private theorem conreyH_analyticAt_pos {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ conreyH s := by
  have hi : AnalyticAt ℂ (fun z : ℂ => (Gammaℝ z)⁻¹) s :=
    differentiable_Gammaℝ_inv.analyticAt s
  have hgamma : AnalyticAt ℂ Gammaℝ s := by
    have hfun : (fun z : ℂ => ((Gammaℝ z)⁻¹)⁻¹) = Gammaℝ := by
      funext z
      simp
    rw [← hfun]
    exact hi.inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs))
  exact (((analyticAt_const.mul analyticAt_id).mul
    (analyticAt_id.sub analyticAt_const)).mul hgamma)

/-- The actual local factorization gives the sum of logarithmic derivatives
away from the V1 zeros; it is not assumed as a contour input. -/
theorem logDeriv_conreyDegreeOneEta_eq_add {g g0 g1 L : ℝ} {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (hne : conreyDegreeOneV1 g g0 g1 L s ≠ 0) :
    logDeriv (conreyDegreeOneEta g g0 g1 L) s =
      logDeriv conreyH s + logDeriv (conreyDegreeOneV1 g g0 g1 L) s := by
  have heq : conreyDegreeOneEta g g0 g1 L =ᶠ[nhds s]
      (fun z => conreyH z * conreyDegreeOneV1 g g0 g1 L z) := by
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds hs, eventually_ne_nhds hs1] with z hz hz1
    exact conreyDegreeOneEta_eq_conreyH_mul_conreyDegreeOneV1_of_re_pos_of_ne_one hz hz1
  calc
    _ = logDeriv (fun z => conreyH z * conreyDegreeOneV1 g g0 g1 L z) s := by
      simp only [logDeriv_apply]
      rw [heq.deriv_eq, heq.self_of_nhds]
    _ = _ := logDeriv_mul s (conreyH_ne_zero_of_re_pos_of_ne_one hs hs1) hne
      (conreyH_analyticAt_pos hs).differentiableAt
      (analyticAt_conreyDegreeOneV1_of_re_pos_of_ne_one hs hs1).differentiableAt

private theorem continuousOn_logDeriv_comp {f : ℂ → ℂ} {z : ℝ → ℂ} {S : Set ℝ}
    (hz : ContinuousOn z S) (ha : ∀ t ∈ S, AnalyticAt ℂ f (z t))
    (hn : ∀ t ∈ S, f (z t) ≠ 0) :
    ContinuousOn (fun t => logDeriv f (z t)) S := by
  intro t ht
  exact ((ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero
    (ha t ht) (hn t ht)).continuousAt.comp_continuousWithinAt (hz t ht))

/-- Real or imaginary projection of the actual eta derivative splits along
a continuous zero-free path. Analyticity supplies both summands' integrability. -/
theorem integral_projection_logDeriv_conreyEta_eq_add
    (p : ℂ →L[ℝ] ℝ) (z : ℝ → ℂ) {g g0 g1 L a b : ℝ}
    (hz : ContinuousOn z (uIcc a b))
    (hs : ∀ t ∈ uIcc a b, 0 < (z t).re)
    (hs1 : ∀ t ∈ uIcc a b, z t ≠ 1)
    (hne : ∀ t ∈ uIcc a b, conreyDegreeOneV1 g g0 g1 L (z t) ≠ 0) :
    (∫ t in a..b, p (logDeriv (conreyDegreeOneEta g g0 g1 L) (z t))) =
      (∫ t in a..b, p (logDeriv conreyH (z t))) +
        ∫ t in a..b, p (logDeriv (conreyDegreeOneV1 g g0 g1 L) (z t)) := by
  have hH := continuousOn_logDeriv_comp hz
    (fun t ht => conreyH_analyticAt_pos (hs t ht))
    (fun t ht => conreyH_ne_zero_of_re_pos_of_ne_one (hs t ht) (hs1 t ht))
  have hV := continuousOn_logDeriv_comp hz
    (fun t ht => analyticAt_conreyDegreeOneV1_of_re_pos_of_ne_one (hs t ht) (hs1 t ht)) hne
  have hHI : IntervalIntegrable (fun t => p (logDeriv conreyH (z t))) volume a b :=
    (p.continuous.comp_continuousOn hH).intervalIntegrable
  have hVI : IntervalIntegrable
      (fun t => p (logDeriv (conreyDegreeOneV1 g g0 g1 L) (z t))) volume a b :=
    (p.continuous.comp_continuousOn hV).intervalIntegrable
  rw [← intervalIntegral.integral_add hHI hVI]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [logDeriv_conreyDegreeOneEta_eq_add (hs t ht) (hs1 t ht) (hne t ht), map_add]

/-- Quantitative H contribution along the original right edge, including
the exact length and the full integral main term. -/
theorem conreyH_rightArgument_mainTerm_bound {A U T : ℝ}
    (hA : 1 < A) (hU : 2 ≤ U) (hAU : A ≤ U) (hUT : U ≤ T) :
    |(∫ t in U..T, (logDeriv conreyH ((A : ℂ) + I * t)).re) -
      (∫ t in U..T, Real.log (t / (2 * Real.pi))) / 2| ≤ 8 * (T - U) := by
  have hs : ∀ t : ℝ, 0 < (((A : ℂ) + I * t)).re := by
    intro t
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul,
      mul_zero, sub_self, add_zero]
    linarith
  have hs1 : ∀ t : ℝ, (A : ℂ) + I * t ≠ 1 := by
    intro t he
    have hr := congrArg Complex.re he
    simp at hr
    linarith
  have hHcont := continuousOn_logDeriv_comp
    (by fun_prop : ContinuousOn (fun t : ℝ => (A : ℂ) + I * t) (uIcc U T))
    (fun t _ => conreyH_analyticAt_pos (hs t))
    (fun t _ => conreyH_ne_zero_of_re_pos_of_ne_one (hs t) (hs1 t))
  have hHI : IntervalIntegrable
      (fun t : ℝ => (logDeriv conreyH ((A : ℂ) + I * t)).re) volume U T :=
    (Complex.continuous_re.comp_continuousOn hHcont).intervalIntegrable
  have hMcont : ContinuousOn (fun t : ℝ => Real.log (t / (2 * Real.pi)) / 2) (uIcc U T) := by
    apply ContinuousOn.div_const
    apply ContinuousOn.log
    · fun_prop
    · intro t ht
      rw [uIcc_of_le hUT] at ht
      exact div_ne_zero (by linarith [ht.1]) (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hMI : IntervalIntegrable (fun t : ℝ => Real.log (t / (2 * Real.pi)) / 2)
      volume U T := hMcont.intervalIntegrable
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => (logDeriv conreyH ((A : ℂ) + I * t)).re -
      Real.log (t / (2 * Real.pi)) / 2) (a := U) (b := T) (C := 8) (by
      intro t ht
      rw [uIoc_of_le hUT] at ht
      have hraw := norm_logDeriv_conreyH_sub_half_log_t_div_two_pi_le
        (show 2 ≤ t by linarith [ht.1]) hA (show A ≤ t by linarith [ht.1])
      have hre := Complex.abs_re_le_norm
        (logDeriv conreyH ((A : ℂ) + I * t) - ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ))
      rw [Real.norm_eq_abs]
      calc
        _ ≤ ‖logDeriv conreyH ((A : ℂ) + I * t) -
            ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ)‖ := by
          simpa only [Complex.sub_re, Complex.ofReal_re] using hre
        _ ≤ 8 := hraw)
  rw [intervalIntegral.integral_sub hHI hMI] at hbound
  have hmain : (∫ t in U..T, Real.log (t / (2 * Real.pi)) / 2) =
      (∫ t in U..T, Real.log (t / (2 * Real.pi))) / 2 := by
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const]
  rw [hmain] at hbound
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hUT)] using hbound

/-- Uniform horizontal H bound in a whole unit window. -/
theorem conreyH_horizontalArgument_bound {L base t : ℝ} (hL : 40000 ≤ L)
    (hbase : conreyHorizontalRightEdge L + 1 ≤ base) (ht : t ∈ Icc base (base + 1)) :
    |∫ x in (1 / 2 : ℝ)..2 * Real.log L, (logDeriv conreyH ((x : ℂ) + I * t)).im| ≤
      (2 * Real.log L - 1 / 2) * (conreyHorizontalJensenArchimedeanConstant *
        (1 + Real.log (conreyHorizontalJensenHeightBase L base + 2))) := by
  have hab : (1 / 2 : ℝ) ≤ 2 * Real.log L := by
    linarith [two_le_log_of_forty_thousand_le hL]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ => (logDeriv conreyH ((x : ℂ) + I * t)).im)
    (a := (1 / 2 : ℝ)) (b := 2 * Real.log L)
    (C := conreyHorizontalJensenArchimedeanConstant *
      (1 + Real.log (conreyHorizontalJensenHeightBase L base + 2))) (by
      intro x hx
      rw [uIoc_of_le hab] at hx
      have hzrect : (x : ℂ) + I * t ∈ conreyHorizontalJensenRectangle 0 L base := by
          change (((x : ℂ) + I * t)).re ∈ Icc (conreyHorizontalLeftEdge 0 L)
            (conreyHorizontalRightEdge L) ∧ (((x : ℂ) + I * t)).im ∈ Icc base (base + 1)
          simpa [conreyHorizontalLeftEdge, conreyHorizontalRightEdge] using And.intro
            (show x ∈ Icc (1 / 2 : ℝ) (2 * Real.log L) from ⟨hx.1.le, hx.2⟩) ht
      have hzinner := conreyHorizontalJensenRectangle_subset_innerClosedBall 0 L base hzrect
      have hzouter := Metric.closedBall_subset_closedBall
        (conreyHorizontalJensenInnerRadius_lt_outerRadius (R := 0) (by norm_num)
          (by norm_num) hL).le hzinner
      exact (Complex.abs_im_le_norm _).trans
        (norm_logDeriv_conreyH_le_conreyHorizontalJensenOuterClosedBall hL hbase hzouter))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hbound
  simpa only [mul_comm] using hbound

/-- Auxiliary cutoff two proves both right-edge V1 nonvanishing and its
whole interval argument bound. The long mollifier is not altered. -/
theorem conreyV1_right_nonzero_and_argument_bound {L U T : ℝ}
    (hL : 40000 ≤ L) (hU : 1 ≤ U) (hUT : U ≤ T) (hT : T ≤ Real.exp L) :
    (∀ t ∈ Icc U T,
      conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L (((2 * Real.log L : ℝ) : ℂ) + I * t) ≠ 0) ∧
    |∫ t in U..T,
      (logDeriv (conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L)
        (((2 * Real.log L : ℝ) : ℂ) + I * t)).re| ≤ Real.pi := by
  have heq : conreyExplicitRightVerticalFunction 2 (1 / 2) L =
      conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L := by
    funext s
    change conreyDegreeOneV1 _ _ _ _ s * conreyMollifier 2 _ conreyExplicitP s = _
    rw [conreyMollifier_two (by norm_num [conreyExplicitP])
      (by norm_num [conreyExplicitP]), mul_one]
  constructor
  · intro t ht hzero
    have hre := three_tenths_le_conreyExplicitRightVerticalProduct_global_re
      (Y := 2) (sigma0 := (1 / 2 : ℝ)) (by norm_num) le_rfl hL
      (hU.trans ht.1) (ht.2.trans hT)
    rw [← conreyExplicitRightVerticalFunction_apply, heq, hzero] at hre
    norm_num at hre
  · simpa only [heq] using
      (abs_intervalIntegral_re_logDeriv_conreyExplicitRightVertical_le_pi
        (Y := 2) (sigma0 := (1 / 2 : ℝ)) (by norm_num) le_rfl hL hU hUT hT)

end HardyTheorem
