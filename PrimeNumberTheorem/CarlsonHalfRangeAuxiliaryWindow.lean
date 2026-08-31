import PrimeNumberTheorem.CarlsonHalfRangeInteriorPower
import PrimeNumberTheorem.CarlsonTwoThirdsHalfRangeExponent

/-! The fixed left window for Littlewood, with a uniform energy bound on
every subinterval of the Gaussian-covered height interval.  The zero-count
and contour assertions are deliberately not part of this module. -/

open Complex Filter MeasureTheory Set
open scoped Interval

namespace PrimeNumberTheorem.CarlsonZeroDensity

noncomputable def halfRangeAuxiliaryLeft : ℝ := 2 / 3 - 1 / 10000
noncomputable def halfRangeAuxiliaryRight : ℝ := 2 / 3 - 1 / 20000

theorem halfRangeAuxiliary_exact_slack : halfRangeTargetExponent -
    (1 - (12 / 5 : ℝ) * ((halfRangeAuxiliaryLeft - 1 / 2) / (4 - 1 / 2))) =
      1909 / 3150000 := by
  norm_num [halfRangeTargetExponent, halfRangeAuxiliaryLeft]

/-- Every allowed line has a strictly positive Littlewood weight and a power
strictly below the first target exponent. -/
theorem halfRangeAuxiliary_bounds {x : ℝ}
    (hx : x ∈ Icc halfRangeAuxiliaryLeft halfRangeAuxiliaryRight) :
    x ∈ Icc (1 / 2 : ℝ) (2 / 3) ∧ (1 / 20000 : ℝ) ≤ 2 / 3 - x ∧
      1 - (12 / 5 : ℝ) * ((x - 1 / 2) / (4 - 1 / 2)) < halfRangeTargetExponent := by
  rcases hx with ⟨hL, hR⟩
  norm_num [halfRangeAuxiliaryLeft] at hL
  norm_num [halfRangeAuxiliaryRight] at hR
  norm_num [halfRangeTargetExponent]
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

private theorem continuous_error_energy {x : ℝ}
    (hx : x ∈ Icc (1 / 2 : ℝ) (2 / 3)) (Y0 Y1 : ℕ) :
    Continuous fun t : ℝ =>
      ‖twoScaleMollifiedZetaError Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖ ^ 2 := by
  have herror : Continuous fun t : ℝ =>
      twoScaleMollifiedZetaError Y0 Y1 ((x : ℂ) + I * (t : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hs1 : (x : ℂ) + I * (t : ℂ) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
        sub_self, add_zero, Complex.one_re] at hre
      linarith [hx.2]
    have hpoint : ContinuousAt (fun u : ℝ => (x : ℂ) + I * (u : ℂ)) t := by fun_prop
    simpa only [Function.comp_def] using
      (analyticAt_twoScaleMollifiedZetaError_of_ne_one Y0 Y1 hs1).continuousAt.comp
        (f := fun u : ℝ => (x : ℂ) + I * (u : ℂ)) hpoint
  exact herror.norm.pow 2

/-- The threshold and constant precede the line and both height endpoints.
Genuine interval integrability is supplied, not assumed. -/
theorem exists_eventually_halfRange_auxiliary_subinterval_moment_le :
    ∃ K > (0 : ℝ), ∀ᶠ V : ℝ in atTop,
      ∀ x ∈ Icc halfRangeAuxiliaryLeft halfRangeAuxiliaryRight,
      ∀ u v : ℝ, 2 * V ≤ u → v ≤ 5 * V / 2 → u ≤ v →
        IntervalIntegrable (fun t : ℝ =>
          ‖twoScaleMollifiedZetaError (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
            ((x : ℂ) + I * (t : ℂ))‖ ^ 2) volume u v ∧
        (∫ t in u..v,
          ‖twoScaleMollifiedZetaError (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
            ((x : ℂ) + I * (t : ℂ))‖ ^ 2) ≤
          K * V ^ halfRangeTargetExponent * (1 + Real.log V) ^ 6 := by
  obtain ⟨K, hK, hmoment⟩ := exists_eventually_halfRange_leftStrip_moment_le_powerLog
  refine ⟨K, hK, ?_⟩
  filter_upwards [hmoment, eventually_ge_atTop (1 : ℝ)] with V hmoment hV
  intro x hx u v hu hv huv
  obtain ⟨hxStrip, hxWeight, hxPower⟩ := halfRangeAuxiliary_bounds hx
  let g : ℝ → ℝ := fun t =>
    ‖twoScaleMollifiedZetaError (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
      ((x : ℂ) + I * (t : ℂ))‖ ^ 2
  have hg : Continuous g := continuous_error_energy hxStrip _ _
  refine ⟨hg.intervalIntegrable u v, ?_⟩
  have hsubset : Icc u v ⊆ Icc (2 * V) (5 * V / 2) := by
    intro t ht
    exact ⟨hu.trans ht.1, ht.2.trans hv⟩
  have hmono : (∫ t in Icc u v, g t) ≤ ∫ t in Icc (2 * V) (5 * V / 2), g t :=
    setIntegral_mono_set (hg.continuousOn.integrableOn_compact isCompact_Icc)
      (Eventually.of_forall fun t => sq_nonneg _) (Eventually.of_forall hsubset)
  have hfull := hmoment x hxStrip
  rw [integral_indicator measurableSet_Icc] at hfull
  calc
    _ = ∫ t in Icc u v, g t := by
      rw [intervalIntegral.integral_of_le huv, integral_Icc_eq_integral_Ioc]
    _ ≤ ∫ t in Icc (2 * V) (5 * V / 2), g t := hmono
    _ ≤ K * V ^ (1 - (12 / 5 : ℝ) * ((x - 1 / 2) / (4 - 1 / 2))) *
        (1 + Real.log V) ^ 6 := hfull
    _ ≤ K * V ^ halfRangeTargetExponent * (1 + Real.log V) ^ 6 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hV hxPower.le) hK.le) (by positivity)

end PrimeNumberTheorem.CarlsonZeroDensity
