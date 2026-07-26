import PrimeNumberTheorem.VKEdgePiOverTwoEpsilonOscillation
import PrimeNumberTheorem.VKEdgePiOverTwoGaussianL2

open Complex Filter MeasureTheory Polynomial Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

private theorem measurable_normalizedPsiError_measure (rho : ℂ) :
    Measurable (normalizedPsiError rho) := by
  have hpsi : Measurable chebyshevPsi := by
    simpa only [chebyshevPsi_eq_mathlib] using
      Chebyshev.psi_mono.measurable
  unfold normalizedPsiError
  fun_prop

/--
Every threshold below the limiting first-moment ratio forces the weighted
second moment to exceed the threshold squared times the full kernel mass.
-/
theorem
    CenteredLocalizedContourData.eventually_secondMoment_gt_sq_mul_coefficient
    {q d : ℝ} {rho : ℂ} {multiplicity mean C : ℝ}
    (data : CenteredLocalizedContourData q d rho multiplicity mean)
    (hmultiplicity : 0 < multiplicity) (hmean : 0 < mean)
    (hC0 : 0 ≤ C) (hC : C < multiplicity / mean) :
    ∀ᶠ m : ℝ in atTop,
      C ^ 2 * data.coefficient m <
        centeredNormalizedWindowSecondMoment
          q d rho data.kernel m := by
  have hCmean : C * mean < multiplicity :=
    (lt_div_iff₀ hmean).1 hC
  have hCmean0 : 0 ≤ C * mean :=
    mul_nonneg hC0 hmean.le
  have hsq :
      (C * mean) ^ 2 < multiplicity ^ 2 := by
    nlinarith
  have hlimits :
      2 * C ^ 2 * mean <
        2 * multiplicity ^ 2 / mean := by
    apply (lt_div_iff₀ hmean).2
    nlinarith
  let midpoint : ℝ :=
    (2 * C ^ 2 * mean +
      2 * multiplicity ^ 2 / mean) / 2
  have hmidLower : 2 * C ^ 2 * mean < midpoint := by
    dsimp [midpoint]
    linarith
  have hmidUpper :
      midpoint < 2 * multiplicity ^ 2 / mean := by
    dsimp [midpoint]
    linarith
  have hsecond :=
    data.eventually_secondMoment_gt
      hmultiplicity hmean hmidUpper
  have hscaled :
      Tendsto
        (fun m => C ^ 2 * data.coefficient m)
        atTop (𝓝 (2 * C ^ 2 * mean)) := by
    have hconst :
        Tendsto (fun _m : ℝ => C ^ 2) atTop (𝓝 (C ^ 2)) :=
      tendsto_const_nhds
    have h := hconst.mul data.coefficient_tendsto
    convert h using 1 <;> ring
  have hscaledUpper :
      ∀ᶠ m : ℝ in atTop,
        C ^ 2 * data.coefficient m < midpoint :=
    (tendsto_order.1 hscaled).2 midpoint hmidLower
  filter_upwards [hsecond, hscaledUpper] with m hsecondM hscaledM
  exact hscaledM.trans hsecondM

/--
The strict weighted second-moment inequality forces a positive-measure set of
large normalized PNT errors in every sufficiently late centered log window.
-/
theorem CenteredLocalizedContourData.eventually_positive_measure_error_gt
    {q d : ℝ} {rho : ℂ} {multiplicity mean C : ℝ}
    (data : CenteredLocalizedContourData q d rho multiplicity mean)
    (hmultiplicity : 0 < multiplicity) (hmean : 0 < mean)
    (hC0 : 0 ≤ C) (hC : C < multiplicity / mean) :
    ∀ᶠ m : ℝ in atTop,
      0 <
        volume.real
          {y ∈ localizedGaussianLogWindow q d m |
            C < |normalizedPsiError rho y|} := by
  have hmoment :=
    data.eventually_secondMoment_gt_sq_mul_coefficient
      hmultiplicity hmean hC0 hC
  filter_upwards [
    hmoment,
    data.eventually_kernel_integrable,
    data.eventually_second_moment_integrable] with
      m hmomentM hkInt hsecondInt
  let window : Set ℝ := localizedGaussianLogWindow q d m
  let good : Set ℝ :=
    {y ∈ window | C < |normalizedPsiError rho y|}
  have hwindowMeasurable : MeasurableSet window := measurableSet_Icc
  have hgoodMeasurable : MeasurableSet good := by
    exact hwindowMeasurable.inter
      ((measurable_normalizedPsiError_measure rho).norm measurableSet_Ioi)
  have hgoodSubset : good ⊆ window := fun _ hy => hy.1
  have hgoodFinite : volume good ≠ ⊤ :=
    measure_ne_top_of_subset hgoodSubset isCompact_Icc.measure_lt_top.ne
  by_contra hpositive
  have hrealZero : volume.real good = 0 :=
    le_antisymm (le_of_not_gt hpositive) measureReal_nonneg
  have hmeasureZero : volume good = 0 :=
    (measureReal_eq_zero_iff hgoodFinite).1 hrealZero
  have haenotGood : ∀ᵐ y : ℝ, y ∉ good :=
    measure_eq_zero_iff_ae_notMem.mp hmeasureZero
  have hmajorInt :
      IntegrableOn
        (fun y => C ^ 2 * |data.kernel m y|)
        window :=
    (hkInt.abs.const_mul (C ^ 2)).integrableOn
  have hmomentLe :
      centeredNormalizedWindowSecondMoment q d rho data.kernel m ≤
        C ^ 2 * data.coefficient m := by
    have hpointwise :
        ∀ᵐ y ∂(volume.restrict window),
          normalizedPsiError rho y ^ 2 * |data.kernel m y| ≤
            C ^ 2 * |data.kernel m y| := by
      filter_upwards [
        ae_restrict_mem hwindowMeasurable,
        ae_restrict_of_ae haenotGood] with y hyWindow hyNotGood
      have habsLe : |normalizedPsiError rho y| ≤ C := by
        exact le_of_not_gt fun hlarge =>
          hyNotGood ⟨hyWindow, hlarge⟩
      have hsqLe :
          normalizedPsiError rho y ^ 2 ≤ C ^ 2 := by
        nlinarith [sq_abs (normalizedPsiError rho y),
          abs_nonneg (normalizedPsiError rho y)]
      exact mul_le_mul_of_nonneg_right hsqLe (abs_nonneg _)
    calc
      centeredNormalizedWindowSecondMoment q d rho data.kernel m ≤
          ∫ y : ℝ in window, C ^ 2 * |data.kernel m y| := by
        unfold centeredNormalizedWindowSecondMoment
        exact integral_mono_ae hsecondInt hmajorInt hpointwise
      _ = C ^ 2 * ∫ y : ℝ in window, |data.kernel m y| := by
        rw [integral_const_mul]
      _ ≤ C ^ 2 * ∫ y : ℝ, |data.kernel m y| :=
        mul_le_mul_of_nonneg_left
          (setIntegral_le_integral hkInt.abs
            (Filter.Eventually.of_forall fun y => abs_nonneg _))
          (sq_nonneg C)
      _ = C ^ 2 * data.coefficient m := by
        rw [data.coefficient_eq_kernel_mass m]
  exact (not_lt_of_ge hmomentLe) hmomentM

/--
A fixed missing odd harmonic gives positive logarithmic measure above the
strict `pi / 2` threshold in every sufficiently late centered window.
-/
theorem
    eventually_positive_measure_normalizedPsiError_gt_strictPiOverTwo
    {q d : ℝ} {rho : ℂ} {k : ℕ}
    (hq : 16 ≤ q) (hd : 0 < d) (hdq : d < q)
    (hmargin : 16 * (q + d) ≤ d ^ 2)
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hmissing :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0) :
    ∀ᶠ m : ℝ in atTop,
      0 <
        volume.real
          {y ∈ localizedGaussianLogWindow q d m |
            (analyticOrderNatAt riemannZeta rho : ℝ) *
                strictPiOverTwoOscillationConstant k <
              |normalizedPsiError rho y|} := by
  have hrho1 : rho ≠ 1 := by
    intro hrho
    have hre := congrArg Complex.re hrho
    norm_num at hre
    linarith
  have hmultiplicity :
      0 < (analyticOrderNatAt riemannZeta rho : ℝ) := by
    exact_mod_cast
      ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
        hrho1 hzero
  have hconstantPos :
      0 ≤
        (analyticOrderNatAt riemannZeta rho : ℝ) *
          strictPiOverTwoOscillationConstant k := by
    exact mul_nonneg hmultiplicity.le
      (le_trans (by positivity : 0 ≤ Real.pi / 2)
        (pi_div_two_lt_strictPiOverTwoOscillationConstant k).le)
  have hconstant :
      (analyticOrderNatAt riemannZeta rho : ℝ) *
          strictPiOverTwoOscillationConstant k <
        (analyticOrderNatAt riemannZeta rho : ℝ) /
          sharpenedMissingHarmonicDenominator k := by
    rw [show
        (analyticOrderNatAt riemannZeta rho : ℝ) /
              sharpenedMissingHarmonicDenominator k =
            (analyticOrderNatAt riemannZeta rho : ℝ) *
              sharpenedMissingHarmonicLowerBound k by
      unfold sharpenedMissingHarmonicLowerBound
      ring]
    exact mul_lt_mul_of_pos_left
      (strictPiOverTwoOscillationConstant_lt_lowerBound k)
      hmultiplicity
  exact
    (sharpenedCenteredLocalizedContourData
      q d hq hd hdq hmargin
        hrhoRe0 hrhoRe1 hgamma hzero hmissing
      |>.eventually_positive_measure_error_gt
        hmultiplicity (sharpenedMissingHarmonicDenominator_pos k)
        hconstantPos hconstant)

/--
Carlson selects the missing odd harmonic. For every fixed positive epsilon,
the strict `pi / 2` oscillation set has positive logarithmic measure in each
sufficiently late interval `[log Y, (1 + epsilon) * log Y]`.
-/
theorem
    exists_eventually_positive_measure_in_epsilonLogWindow_gt_strictPiOverTwo
    {ε : ℝ} {rho : ℂ} {sigma : ℝ}
    (hε : 0 < ε)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hσ : 1 / 2 < sigma)
    (hσrho : sigma < rho.re)
    (hrhoRe1 : rho.re < 1) :
    ∃ k : ℕ,
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
      Real.pi / 2 < strictPiOverTwoOscillationConstant k ∧
      ∀ᶠ Y : ℝ in atTop,
        0 <
          volume.real
            {y ∈ Set.Icc (Real.log Y) ((1 + ε) * Real.log Y) |
              (analyticOrderNatAt riemannZeta rho : ℝ) *
                  strictPiOverTwoOscillationConstant k <
                |normalizedPsiError rho y|} := by
  have hrhoRe0 : 0 < rho.re := by linarith
  rcases
      exists_missing_oddHarmonic_with_strict_gap_of_carlson
        hrhoRe1 hgamma hσ hσrho with
    ⟨k, hmissing, _hOldGap⟩
  have hmissing' :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 := by
    simpa [missingHarmonicContourCenter] using hmissing
  have hlocal :=
    eventually_positive_measure_normalizedPsiError_gt_strictPiOverTwo
      (epsilonCenterCoefficient_ge_sixteen hε)
      (epsilonRadiusCoefficient_pos hε)
      (epsilonRadiusCoefficient_lt_center hε)
      (epsilonRadius_sq_ge_sixteen_mul hε)
      hrhoRe0 hrhoRe1 hgamma hzero hmissing'
  have hscaled :=
    (tendsto_epsilonGaussianScale_atTop hε).eventually hlocal
  refine
    ⟨k, hmissing',
      pi_div_two_lt_strictPiOverTwoOscillationConstant k, ?_⟩
  filter_upwards [hscaled] with Y hY
  simpa only [localizedGaussianLogWindow_epsilonGaussianScale hε Y] using hY

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
