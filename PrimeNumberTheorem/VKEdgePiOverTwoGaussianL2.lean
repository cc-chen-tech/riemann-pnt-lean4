import MathlibAux.WeightedCauchySchwarz
import PrimeNumberTheorem.VKEdgePiOverTwoCenteredMissingHarmonicContour

open Complex Filter MeasureTheory Polynomial Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

private theorem measurable_normalizedPsiError_l2 (rho : ℂ) :
    Measurable (normalizedPsiError rho) := by
  have hpsi : Measurable chebyshevPsi := by
    simpa only [chebyshevPsi_eq_mathlib] using
      Chebyshev.psi_mono.measurable
  unfold normalizedPsiError
  fun_prop

/--
The centered contour first moment forces a weighted second moment. The
limiting lower endpoint is the exact Cauchy--Schwarz ratio
`2 * multiplicity^2 / mean`.
-/
theorem CenteredLocalizedContourData.eventually_secondMoment_gt
    {q d : ℝ} {rho : ℂ} {multiplicity mean C2 : ℝ}
    (data : CenteredLocalizedContourData q d rho multiplicity mean)
    (hmultiplicity : 0 < multiplicity) (hmean : 0 < mean)
    (hC2 : C2 < 2 * multiplicity ^ 2 / mean) :
    ∀ᶠ m : ℝ in atTop,
      C2 <
        centeredNormalizedWindowSecondMoment
          q d rho data.kernel m := by
  have hlimitDenom : (2 * mean : ℝ) ≠ 0 := by positivity
  have hratio :
      Tendsto
        (fun m =>
          (data.signal m - data.remainder m) ^ 2 /
            data.coefficient m)
        atTop
        (𝓝 (2 * multiplicity ^ 2 / mean)) := by
    have h :=
      ((data.signal_tendsto.sub data.remainder_tendsto).pow 2).div
        data.coefficient_tendsto hlimitDenom
    convert h using 1
    field_simp
    ring
  have hratioLower :
      ∀ᶠ m : ℝ in atTop,
        C2 <
          (data.signal m - data.remainder m) ^ 2 /
            data.coefficient m :=
    (tendsto_order.1 hratio).1 C2 hC2
  have hsignalPos :
      ∀ᶠ m : ℝ in atTop,
        0 < data.signal m - data.remainder m := by
    have hsignalSub :=
      data.signal_tendsto.sub data.remainder_tendsto
    have hlimitPos : 0 < 2 * multiplicity - 0 := by
      linarith
    exact
      (tendsto_order.1 hsignalSub).1 0
        hlimitPos
  filter_upwards [
    data.eventually_coefficient_pos,
    data.eventually_kernel_measurable,
    data.eventually_kernel_integrable,
    data.eventually_second_moment_integrable,
    data.eventually_first_moment_bound,
    hratioLower,
    hsignalPos] with
      m hcoefficient hkMeas hkInt hsecondInt hfirstBound hratioM hsignalM
  let window : Set ℝ := localizedGaussianLogWindow q d m
  let weight : ℝ → ℝ := fun y => |data.kernel m y|
  let firstMoment : ℝ :=
    centeredNormalizedWindowFirstMoment q d rho data.kernel m
  let secondMoment : ℝ :=
    centeredNormalizedWindowSecondMoment q d rho data.kernel m
  have hweightMeas : Measurable weight := hkMeas.norm
  have hweightInt : IntegrableOn weight window :=
    hkInt.abs.integrableOn
  have hcs :
      firstMoment ^ 2 ≤
        secondMoment * ∫ y : ℝ in window, weight y := by
    have h :=
      MathlibAux.sq_setIntegral_abs_mul_weight_le
        (μ := volume) (s := window)
        (f := normalizedPsiError rho) (w := weight)
        measurableSet_Icc
        (measurable_normalizedPsiError_l2 rho)
        hweightMeas
        (fun _ _ => abs_nonneg _)
        (by simpa [secondMoment, weight, window] using hsecondInt)
        hweightInt
    simpa [firstMoment, secondMoment, weight, window,
      centeredNormalizedWindowFirstMoment,
      centeredNormalizedWindowSecondMoment] using h
  have hsecondNonneg : 0 ≤ secondMoment := by
    dsimp [secondMoment]
    unfold centeredNormalizedWindowSecondMoment
    exact integral_nonneg fun y =>
      mul_nonneg (sq_nonneg _) (abs_nonneg _)
  have hmass :
      (∫ y : ℝ in window, weight y) ≤ data.coefficient m := by
    calc
      (∫ y : ℝ in window, weight y) ≤
          ∫ y : ℝ, weight y :=
        setIntegral_le_integral hkInt.abs
          (Filter.Eventually.of_forall fun y => abs_nonneg _)
      _ = data.coefficient m := by
        rw [data.coefficient_eq_kernel_mass m]
  have hfirstNonneg : 0 ≤ firstMoment := by
    dsimp [firstMoment]
    unfold centeredNormalizedWindowFirstMoment
    exact integral_nonneg fun y =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsignalLeFirst :
      data.signal m - data.remainder m ≤ firstMoment := by
    dsimp [firstMoment]
    linarith
  have hsignalSqLe :
      (data.signal m - data.remainder m) ^ 2 ≤ firstMoment ^ 2 := by
    simpa [pow_two] using
      mul_self_le_mul_self hsignalM.le hsignalLeFirst
  have hratioLe :
      (data.signal m - data.remainder m) ^ 2 /
          data.coefficient m ≤
        secondMoment := by
    apply (div_le_iff₀ hcoefficient).2
    calc
      (data.signal m - data.remainder m) ^ 2 ≤
          firstMoment ^ 2 := hsignalSqLe
      _ ≤ secondMoment * ∫ y : ℝ in window, weight y := hcs
      _ ≤ secondMoment * data.coefficient m :=
        mul_le_mul_of_nonneg_left hmass hsecondNonneg
  exact hratioM.trans_le hratioLe

/--
True zeta contour specialization of the Gaussian weighted second-moment
lower bound, retaining analytic multiplicity.
-/
theorem eventually_centeredSharpenedNormalizedPsiError_secondMoment_gt
    {q d : ℝ} {rho : ℂ} {k : ℕ}
    (hq : 16 ≤ q) (hd : 0 < d) (hdq : d < q)
    (hmargin : 16 * (q + d) ≤ d ^ 2)
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hmissing :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0)
    {C2 : ℝ}
    (hC2 :
      C2 <
        2 * (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 /
          sharpenedMissingHarmonicDenominator k) :
    ∀ᶠ m : ℝ in atTop,
      C2 <
        centeredNormalizedWindowSecondMoment q d rho
          (centeredSharpenedProjectedPsiKernel q rho k) m := by
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
  exact
    (sharpenedCenteredLocalizedContourData
      q d hq hd hdq hmargin
        hrhoRe0 hrhoRe1 hgamma hzero hmissing
      |>.eventually_secondMoment_gt
        hmultiplicity (sharpenedMissingHarmonicDenominator_pos k) hC2)

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
