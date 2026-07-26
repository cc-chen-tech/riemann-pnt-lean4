import PrimeNumberTheorem.VKEdgePiOverTwoCenteredMissingHarmonicContour

open Complex Filter MeasureTheory Polynomial Set Topology

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check centeredNormalizedWindowValues
#check centeredNormalizedWindowSup
#check CenteredLocalizedContourData
#check CenteredLocalizedContourData.radius_nonneg
#check CenteredLocalizedContourData.signal_tendsto
#check CenteredLocalizedContourData.coefficient_tendsto
#check CenteredLocalizedContourData.remainder_tendsto
#check CenteredLocalizedContourData.eventually_coefficient_pos
#check CenteredLocalizedContourData.eventually_window_bddAbove
#check CenteredLocalizedContourData.eventually_upper_bound
#check CenteredLocalizedContourData.eventually_exists_normalizedPsiError_gt
#check centeredSharpenedTargetFilter
#check centeredSharpenedMissingFilter
#check centeredSharpenedProjectedPsiKernel
#check centeredSharpenedProjectedPsiCoefficient
#check tendsto_centeredSharpenedProjectedPsiCoefficient
#check sharpenedCenteredLocalizedContourData
#check eventually_exists_normalizedPsiError_in_centeredWindow_gt

example (q d : ℝ) (rho : ℂ) (m : ℝ) :
    centeredNormalizedWindowValues q d rho m =
      (fun y => |normalizedPsiError rho y|) ''
        localizedGaussianLogWindow q d m := by
  rfl

example (q d : ℝ) (rho : ℂ) (m : ℝ) :
    centeredNormalizedWindowSup q d rho m =
      sSup (centeredNormalizedWindowValues q d rho m) := by
  rfl

example {q d : ℝ} {rho : ℂ} {multiplicity mean C : ℝ}
    (data : CenteredLocalizedContourData q d rho multiplicity mean)
    (hmultiplicity : 0 < multiplicity) (hmean : 0 < mean)
    (hC : C < multiplicity / mean) :
    ∀ᶠ m : ℝ in atTop,
      ∃ y ∈ localizedGaussianLogWindow q d m,
        C < |normalizedPsiError rho y| :=
  data.eventually_exists_normalizedPsiError_gt
    hmultiplicity hmean hC

example (q : ℝ) (rho : ℂ) :
    centeredSharpenedTargetFilter q rho =
      localizedNearZeroFilter rho (centeredPoleRadius q) := by
  rfl

example (q : ℝ) (rho : ℂ) (k : ℕ) :
    centeredSharpenedMissingFilter q rho k =
      localizedNearZeroFilter
        (missingHarmonicContourCenter rho k)
        (centeredPoleRadius q) := by
  rfl

example (q : ℝ) (rho : ℂ) (k : ℕ) (m y : ℝ) :
    centeredSharpenedProjectedPsiKernel q rho k m y =
      projectedPsiKernelAtCenter q
          (centeredSharpenedTargetFilter q rho) rho m y +
        relativeProjectedPsiKernelAtCenter q
          (centeredSharpenedMissingFilter q rho k) rho
          (missingHarmonicContourCenter rho k)
          (missingHarmonicContourCoefficient rho k) m y := by
  rfl

example (q : ℝ) (rho : ℂ) (k : ℕ) (m : ℝ) :
    centeredSharpenedProjectedPsiCoefficient q rho k m =
      ∫ y : ℝ,
        |centeredSharpenedProjectedPsiKernel q rho k m y| := by
  rfl

example {q : ℝ} {rho : ℂ} {k : ℕ}
    (hrho0 : rho ≠ 0) (hgamma : 0 < rho.im) :
    Tendsto
      (centeredSharpenedProjectedPsiCoefficient q rho k)
      atTop
      (𝓝 (2 * sharpenedMissingHarmonicDenominator k)) :=
  tendsto_centeredSharpenedProjectedPsiCoefficient
    q hrho0 hgamma

noncomputable example {q d : ℝ} {rho : ℂ} {k : ℕ}
    (hq : 16 ≤ q) (hd : 0 < d) (hdq : d < q)
    (hmargin : 16 * (q + d) ≤ d ^ 2)
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hmissing :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0) :
    CenteredLocalizedContourData q d rho
      (analyticOrderNatAt riemannZeta rho : ℝ)
      (sharpenedMissingHarmonicDenominator k) :=
  sharpenedCenteredLocalizedContourData
    q d hq hd hdq hmargin
      hrhoRe0 hrhoRe1 hgamma hzero hmissing

example {q d : ℝ} {rho : ℂ} {k : ℕ}
    (hq : 16 ≤ q) (hd : 0 < d) (hdq : d < q)
    (hmargin : 16 * (q + d) ≤ d ^ 2)
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hmissing :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0)
    {C : ℝ}
    (hC :
      C <
        (analyticOrderNatAt riemannZeta rho : ℝ) /
          sharpenedMissingHarmonicDenominator k) :
    ∀ᶠ m : ℝ in atTop,
      ∃ y ∈ localizedGaussianLogWindow q d m,
        C < |normalizedPsiError rho y| :=
  eventually_exists_normalizedPsiError_in_centeredWindow_gt
    hq hd hdq hmargin hrhoRe0 hrhoRe1 hgamma hzero hmissing hC

end PrimeNumberTheorem.VKEdgePiOverTwo
