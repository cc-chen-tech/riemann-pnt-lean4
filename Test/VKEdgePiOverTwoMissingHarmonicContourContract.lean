import PrimeNumberTheorem.VKEdgePiOverTwoMissingHarmonicContour

open Complex Filter Topology

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check missingHarmonicContourCoefficient
#check sharpenedProjectedPsiKernel
#check sharpenedProjectedPsiCoefficient
#check tendsto_sharpenedProjectedPsiCoefficient
#check sharpenedConcreteLocalizedContourData
#check eventually_exists_psiError_in_powerSevenWindow_gt_strictPiOverTwo
#check exists_eventually_psiError_in_powerSevenWindow_gt_strictPiOverTwo

example {rho : ℂ} {k : ℕ}
    (hrho0 : rho ≠ 0) (hgamma : 0 < rho.im) :
    Tendsto
      (sharpenedProjectedPsiCoefficient rho k)
      atTop
      (𝓝 (2 * sharpenedMissingHarmonicDenominator k)) :=
  tendsto_sharpenedProjectedPsiCoefficient hrho0 hgamma

example {rho : ℂ} {k : ℕ}
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hmissing :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0) :
    ∀ᶠ Y : ℝ in atTop,
      ∃ x ∈ powerSevenWindow Y,
        (analyticOrderNatAt riemannZeta rho : ℝ) *
              strictPiOverTwoOscillationConstant k *
              (x ^ rho.re / ‖rho‖) <
          |chebyshevPsi x - x| :=
  eventually_exists_psiError_in_powerSevenWindow_gt_strictPiOverTwo
    hrhoRe0 hrhoRe1 hgamma hzero hmissing

end PrimeNumberTheorem.VKEdgePiOverTwo
