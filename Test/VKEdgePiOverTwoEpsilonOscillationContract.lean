import PrimeNumberTheorem.VKEdgePiOverTwoEpsilonOscillation

open Complex Filter Set

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check epsilonCenterCoefficient_ge_sixteen
#check epsilonRadiusCoefficient_pos
#check epsilonRadiusCoefficient_lt_center
#check epsilonRadius_sq_ge_sixteen_mul
#check tendsto_epsilonGaussianScale_atTop
#check eventually_exists_psiError_in_powerOnePlusEpsilonWindow_gt_strictPiOverTwo
#check exists_eventually_psiError_in_powerOnePlusEpsilonWindow_gt_strictPiOverTwo

example {ε : ℝ} (hε : 0 < ε) :
    16 ≤ epsilonCenterCoefficient ε :=
  epsilonCenterCoefficient_ge_sixteen hε

example {ε : ℝ} (hε : 0 < ε) :
    16 * (epsilonCenterCoefficient ε + epsilonRadiusCoefficient ε) ≤
      epsilonRadiusCoefficient ε ^ 2 :=
  epsilonRadius_sq_ge_sixteen_mul hε

example {ε : ℝ} (hε : 0 < ε) :
    Tendsto (epsilonGaussianScale ε) atTop atTop :=
  tendsto_epsilonGaussianScale_atTop hε

example {ε : ℝ} {rho : ℂ} {k : ℕ}
    (hε : 0 < ε)
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hmissing :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0) :
    ∀ᶠ Y : ℝ in atTop,
      ∃ x ∈ powerOnePlusEpsilonWindow ε Y,
        (analyticOrderNatAt riemannZeta rho : ℝ) *
              strictPiOverTwoOscillationConstant k *
              (x ^ rho.re / ‖rho‖) <
            |chebyshevPsi x - x| :=
  eventually_exists_psiError_in_powerOnePlusEpsilonWindow_gt_strictPiOverTwo
    hε hrhoRe0 hrhoRe1 hgamma hzero hmissing

example {ε : ℝ} {rho : ℂ} {sigma : ℝ}
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
        ∃ x ∈ powerOnePlusEpsilonWindow ε Y,
          (analyticOrderNatAt riemannZeta rho : ℝ) *
                strictPiOverTwoOscillationConstant k *
                (x ^ rho.re / ‖rho‖) <
              |chebyshevPsi x - x| :=
  exists_eventually_psiError_in_powerOnePlusEpsilonWindow_gt_strictPiOverTwo
    hε hgamma hzero hσ hσrho hrhoRe1

end PrimeNumberTheorem.VKEdgePiOverTwo
