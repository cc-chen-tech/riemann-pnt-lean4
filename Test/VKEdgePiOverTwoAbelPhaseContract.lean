import PrimeNumberTheorem.VKEdgePiOverTwoAbelPhase

open Complex Filter MeasureTheory Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check normalizedPsiError
#check zeroResiduePhase
#check realPhaseCos
#check phaseCos
#check sharpenedPsiAbelKernel

example {beta lambda a : ℝ}
    (herror : PsiPowerErrorBound beta) (ha : 0 < a) :
    IntegrableOn
      (fun y : ℝ =>
        ((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
          Complex.exp
            (-(((beta + a : ℝ) : ℂ) + I * (lambda : ℂ)) * (y : ℂ)))
      (Set.Ioi 0) :=
  integrableOn_logarithmicPsiError_exp_of_power_error herror ha

example {rho : ℂ} {m : ℕ} (hrho0 : rho ≠ 0) :
    Complex.exp (((zeroResiduePhase rho : ℝ) : ℂ) * I) *
        (-(m : ℂ) * (‖rho‖ : ℂ) / rho) =
      (m : ℂ) :=
  exp_zeroResiduePhase_mul_residue hrho0

example {rho : ℂ} {lambda a : ℝ}
    (herror : PsiPowerErrorBound rho.re) (ha : 0 < a) :
    realAbelMean
        (fun y =>
          normalizedPsiError rho y * phaseCos rho lambda y) a =
      (Complex.exp (((zeroResiduePhase rho : ℝ) : ℂ) * I) *
          ((‖rho‖ : ℂ) *
            psiAbelCoefficient rho.re lambda a)).re :=
  realAbelMean_normalizedPsiError_mul_phaseCos herror ha

example {rho : ℂ} {phase lambda a : ℝ}
    (herror : PsiPowerErrorBound rho.re) (ha : 0 < a) :
    realAbelMean
        (fun y =>
          normalizedPsiError rho y *
            realPhaseCos phase lambda y) a =
      (Complex.exp (((phase : ℝ) : ℂ) * I) *
          ((‖rho‖ : ℂ) *
            psiAbelCoefficient rho.re lambda a)).re :=
  realAbelMean_normalizedPsiError_mul_realPhaseCos herror ha

example {rho : ℂ} {m : ℕ}
    (hrhoRe0 : 0 ≤ rho.re) (hrhoRe1 : rho.re < 1)
    (hrhoIm : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (horder : analyticOrderAt riemannZeta rho = m)
    (herror : PsiPowerErrorBound rho.re) :
    Tendsto
      (realAbelMean
        (fun y =>
          normalizedPsiError rho y *
            phaseCos rho rho.im y))
      (𝓝[>] 0) (𝓝 (m : ℝ)) :=
  tendsto_targetPhaseAbelMean_of_zeta_zero
    hrhoRe0 hrhoRe1 hrhoIm hzero horder herror

example {rho : ℂ} {lambda phase : ℝ}
    (hrhoRe0 : 0 ≤ rho.re) (hrhoRe1 : rho.re < 1)
    (hlambda : 0 < lambda)
    (hzeta : riemannZeta ((rho.re : ℂ) + I * lambda) ≠ 0)
    (herror : PsiPowerErrorBound rho.re) :
    Tendsto
      (realAbelMean
        (fun y =>
          normalizedPsiError rho y *
            realPhaseCos phase lambda y))
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_realPhaseAbelMean_of_zeta_ne_zero
    hrhoRe0 hrhoRe1 hlambda hzeta herror

example (rho : ℂ) (gamma : ℝ) (k : ℕ) (y : ℝ) :
    sharpenedPsiAbelKernel rho gamma k y =
      phaseCos rho gamma y -
        ((-1 : ℝ) ^ k) *
          (1 / (2 * ((2 * k + 1 : ℕ) : ℝ))) *
            realPhaseCos
              (((2 * k + 1 : ℕ) : ℝ) * zeroResiduePhase rho)
              (((2 * k + 1 : ℕ) : ℝ) * gamma) y :=
  sharpenedPsiAbelKernel_eq_two_phases rho gamma k y

example {rho : ℂ} {gamma : ℝ} (k : ℕ) (hgamma : 0 < gamma) :
    Tendsto
      (realAbelMean
        (fun y => |sharpenedPsiAbelKernel rho gamma k y|))
      (𝓝[>] 0)
      (𝓝 (sharpenedMissingHarmonicDenominator k)) :=
  tendsto_abs_sharpenedPsiAbelKernel hgamma

example {rho : ℂ} {m : ℕ} {k : ℕ}
    (hrhoRe0 : 0 ≤ rho.re) (hrhoRe1 : rho.re < 1)
    (hrhoIm : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (horder : analyticOrderAt riemannZeta rho = m)
    (hmissing :
      riemannZeta
        (oddHarmonicPoint rho.re rho.im k) ≠ 0)
    (herror : PsiPowerErrorBound rho.re) :
    Tendsto
      (realAbelMean
        (fun y =>
          normalizedPsiError rho y *
            sharpenedPsiAbelKernel rho rho.im k y))
      (𝓝[>] 0) (𝓝 (m : ℝ)) :=
  tendsto_sharpenedPsiAbelMean_of_missing
    hrhoRe0 hrhoRe1 hrhoIm hzero horder hmissing herror

#check strictPiOverTwoOscillationConstant

example (k : ℕ) :
    Real.pi / 2 < strictPiOverTwoOscillationConstant k :=
  pi_div_two_lt_strictPiOverTwoOscillationConstant k

example {rho : ℂ} {m : ℕ} {sigma : ℝ}
    (hrhoRe1 : rho.re < 1) (hrhoIm : 0 < rho.im)
    (hsigmaHalf : 1 / 2 < sigma)
    (hsigmaRho : sigma < rho.re)
    (hzero : riemannZeta rho = 0)
    (horder : analyticOrderAt riemannZeta rho = m)
    (hm : 1 ≤ m) :
    ∃ k : ℕ,
      riemannZeta
          (oddHarmonicPoint rho.re rho.im k) ≠ 0 ∧
      Real.pi / 2 < strictPiOverTwoOscillationConstant k ∧
      ∀ Y : ℝ, 0 ≤ Y →
        ∃ y : ℝ, Y ≤ y ∧
          (m : ℝ) * strictPiOverTwoOscillationConstant k <
            |normalizedPsiError rho y| :=
  exists_far_normalizedPsiError_gt_pi_div_two_of_zeta_zero
    hrhoRe1 hrhoIm hsigmaHalf hsigmaRho
    hzero horder hm

example {rho : ℂ} {m : ℕ} {sigma : ℝ}
    (hrhoRe1 : rho.re < 1) (hrhoIm : 0 < rho.im)
    (hsigmaHalf : 1 / 2 < sigma)
    (hsigmaRho : sigma < rho.re)
    (hzero : riemannZeta rho = 0)
    (horder : analyticOrderAt riemannZeta rho = m)
    (hm : 1 ≤ m) :
    ∃ k : ℕ,
      riemannZeta
          (oddHarmonicPoint rho.re rho.im k) ≠ 0 ∧
      Real.pi / 2 < strictPiOverTwoOscillationConstant k ∧
      ∀ X : ℝ, 1 ≤ X →
        ∃ x : ℝ, X ≤ x ∧
          (m : ℝ) * strictPiOverTwoOscillationConstant k *
              (x ^ rho.re / ‖rho‖) <
            |chebyshevPsi x - x| :=
  exists_far_psiError_gt_pi_div_two_of_zeta_zero
    hrhoRe1 hrhoIm hsigmaHalf hsigmaRho
    hzero horder hm

end VKEdgePiOverTwo
end PrimeNumberTheorem
