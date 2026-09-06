import HardyTheorem.SelbergFourierMellinAlgebra

open Complex

namespace HardyTheorem

example {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi) :
    0 < selbergGammaRayAngle delta ∧
      selbergGammaRayAngle delta < Real.pi / 2 :=
  selbergGammaRayAngle_mem hdelta0 hdeltaPi

example (delta : ℝ) :
    selbergGammaRayAngle delta / 2 - selbergFourierAngle delta =
      delta / 4 :=
  selbergGammaRayAngle_half_sub_fourierAngle delta

example {delta : ℝ} (hdelta0 : 0 < delta) :
    0 < selbergGammaRayAngle delta / 2 - selbergFourierAngle delta :=
  selbergGammaFourierDecayMargin_pos hdelta0

example {delta sigma t : ℝ}
    (hdelta0 : 0 < delta) (hdeltaPi : delta < Real.pi / 2)
    (hsigma : 0 < sigma) (ht : 0 ≤ t) :
    ‖Complex.Gamma (((sigma : ℂ) + I * t) / 2)‖ *
        Real.exp (selbergFourierAngle delta * t) ≤
      Real.Gamma (sigma / 2) *
        (Real.cos (selbergGammaRayAngle delta)) ^ (-sigma / 2) *
        Real.exp (-(delta / 4) * t) :=
  selbergGammaHalf_mul_fourierTilt_le
    hdelta0 hdeltaPi hsigma ht

example {delta sigma t : ℝ}
    (hdelta0 : 0 < delta) (hdeltaPi : delta < Real.pi / 2)
    (hsigma : 0 < sigma) :
    ‖Complex.Gamma (((sigma : ℂ) + I * t) / 2)‖ *
        Real.exp (selbergFourierAngle delta * t) ≤
      Real.Gamma (sigma / 2) *
        (Real.cos (selbergGammaRayAngle delta)) ^ (-sigma / 2) *
        Real.exp (-(delta / 4) * |t|) :=
  selbergGammaHalf_mul_fourierTilt_le_abs
    hdelta0 hdeltaPi hsigma

example {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y t : ℝ) :
    selbergFourierZ delta y ^ (I * t) =
      (Real.exp (selbergFourierAngle delta * t) : ℂ) *
        Complex.exp (-I * (y * t)) :=
  selbergFourierZ_cpow_I hdelta0 hdeltaPi y t

example {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y sigma t : ℝ) :
    ‖selbergFourierZ delta y ^ ((sigma : ℂ) + I * t)‖ =
      Real.exp (-y * sigma + selbergFourierAngle delta * t) :=
  norm_selbergFourierZ_cpow hdelta0 hdeltaPi y sigma t

example (delta y : ℝ) :
    (selbergFourierZ delta y)⁻¹ ^ (2 : ℕ) =
      (Real.exp (2 * y) : ℂ) *
        ((Real.sin delta : ℂ) + I * Real.cos delta) :=
  selbergFourierZ_inv_sq delta y

example {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) :
    0 < ((selbergFourierZ delta y)⁻¹ ^ (2 : ℕ)).re :=
  selbergFourierZ_inv_sq_re_pos hdelta0 hdeltaPi y

example {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) :
    0 < ((selbergFourierZ delta y)⁻¹ ^ (2 : ℕ)).im :=
  selbergFourierZ_inv_sq_im_pos hdelta0 hdeltaPi y

example {A : ℂ} (hA : 0 < A.re) :
    Summable (fun n : ℕ => Complex.exp (-A * (n : ℂ) ^ 2)) :=
  summable_cexp_neg_mul_nat_sq hA

example {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ)
    {μ ν : ℕ} (hμ : 0 < μ) (hν : 0 < ν) :
    0 < (selbergGaussianCoefficient delta y μ ν).re :=
  selbergGaussianCoefficient_re_pos hdelta0 hdeltaPi hμ hν y

example (delta y : ℝ) (μ ν : ℕ) :
    selbergGaussianCoefficient delta y μ ν =
      (Real.pi * ((μ : ℝ) / (ν : ℝ)) ^ 2 * Real.exp (2 * y) : ℝ) *
        Complex.exp (((Real.pi / 2 - delta : ℝ) : ℂ) * I) :=
  selbergGaussianCoefficient_polar delta y μ ν

example {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ)
    {μ ν : ℕ} (hμ : 0 < μ) (hν : 0 < ν) :
    Summable (selbergGaussianThetaTerm delta y μ ν) :=
  summable_selbergGaussianThetaTerm hdelta0 hdeltaPi hμ hν y

example (delta y : ℝ) (μ ν n : ℕ) :
    selbergGaussianThetaTerm delta y μ ν n =
      Complex.exp
        (-((Real.pi * (((n : ℝ) * μ) / ν) ^ 2 : ℝ) : ℂ) *
          (selbergFourierZ delta y)⁻¹ ^ (2 : ℕ)) :=
  selbergGaussianThetaTerm_eq delta y μ ν n

example {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ)
    {μ ν : ℕ} (hμ : 0 < μ) (hν : 0 < ν) :
    Summable (fun n : ℕ =>
      selbergGaussianThetaTerm delta y μ ν (n + 1)) :=
  summable_selbergGaussianThetaTerm_add_one
    hdelta0 hdeltaPi hμ hν y

example {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ)
    {μ ν : ℕ} (hμ : 0 < μ) (hν : 0 < ν) :
    HasSum
      (fun n : ℕ => selbergGaussianThetaTerm delta y μ ν (n + 1))
      (selbergGaussianThetaSum delta y μ ν) :=
  hasSum_selbergGaussianThetaSum hdelta0 hdeltaPi hμ hν y

#print axioms selbergFourierZ_cpow_I
#print axioms selbergFourierZ_inv_sq
#print axioms selbergFourierZ_inv_sq_re_pos
#print axioms selbergFourierZ_inv_sq_im_pos
#print axioms summable_cexp_neg_mul_nat_sq
#print axioms selbergGaussianCoefficient_re_pos
#print axioms summable_selbergGaussianThetaTerm
#print axioms selbergGaussianThetaTerm_eq
#print axioms summable_selbergGaussianThetaTerm_add_one
#print axioms hasSum_selbergGaussianThetaSum
#print axioms selbergGammaRayAngle_mem
#print axioms selbergGammaRayAngle_half_sub_fourierAngle
#print axioms selbergGammaFourierDecayMargin_pos
#print axioms selbergGammaHalf_mul_fourierTilt_le

end HardyTheorem
