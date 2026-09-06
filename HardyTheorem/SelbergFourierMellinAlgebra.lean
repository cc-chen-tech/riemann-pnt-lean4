import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import HardyTheorem.SelbergGammaRayBound

open Complex

namespace HardyTheorem

/-!
# Algebra of Selberg's Fourier--Mellin phase

This file isolates the exact complex identities behind the passage from the
Mellin variable to Selberg's Gaussian Fourier kernel.  It deliberately does
not assert the contour shift or Fourier inversion: those remain analytic S1
obligations.
-/

/-- The angular displacement in Selberg's completed-zeta Fourier tilt. -/
noncomputable def selbergFourierAngle (delta : ℝ) : ℝ :=
  Real.pi / 4 - delta / 2

/-- The ray angle used to obtain exponential decay from the rotated Gamma
integral. -/
noncomputable def selbergGammaRayAngle (delta : ℝ) : ℝ :=
  Real.pi / 2 - delta / 2

theorem selbergGammaRayAngle_mem
    {delta : ℝ} (hdelta0 : 0 < delta) (hdeltaPi : delta < Real.pi) :
    0 < selbergGammaRayAngle delta ∧
      selbergGammaRayAngle delta < Real.pi / 2 := by
  unfold selbergGammaRayAngle
  constructor <;> linarith

/-- Half of the Gamma-ray decay exceeds the Fourier tilt by exactly
`delta / 4`. -/
theorem selbergGammaRayAngle_half_sub_fourierAngle (delta : ℝ) :
    selbergGammaRayAngle delta / 2 - selbergFourierAngle delta =
      delta / 4 := by
  unfold selbergGammaRayAngle selbergFourierAngle
  ring

theorem selbergGammaFourierDecayMargin_pos
    {delta : ℝ} (hdelta0 : 0 < delta) :
    0 < selbergGammaRayAngle delta / 2 - selbergFourierAngle delta := by
  rw [selbergGammaRayAngle_half_sub_fourierAngle]
  positivity

/-- On the positive half of the Mellin line, the Gamma decay at Selberg's
rotated-ray angle absorbs the principal-power Fourier tilt and leaves the
strict factor `exp (-(delta / 4) * t)`. -/
theorem selbergGammaHalf_mul_fourierTilt_le
    {delta sigma t : ℝ}
    (hdelta0 : 0 < delta) (hdeltaPi : delta < Real.pi / 2)
    (hsigma : 0 < sigma) (ht : 0 ≤ t) :
    ‖Complex.Gamma (((sigma : ℂ) + I * t) / 2)‖ *
        Real.exp (selbergFourierAngle delta * t) ≤
      Real.Gamma (sigma / 2) *
        (Real.cos (selbergGammaRayAngle delta)) ^ (-sigma / 2) *
        Real.exp (-(delta / 4) * t) := by
  have heta := selbergGammaRayAngle_mem hdelta0 (hdeltaPi.trans (by linarith [Real.pi_pos]))
  have hgamma :=
    norm_Gamma_le_real_Gamma_mul_cos_rpow_mul_exp_neg_abs_im
      (((sigma : ℂ) + I * t) / 2) heta.1.le heta.2
        (by simpa using div_pos hsigma (by norm_num : (0 : ℝ) < 2))
  have hre : (((sigma : ℂ) + I * t) / 2).re = sigma / 2 := by
    norm_num
  have him : (((sigma : ℂ) + I * t) / 2).im = t / 2 := by
    norm_num
  have htHalf : 0 ≤ t / 2 := div_nonneg ht (by norm_num)
  rw [hre, him, abs_of_nonneg htHalf] at hgamma
  have hnegHalf : -(sigma / 2) = -sigma / 2 := by ring
  rw [hnegHalf] at hgamma
  have hexp :
      Real.exp (-selbergGammaRayAngle delta * (t / 2)) *
          Real.exp (selbergFourierAngle delta * t) =
        Real.exp (-(delta / 4) * t) := by
    rw [← Real.exp_add]
    congr 1
    rw [← selbergGammaRayAngle_half_sub_fourierAngle delta]
    ring
  calc
    ‖Complex.Gamma (((sigma : ℂ) + I * t) / 2)‖ *
        Real.exp (selbergFourierAngle delta * t) ≤
      (Real.Gamma (sigma / 2) *
          (Real.cos (selbergGammaRayAngle delta)) ^ (-sigma / 2) *
          Real.exp (-selbergGammaRayAngle delta * (t / 2))) *
        Real.exp (selbergFourierAngle delta * t) :=
      mul_le_mul_of_nonneg_right hgamma
        (Real.exp_pos (selbergFourierAngle delta * t)).le
    _ = Real.Gamma (sigma / 2) *
        (Real.cos (selbergGammaRayAngle delta)) ^ (-sigma / 2) *
        Real.exp (-(delta / 4) * t) := by
      calc
        (Real.Gamma (sigma / 2) *
              (Real.cos (selbergGammaRayAngle delta)) ^ (-sigma / 2) *
              Real.exp (-selbergGammaRayAngle delta * (t / 2))) *
            Real.exp (selbergFourierAngle delta * t) =
          (Real.Gamma (sigma / 2) *
              (Real.cos (selbergGammaRayAngle delta)) ^ (-sigma / 2)) *
            (Real.exp (-selbergGammaRayAngle delta * (t / 2)) *
              Real.exp (selbergFourierAngle delta * t)) := by ring
        _ = _ := by rw [hexp]

/-- Signed-height version of the Gamma/Fourier estimate.  It is uniform on
the upper and lower horizontal sides and keeps the same strict
`exp (-(δ/4)|t|)` margin. -/
theorem selbergGammaHalf_mul_fourierTilt_le_abs
    {delta sigma t : ℝ}
    (hdelta0 : 0 < delta) (hdeltaPi : delta < Real.pi / 2)
    (hsigma : 0 < sigma) :
    ‖Complex.Gamma (((sigma : ℂ) + I * t) / 2)‖ *
        Real.exp (selbergFourierAngle delta * t) ≤
      Real.Gamma (sigma / 2) *
        (Real.cos (selbergGammaRayAngle delta)) ^ (-sigma / 2) *
        Real.exp (-(delta / 4) * |t|) := by
  have heta := selbergGammaRayAngle_mem hdelta0
    (hdeltaPi.trans (by linarith [Real.pi_pos]))
  have hgamma :=
    norm_Gamma_le_real_Gamma_mul_cos_rpow_mul_exp_neg_abs_im
      (((sigma : ℂ) + I * t) / 2) heta.1.le heta.2
        (by simpa using div_pos hsigma (by norm_num : (0 : ℝ) < 2))
  have hre : (((sigma : ℂ) + I * t) / 2).re = sigma / 2 := by
    norm_num
  have him : (((sigma : ℂ) + I * t) / 2).im = t / 2 := by
    norm_num
  have habs : |t / 2| = |t| / 2 := by
    rw [abs_div]
    norm_num
  rw [hre, him, habs] at hgamma
  have hnegHalf : -(sigma / 2) = -sigma / 2 := by ring
  rw [hnegHalf] at hgamma
  have htheta : 0 ≤ selbergFourierAngle delta := by
    unfold selbergFourierAngle
    linarith
  have htilt :
      Real.exp (selbergFourierAngle delta * t) ≤
        Real.exp (selbergFourierAngle delta * |t|) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (le_abs_self t) htheta
  let C : ℝ := Real.Gamma (sigma / 2) *
    (Real.cos (selbergGammaRayAngle delta)) ^ (-sigma / 2)
  have hC : 0 ≤ C := by
    exact mul_nonneg (Real.Gamma_pos_of_pos (by positivity)).le
      (Real.rpow_nonneg (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], heta.2⟩).le _)
  have hgammaC :
      ‖Complex.Gamma (((sigma : ℂ) + I * t) / 2)‖ ≤
        C * Real.exp (-selbergGammaRayAngle delta * (|t| / 2)) := by
    simpa only [C] using hgamma
  have hexp :
      Real.exp (-selbergGammaRayAngle delta * (|t| / 2)) *
          Real.exp (selbergFourierAngle delta * |t|) =
        Real.exp (-(delta / 4) * |t|) := by
    rw [← Real.exp_add]
    congr 1
    rw [← selbergGammaRayAngle_half_sub_fourierAngle delta]
    ring
  change ‖Complex.Gamma (((sigma : ℂ) + I * t) / 2)‖ *
      Real.exp (selbergFourierAngle delta * t) ≤
    C * Real.exp (-(delta / 4) * |t|)
  calc
    ‖Complex.Gamma (((sigma : ℂ) + I * t) / 2)‖ *
        Real.exp (selbergFourierAngle delta * t) ≤
      (C * Real.exp (-selbergGammaRayAngle delta * (|t| / 2))) *
        Real.exp (selbergFourierAngle delta * t) :=
      mul_le_mul_of_nonneg_right hgammaC (Real.exp_pos _).le
    _ ≤ (C * Real.exp (-selbergGammaRayAngle delta * (|t| / 2))) *
        Real.exp (selbergFourierAngle delta * |t|) := by
      exact mul_le_mul_of_nonneg_left htilt
        (mul_nonneg hC (Real.exp_pos _).le)
    _ = C * Real.exp (-(delta / 4) * |t|) := by
      rw [show (C * Real.exp (-selbergGammaRayAngle delta * (|t| / 2))) *
          Real.exp (selbergFourierAngle delta * |t|) =
        C * (Real.exp (-selbergGammaRayAngle delta * (|t| / 2)) *
          Real.exp (selbergFourierAngle delta * |t|)) by ring, hexp]

/-- The complex Mellin parameter after the logarithmic substitution
`x = exp y`. -/
noncomputable def selbergFourierZ (delta y : ℝ) : ℂ :=
  Complex.exp ((-y : ℂ) - I * selbergFourierAngle delta)

theorem selbergFourierZ_ne_zero (delta y : ℝ) :
    selbergFourierZ delta y ≠ 0 := by
  exact Complex.exp_ne_zero _

theorem log_selbergFourierZ
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) :
    Complex.log (selbergFourierZ delta y) =
      (-y : ℂ) - I * selbergFourierAngle delta := by
  unfold selbergFourierZ
  apply Complex.log_exp
  · have hthetaPi : selbergFourierAngle delta < Real.pi := by
      unfold selbergFourierAngle
      linarith [Real.pi_pos]
    simpa using hthetaPi
  · have htheta0 : 0 < selbergFourierAngle delta := by
      unfold selbergFourierAngle
      linarith
    have hnegThetaPi : -selbergFourierAngle delta ≤ Real.pi := by
      linarith [Real.pi_pos]
    simpa using hnegThetaPi

/-- The principal complex power gives exactly the exponential tilt and the
unitary Fourier phase used in Selberg's S1 identity. -/
theorem selbergFourierZ_cpow_I
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y t : ℝ) :
    selbergFourierZ delta y ^ (I * t) =
      (Real.exp (selbergFourierAngle delta * t) : ℂ) *
        Complex.exp (-I * (y * t)) := by
  rw [Complex.cpow_def_of_ne_zero (selbergFourierZ_ne_zero delta y),
    log_selbergFourierZ hdelta0 hdeltaPi y]
  have hexponent :
      (((-y : ℂ) - I * selbergFourierAngle delta) * (I * t)) =
        (selbergFourierAngle delta * t : ℝ) + (-I * (y * t)) := by
    push_cast
    ring_nf
    simp [I_sq]
  rw [hexponent, Complex.exp_add, ← Complex.ofReal_exp]

/-- Exact modulus of Selberg's principal complex power on a horizontal
line.  The `t` term is the Fourier tilt that the rotated Gamma bound must
absorb. -/
theorem norm_selbergFourierZ_cpow
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y sigma t : ℝ) :
    ‖selbergFourierZ delta y ^ ((sigma : ℂ) + I * t)‖ =
      Real.exp (-y * sigma + selbergFourierAngle delta * t) := by
  rw [Complex.cpow_def_of_ne_zero (selbergFourierZ_ne_zero delta y),
    log_selbergFourierZ hdelta0 hdeltaPi y, Complex.norm_exp]
  congr 1
  norm_num [Complex.mul_re]

/-- Squaring the reciprocal Mellin parameter produces the damped oscillatory
Gaussian phase `sin delta + i cos delta` used in both the diagonal and the
off-diagonal energy calculations. -/
theorem selbergFourierZ_inv_sq (delta y : ℝ) :
    (selbergFourierZ delta y)⁻¹ ^ (2 : ℕ) =
      (Real.exp (2 * y) : ℂ) *
        ((Real.sin delta : ℂ) + I * Real.cos delta) := by
  unfold selbergFourierZ
  rw [← Complex.exp_neg, ← Complex.exp_nat_mul]
  have hexponent :
      (((2 : ℕ) : ℂ) *
          -((-y : ℂ) - I * (selbergFourierAngle delta : ℂ))) =
        (2 * y : ℝ) + I * (Real.pi / 2 - delta) := by
    apply Complex.ext
    · norm_num [selbergFourierAngle]
    · norm_num [selbergFourierAngle]
      ring
  rw [hexponent, Complex.exp_add, ← Complex.ofReal_exp,
    show I * ((Real.pi : ℂ) / 2 - (delta : ℂ)) =
      ((Real.pi / 2 - delta : ℝ) : ℂ) * I by
        push_cast
        ring,
    Complex.exp_ofReal_mul_I, Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub]
  ring

/-- In Selberg's admissible angular range the Gaussian phase has strictly
positive real part, hence genuine decay. -/
theorem selbergFourierZ_inv_sq_re_pos
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) :
    0 < ((selbergFourierZ delta y)⁻¹ ^ (2 : ℕ)).re := by
  rw [selbergFourierZ_inv_sq]
  have hsin : 0 < Real.sin delta :=
    Real.sin_pos_of_pos_of_lt_pi hdelta0 (by linarith [Real.pi_pos])
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    sub_zero, add_zero]
  exact mul_pos (Real.exp_pos (2 * y)) hsin

/-- In the same range the imaginary part is strictly positive and supplies
the oscillation used by the off-diagonal estimate. -/
theorem selbergFourierZ_inv_sq_im_pos
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) :
    0 < ((selbergFourierZ delta y)⁻¹ ^ (2 : ℕ)).im := by
  rw [selbergFourierZ_inv_sq]
  have hcos : 0 < Real.cos delta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hdeltaPi⟩
  simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_add, add_zero]
  exact mul_pos (Real.exp_pos (2 * y)) hcos

/-- A complex Gaussian with positive real coefficient is absolutely
summable on the natural numbers.  This is the convergence lemma needed for
the nonconstant theta series in Selberg's exact S1 transform. -/
theorem summable_cexp_neg_mul_nat_sq {A : ℂ} (hA : 0 < A.re) :
    Summable (fun n : ℕ => Complex.exp (-A * (n : ℂ) ^ 2)) := by
  apply Summable.of_norm_bounded
    (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hA))
  intro n
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    by_cases hn0 : n = 0
    · simp [hn0]
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
      nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) by positivity)
        (sub_nonneg.mpr hn1)]
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, zero_mul, mul_zero,
    sub_zero, add_zero]
  nlinarith

/-- The complex Gaussian coefficient occurring after Selberg's logarithmic
Mellin substitution. -/
noncomputable def selbergGaussianCoefficient
    (delta y : ℝ) (μ ν : ℕ) : ℂ :=
  (Real.pi * ((μ : ℝ) / (ν : ℝ)) ^ 2 : ℝ) *
    (selbergFourierZ delta y)⁻¹ ^ (2 : ℕ)

/-- Polar form of the complex Gaussian coefficient.  Its angle is exactly
`pi/2-delta`; this is the phase cancelled by the rotated Gamma ray in the
complex inverse Mellin formula. -/
theorem selbergGaussianCoefficient_polar
    (delta y : ℝ) (μ ν : ℕ) :
    selbergGaussianCoefficient delta y μ ν =
      (Real.pi * ((μ : ℝ) / (ν : ℝ)) ^ 2 * Real.exp (2 * y) : ℝ) *
        Complex.exp (((Real.pi / 2 - delta : ℝ) : ℂ) * I) := by
  have hphase :
      Complex.exp (((Real.pi / 2 - delta : ℝ) : ℂ) * I) =
        (Real.sin delta : ℂ) + I * Real.cos delta := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    ring
  rw [selbergGaussianCoefficient, selbergFourierZ_inv_sq, hphase]
  push_cast
  ring

/-- One term of the nonconstant theta series in Selberg's exact inverse
Fourier kernel. -/
noncomputable def selbergGaussianThetaTerm
    (delta y : ℝ) (μ ν n : ℕ) : ℂ :=
  Complex.exp (-selbergGaussianCoefficient delta y μ ν * (n : ℂ) ^ 2)

/-- Positive mollifier indices make the real part of Selberg's Gaussian
coefficient strictly positive. -/
theorem selbergGaussianCoefficient_re_pos
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2)
    {μ ν : ℕ} (hμ : 0 < μ) (hν : 0 < ν) (y : ℝ) :
    0 < (selbergGaussianCoefficient delta y μ ν).re := by
  unfold selbergGaussianCoefficient
  have hμr : 0 < (μ : ℝ) := by exact_mod_cast hμ
  have hνr : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hscale : 0 < Real.pi * ((μ : ℝ) / (ν : ℝ)) ^ 2 := by
    exact mul_pos Real.pi_pos (sq_pos_of_pos (div_pos hμr hνr))
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_pos hscale
    (selbergFourierZ_inv_sq_re_pos hdelta0 hdeltaPi y)

/-- The actual theta series used by Selberg is absolutely convergent for
every positive pair of mollifier indices. -/
theorem summable_selbergGaussianThetaTerm
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2)
    {μ ν : ℕ} (hμ : 0 < μ) (hν : 0 < ν) (y : ℝ) :
    Summable (selbergGaussianThetaTerm delta y μ ν) := by
  unfold selbergGaussianThetaTerm
  exact summable_cexp_neg_mul_nat_sq
    (selbergGaussianCoefficient_re_pos hdelta0 hdeltaPi hμ hν y)

/-- The coefficient notation expands to the exact Gaussian appearing in
Selberg's equations (7.3) and (8.7). -/
theorem selbergGaussianThetaTerm_eq
    (delta y : ℝ) (μ ν n : ℕ) :
    selbergGaussianThetaTerm delta y μ ν n =
      Complex.exp
        (-((Real.pi * (((n : ℝ) * μ) / ν) ^ 2 : ℝ) : ℂ) *
          (selbergFourierZ delta y)⁻¹ ^ (2 : ℕ)) := by
  unfold selbergGaussianThetaTerm selbergGaussianCoefficient
  apply congrArg Complex.exp
  push_cast
  ring

/-- The positive-index theta series is the one-shifted tail of the
absolutely summable natural-number Gaussian. -/
theorem summable_selbergGaussianThetaTerm_add_one
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2)
    {μ ν : ℕ} (hμ : 0 < μ) (hν : 0 < ν) (y : ℝ) :
    Summable (fun n : ℕ =>
      selbergGaussianThetaTerm delta y μ ν (n + 1)) := by
  exact (summable_nat_add_iff 1).mpr
    (summable_selbergGaussianThetaTerm hdelta0 hdeltaPi hμ hν y)

/-- The convergent positive-index Gaussian theta sum in Selberg's explicit
inverse Fourier kernel. -/
noncomputable def selbergGaussianThetaSum
    (delta y : ℝ) (μ ν : ℕ) : ℂ :=
  ∑' n : ℕ, selbergGaussianThetaTerm delta y μ ν (n + 1)

theorem hasSum_selbergGaussianThetaSum
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2)
    {μ ν : ℕ} (hμ : 0 < μ) (hν : 0 < ν) (y : ℝ) :
    HasSum
      (fun n : ℕ => selbergGaussianThetaTerm delta y μ ν (n + 1))
      (selbergGaussianThetaSum delta y μ ν) := by
  unfold selbergGaussianThetaSum
  exact (summable_selbergGaussianThetaTerm_add_one
    hdelta0 hdeltaPi hμ hν y).hasSum

end HardyTheorem
