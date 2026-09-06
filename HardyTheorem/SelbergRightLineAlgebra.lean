import HardyTheorem.SelbergGaussianMellin

open Complex

namespace HardyTheorem

/-! # Algebra of Selberg's absolutely convergent right-line expansion -/

/-- The complex power in each Gaussian Mellin term is exactly the product of
the completed-zeta, two mollifier, Fourier, and zeta Dirichlet powers. -/
theorem selbergGaussianMellinPower_eq
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ)
    {μ ν n : ℕ} (hμ : 0 < μ) (hν : 0 < ν) (hn : 0 < n)
    (s : ℂ) :
    (selbergGaussianCoefficient delta y μ ν * (n : ℂ) ^ 2) ^ (-s / 2) =
      (Real.pi : ℂ) ^ (-s / 2) *
        (μ : ℂ) ^ (-s) * (ν : ℂ) ^ s *
        selbergFourierZ delta y ^ s * (n : ℂ) ^ (-s) := by
  let phi : ℝ := Real.pi / 2 - delta
  let r : ℝ := Real.pi * ((μ : ℝ) / (ν : ℝ)) ^ 2 *
    Real.exp (2 * y) * (n : ℝ) ^ 2
  have hμr : 0 < (μ : ℝ) := by exact_mod_cast hμ
  have hνr : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < r := by dsimp [r]; positivity
  have hphiLow : -Real.pi < phi := by
    dsimp [phi]
    linarith [Real.pi_pos]
  have hphiHigh : phi ≤ Real.pi := by
    dsimp [phi]
    linarith [Real.pi_pos]
  have hpolar :
      selbergGaussianCoefficient delta y μ ν * (n : ℂ) ^ 2 =
        (r : ℂ) * Complex.exp ((phi : ℂ) * I) := by
    rw [selbergGaussianCoefficient_polar]
    dsimp [r, phi]
    push_cast
    ring
  have hlogr : Real.log r =
      Real.log Real.pi + 2 * Real.log (μ : ℝ) -
        2 * Real.log (ν : ℝ) + 2 * y + 2 * Real.log (n : ℝ) := by
    have hq : 0 < (μ : ℝ) / (ν : ℝ) := div_pos hμr hνr
    dsimp [r]
    rw [Real.log_mul (mul_ne_zero
          (mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 hq.ne'))
          (Real.exp_ne_zero _)) (pow_ne_zero 2 hnr.ne'),
      Real.log_mul (mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 hq.ne'))
        (Real.exp_ne_zero _),
      Real.log_mul Real.pi_ne_zero (pow_ne_zero 2 hq.ne'),
      Real.log_pow, Real.log_pow, Real.log_div hμr.ne' hνr.ne',
      Real.log_exp]
    ring
  have hw0 : selbergGaussianCoefficient delta y μ ν * (n : ℂ) ^ 2 ≠ 0 := by
    rw [hpolar]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')
      (Complex.exp_ne_zero _)
  have hpi0 : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hμ0 : (μ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hμ.ne'
  have hν0 : (ν : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hν.ne'
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hz0 := selbergFourierZ_ne_zero delta y
  rw [Complex.cpow_def_of_ne_zero hw0,
    Complex.cpow_def_of_ne_zero hpi0,
    Complex.cpow_def_of_ne_zero hμ0,
    Complex.cpow_def_of_ne_zero hν0,
    Complex.cpow_def_of_ne_zero hz0,
    Complex.cpow_def_of_ne_zero hn0]
  simp only [← Complex.exp_add]
  congr 1
  rw [hpolar, log_polar hr hphiLow hphiHigh, hlogr]
  push_cast
  rw [log_selbergFourierZ hdelta0 hdeltaPi y]
  dsimp [phi, selbergFourierAngle]
  push_cast
  rw [Complex.ofReal_log Real.pi_pos.le]
  ring_nf

end HardyTheorem
