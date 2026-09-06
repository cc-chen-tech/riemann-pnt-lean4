import HardyTheorem.SelbergComplexGaussianMellin
import HardyTheorem.SelbergFourierMellinAlgebra

open Real Complex Set MeasureTheory

namespace HardyTheorem

/-! # Termwise Gaussian Mellin inversion in Selberg's theta kernel -/

/-- Every positive arithmetic index in the right-line Dirichlet expansion
has inverse Mellin transform equal to the corresponding complex Gaussian
theta term. -/
theorem integral_selbergGaussianMellin_eq_thetaTerm
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ)
    {μ ν n : ℕ} (hμ : 0 < μ) (hν : 0 < ν) (hn : 0 < n) :
    (1 / (4 * Real.pi) : ℂ) *
        (∫ t : ℝ,
          Complex.Gamma (((2 : ℂ) + I * t) / 2) *
            ((selbergGaussianCoefficient delta y μ ν * (n : ℂ) ^ 2) ^
              (-(((2 : ℂ) + I * t) / 2)))) =
      selbergGaussianThetaTerm delta y μ ν n := by
  let phi : ℝ := Real.pi / 2 - delta
  let r : ℝ := Real.pi * ((μ : ℝ) / (ν : ℝ)) ^ 2 *
    Real.exp (2 * y) * (n : ℝ) ^ 2
  have hphi0 : 0 ≤ phi := by dsimp [phi]; linarith
  have hphiPi : phi < Real.pi / 2 := by dsimp [phi]; linarith
  have hμr : 0 < (μ : ℝ) := by exact_mod_cast hμ
  have hνr : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hpolar :
      selbergGaussianCoefficient delta y μ ν * (n : ℂ) ^ 2 =
        (r : ℂ) * Complex.exp ((phi : ℂ) * I) := by
    rw [selbergGaussianCoefficient_polar]
    dsimp [r, phi]
    push_cast
    ring
  rw [hpolar]
  have h := integral_Gamma_half_vertical_polar_cpow hphi0 hphiPi hr
  rw [h]
  unfold selbergGaussianThetaTerm
  congr 2
  calc
    -((r : ℂ) * Complex.exp ((phi : ℂ) * I)) =
        -(selbergGaussianCoefficient delta y μ ν * (n : ℂ) ^ 2) := by
      rw [hpolar]
    _ = -selbergGaussianCoefficient delta y μ ν * (n : ℂ) ^ 2 := by ring

end HardyTheorem
