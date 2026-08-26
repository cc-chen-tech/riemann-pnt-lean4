import HardyTheorem.SelbergGaussianMellin
import HardyTheorem.SelbergComplexGaussianAbsolute
import Mathlib.Analysis.PSeries

open Real Complex Set MeasureTheory

namespace HardyTheorem

/-! # Absolute convergence of Selberg's arithmetic Gaussian terms -/

/-- One unweighted arithmetic term on the right Mellin line. -/
noncomputable def selbergGaussianMellinLineTerm
    (delta y : ℝ) (μ ν n : ℕ) (t : ℝ) : ℂ :=
  Complex.Gamma (((2 : ℂ) + I * t) / 2) *
    ((selbergGaussianCoefficient delta y μ ν * (n : ℂ) ^ 2) ^
      (-(((2 : ℂ) + I * t) / 2)))

private theorem selbergGaussianMellinLineTerm_polar
    (delta y : ℝ) (μ ν n : ℕ) (t : ℝ) :
    selbergGaussianMellinLineTerm delta y μ ν n t =
      Complex.Gamma (((2 : ℂ) + I * t) / 2) *
        ((((Real.pi * ((μ : ℝ) / (ν : ℝ)) ^ 2 *
              Real.exp (2 * y) * (n : ℝ) ^ 2 : ℝ) : ℂ) *
            Complex.exp (((Real.pi / 2 - delta : ℝ) : ℂ) * I)) ^
          (-(((2 : ℂ) + I * t) / 2))) := by
  unfold selbergGaussianMellinLineTerm
  apply congrArg (fun w : ℂ =>
    Complex.Gamma (((2 : ℂ) + I * t) / 2) *
      w ^ (-(((2 : ℂ) + I * t) / 2)))
  rw [selbergGaussianCoefficient_polar]
  push_cast
  ring

/-- Each positive arithmetic term is absolutely integrable. -/
theorem integrable_selbergGaussianMellinLineTerm
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ)
    {μ ν n : ℕ} (hμ : 0 < μ) (hν : 0 < ν) (hn : 0 < n) :
    Integrable (selbergGaussianMellinLineTerm delta y μ ν n) := by
  let phi : ℝ := Real.pi / 2 - delta
  let r : ℝ := Real.pi * ((μ : ℝ) / (ν : ℝ)) ^ 2 *
    Real.exp (2 * y) * (n : ℝ) ^ 2
  have hphi0 : 0 ≤ phi := by dsimp [phi]; linarith
  have hphiPi : phi < Real.pi / 2 := by dsimp [phi]; linarith
  have hμr : 0 < (μ : ℝ) := by exact_mod_cast hμ
  have hνr : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < r := by dsimp [r]; positivity
  have h := integrable_Gamma_half_vertical_polar_cpow hphi0 hphiPi hr
  apply h.congr
  filter_upwards with t
  symm
  simpa [phi, r] using selbergGaussianMellinLineTerm_polar delta y μ ν n t

/-- The exact `L¹` norm formula specialized to Selberg's arithmetic
radius. -/
theorem integral_norm_selbergGaussianMellinLineTerm
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ)
    {μ ν n : ℕ} (hμ : 0 < μ) (hν : 0 < ν) (hn : 0 < n) :
    (∫ t : ℝ, ‖selbergGaussianMellinLineTerm delta y μ ν n t‖) =
      2 * (Real.pi * ((μ : ℝ) / (ν : ℝ)) ^ 2 *
        Real.exp (2 * y) * (n : ℝ) ^ 2)⁻¹ *
        (∫ u : ℝ, ‖mellin
          (selbergRotatedExponential (Real.pi / 2 - delta))
          ((1 : ℂ) + I * u)‖) := by
  let phi : ℝ := Real.pi / 2 - delta
  let r : ℝ := Real.pi * ((μ : ℝ) / (ν : ℝ)) ^ 2 *
    Real.exp (2 * y) * (n : ℝ) ^ 2
  have hphi0 : 0 ≤ phi := by dsimp [phi]; linarith
  have hphiPi : phi < Real.pi / 2 := by dsimp [phi]; linarith
  have hμr : 0 < (μ : ℝ) := by exact_mod_cast hμ
  have hνr : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < r := by dsimp [r]; positivity
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
    (fun t => congrArg norm
      (selbergGaussianMellinLineTerm_polar delta y μ ν n t)))]
  simpa [phi, r] using
    integral_norm_Gamma_half_vertical_polar_cpow hphi0 hphiPi hr

/-- The integrated absolute values form a convergent series.  The exact
majorant is a constant times `(n+1)⁻²`. -/
theorem summable_integral_norm_selbergGaussianMellinLineTerm_add_one
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ)
    {μ ν : ℕ} (hμ : 0 < μ) (hν : 0 < ν) :
    Summable (fun k : ℕ => ∫ t : ℝ,
      ‖selbergGaussianMellinLineTerm delta y μ ν (k + 1) t‖) := by
  let C : ℝ := Real.pi * ((μ : ℝ) / (ν : ℝ)) ^ 2 *
    Real.exp (2 * y)
  let A : ℝ := ∫ u : ℝ, ‖mellin
    (selbergRotatedExponential (Real.pi / 2 - delta))
    ((1 : ℂ) + I * u)‖
  have hC : C ≠ 0 := by
    have hμr : 0 < (μ : ℝ) := by exact_mod_cast hμ
    have hνr : 0 < (ν : ℝ) := by exact_mod_cast hν
    dsimp [C]
    positivity
  have hp : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    exact (summable_nat_add_iff 1).mpr
      (Real.summable_nat_pow_inv.mpr (by omega : 1 < (2 : ℕ)))
  have hmul := hp.mul_left (2 * C⁻¹ * A)
  apply hmul.congr
  intro k
  rw [integral_norm_selbergGaussianMellinLineTerm
    hdelta0 hdeltaPi y hμ hν (Nat.succ_pos k)]
  dsimp [C, A]
  have hk0 : (((k + 1 : ℕ) : ℝ) ^ 2) ≠ 0 := by positivity
  rw [mul_inv]
  ring

end HardyTheorem
