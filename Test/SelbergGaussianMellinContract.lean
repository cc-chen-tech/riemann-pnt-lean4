import HardyTheorem.SelbergGaussianMellin

open Real Complex Set MeasureTheory

namespace HardyTheorem

#check integral_selbergGaussianMellin_eq_thetaTerm

example {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ)
    {μ ν n : ℕ} (hμ : 0 < μ) (hν : 0 < ν) (hn : 0 < n) :
    (1 / (4 * Real.pi) : ℂ) *
        (∫ t : ℝ,
          Complex.Gamma (((2 : ℂ) + I * t) / 2) *
            ((selbergGaussianCoefficient delta y μ ν * (n : ℂ) ^ 2) ^
              (-(((2 : ℂ) + I * t) / 2)))) =
      selbergGaussianThetaTerm delta y μ ν n := by
  exact integral_selbergGaussianMellin_eq_thetaTerm
    hdelta0 hdeltaPi y hμ hν hn

end HardyTheorem
