import HardyTheorem.SelbergComplexGaussianMellin

open Real Complex Set MeasureTheory Filter Topology

namespace HardyTheorem

#check selbergRotatedExponential
#check mellin_selbergRotatedExponential
#check integrable_exp_neg_mul_abs
#check log_polar
#check polar_cpow_neg
#check verticalIntegrable_mellin_selbergRotatedExponential
#check integral_Gamma_polar_cpow
#check integral_Gamma_half_vertical_polar_cpow

example {phi r : ℝ} (hphi0 : 0 ≤ phi)
    (hphiPi : phi < Real.pi / 2) (hr : 0 < r) :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ,
          Complex.Gamma ((1 : ℂ) + I * t) *
            (((r : ℂ) * Complex.exp ((phi : ℂ) * I)) ^
              (-((1 : ℂ) + I * t)))) =
      Complex.exp (-((r : ℂ) * Complex.exp ((phi : ℂ) * I))) := by
  exact integral_Gamma_polar_cpow hphi0 hphiPi hr

example {phi r : ℝ} (hphi0 : 0 ≤ phi)
    (hphiPi : phi < Real.pi / 2) (hr : 0 < r) :
    (1 / (4 * Real.pi) : ℂ) *
        (∫ t : ℝ,
          Complex.Gamma (((2 : ℂ) + I * t) / 2) *
            (((r : ℂ) * Complex.exp ((phi : ℂ) * I)) ^
              (-(((2 : ℂ) + I * t) / 2)))) =
      Complex.exp (-((r : ℂ) * Complex.exp ((phi : ℂ) * I))) := by
  exact integral_Gamma_half_vertical_polar_cpow hphi0 hphiPi hr

end HardyTheorem
