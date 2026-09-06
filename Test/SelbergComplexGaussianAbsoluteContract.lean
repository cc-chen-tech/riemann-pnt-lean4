import HardyTheorem.SelbergComplexGaussianAbsolute

open Real Complex Set MeasureTheory

namespace HardyTheorem

#check norm_Gamma_half_vertical_polar_cpow
#check integrable_Gamma_half_vertical_polar_cpow
#check integral_norm_Gamma_half_vertical_polar_cpow

example {phi r : ℝ} (hphi0 : 0 ≤ phi)
    (hphiPi : phi < Real.pi / 2) (hr : 0 < r) :
    Integrable (fun t : ℝ =>
      Complex.Gamma (((2 : ℂ) + I * t) / 2) *
        (((r : ℂ) * Complex.exp ((phi : ℂ) * I)) ^
          (-(((2 : ℂ) + I * t) / 2)))) := by
  exact integrable_Gamma_half_vertical_polar_cpow hphi0 hphiPi hr

end HardyTheorem
