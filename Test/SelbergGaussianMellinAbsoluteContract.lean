import HardyTheorem.SelbergGaussianMellinAbsolute

open Real Complex Set MeasureTheory

namespace HardyTheorem

#check selbergGaussianMellinLineTerm
#check integrable_selbergGaussianMellinLineTerm
#check summable_integral_norm_selbergGaussianMellinLineTerm_add_one

example {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ)
    {μ ν : ℕ} (hμ : 0 < μ) (hν : 0 < ν) :
    Summable (fun k : ℕ => ∫ t : ℝ,
      ‖selbergGaussianMellinLineTerm delta y μ ν (k + 1) t‖) := by
  exact summable_integral_norm_selbergGaussianMellinLineTerm_add_one
    hdelta0 hdeltaPi y hμ hν

end HardyTheorem
