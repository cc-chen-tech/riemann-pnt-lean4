import HardyTheorem.SelbergRightLineAlgebra

open Complex

namespace HardyTheorem

#check selbergGaussianMellinPower_eq

example {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ)
    {μ ν n : ℕ} (hμ : 0 < μ) (hν : 0 < ν) (hn : 0 < n)
    (s : ℂ) :
    (selbergGaussianCoefficient delta y μ ν * (n : ℂ) ^ 2) ^ (-s / 2) =
      (Real.pi : ℂ) ^ (-s / 2) *
        (μ : ℂ) ^ (-s) * (ν : ℂ) ^ s *
        selbergFourierZ delta y ^ s * (n : ℂ) ^ (-s) := by
  exact selbergGaussianMellinPower_eq
    hdelta0 hdeltaPi y hμ hν hn s

end HardyTheorem
