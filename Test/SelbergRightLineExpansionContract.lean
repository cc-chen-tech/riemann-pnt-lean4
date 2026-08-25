import HardyTheorem.SelbergRightLineExpansion

open Complex

namespace HardyTheorem

#check selbergRightLineLevel
#check selbergMellinWeight_mul_dirichletTerm_eq_rightLineLevel
#check selbergMellinRaw_rightLine_eq_tsum
#check summable_integral_norm_selbergRightLineLevel
#check normalized_integral_selbergMellinRaw_rightLine_eq_thetaKernel

example {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ)
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    selbergMellinWeight (selbergFourierZ delta y) X
        ((2 : ℂ) + I * t) *
        (1 / (n : ℂ) ^ ((2 : ℂ) + I * t)) =
      selbergRightLineLevel delta X y (n - 1) t := by
  exact selbergMellinWeight_mul_dirichletTerm_eq_rightLineLevel
    hdelta0 hdeltaPi y X hn t

end HardyTheorem
