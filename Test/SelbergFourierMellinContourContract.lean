import HardyTheorem.SelbergFourierMellinContour

open Complex Set
open scoped Interval

namespace HardyTheorem

#check selbergMellinWeight
#check selbergMellinPoleUnit
#check selbergMellinRegularPart
#check selbergMellinRegularizedIntegrand
#check selbergMellinRawIntegrand
#check analyticOnNhd_selbergMellinWeight
#check selbergMellinWeight_one
#check selbergMellinRaw_eq_regularized
#check boundaryRectIntegral_selbergMellinRaw
#check normalized_boundaryRectIntegral_selbergMellinRaw

example {z : ℂ} (hz : z ≠ 0) (X : ℕ) {c T : ℝ}
    (hc : 1 < c) (hT : 0 < T) :
    MathlibAux.boundaryRectIntegral (selbergMellinRawIntegrand z X)
        (1 / 2) c (-T) T =
      (2 * Real.pi * I) *
        (z * selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0) := by
  exact boundaryRectIntegral_selbergMellinRaw hz X hc hT

end HardyTheorem
