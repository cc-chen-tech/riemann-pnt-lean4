import HardyTheorem.SelbergFourierMellinVertical

open Complex MeasureTheory Set Filter Topology
open scoped Interval

namespace HardyTheorem

#check continuous_selbergMellinRaw_vertical
#check integrable_selbergMellinRaw_vertical
#check tendsto_selbergMellinRaw_vertical_intervalIntegral
#check integral_selbergMellinRaw_vertical_sub
#check normalized_integral_selbergMellinRaw_vertical_sub

example {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ) :
    (∫ t : ℝ, selbergMellinRawIntegrand (selbergFourierZ delta y) X
          ((2 : ℂ) + I * t)) -
        (∫ t : ℝ, selbergMellinRawIntegrand (selbergFourierZ delta y) X
          ((1 / 2 : ℂ) + I * t)) =
      (2 * Real.pi : ℂ) *
        (selbergFourierZ delta y * selbergSqrtZetaPsi X 1 *
          selbergSqrtZetaPsi X 0) := by
  exact integral_selbergMellinRaw_vertical_sub hdelta0 hdeltaPi y X

end HardyTheorem
