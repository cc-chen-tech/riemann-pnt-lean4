import PrimeNumberTheorem.FirstOrderLSeriesPerron

open Complex MeasureTheory Set Filter Topology

namespace PrimeNumberTheorem

example {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℝ, 1 ≤ W →
      ‖(∫ w : ℝ in (-W)..W,
          (x : ℂ) ^ perronLine c w *
            (-deriv riemannZeta (perronLine c w) /
              riemannZeta (perronLine c w)) /
                perronLine c w) -
          (chebyshevPsi0 x : ℂ)‖ ≤ C / W :=
  exists_norm_truncated_neg_logDeriv_firstOrderPerron_sub_chebyshevPsi0_le_div
    hx hc

end PrimeNumberTheorem
