import PrimeNumberTheorem.FirstOrderLSeriesPerron

open Complex MeasureTheory Set Filter Topology

namespace PrimeNumberTheorem

/-- Contract for the uniform natural-point Perron estimate needed by the
RH-scale explicit-formula route. -/
example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (W : ℝ), 2 ≤ m → 1 ≤ W →
      ‖(∫ w : ℝ in (-W)..W,
          ((m : ℝ) : ℂ) ^ perronLine 2 w *
            (-deriv riemannZeta (perronLine 2 w) /
              riemannZeta (perronLine 2 w)) /
                perronLine 2 w) -
          (chebyshevPsi0 (m : ℝ) : ℂ)‖ ≤
        C * (m : ℝ) ^ 5 / W := by
  exact exists_uniform_nat_norm_truncated_neg_logDeriv_firstOrderPerron_sub_chebyshevPsi0_le

end PrimeNumberTheorem
