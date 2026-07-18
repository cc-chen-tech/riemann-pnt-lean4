import PrimeNumberTheorem.FirstOrderLSeriesPerron

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction BigOperators LSeries.notation

namespace PrimeNumberTheorem

/-- Contract for the moving-right Perron estimate needed by the unconditional
PNT height selection. -/
example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (W : ℝ), 2 ≤ m → 1 ≤ W →
      ‖(∫ w : ℝ in (-W)..W,
          ((m : ℝ) : ℂ) ^
              perronLine (1 + 1 / Real.log (m : ℝ)) w *
            (-deriv riemannZeta
                (perronLine (1 + 1 / Real.log (m : ℝ)) w) /
              riemannZeta
                (perronLine (1 + 1 / Real.log (m : ℝ)) w)) /
              perronLine (1 + 1 / Real.log (m : ℝ)) w) -
          (chebyshevPsi0 (m : ℝ) : ℂ)‖ ≤
        C * (m : ℝ) * (1 + Real.log (m : ℝ)) ^ 2 / W :=
  exists_uniform_nat_norm_movingRight_truncated_neg_logDeriv_firstOrderPerron_sub_chebyshevPsi0_le

end PrimeNumberTheorem
