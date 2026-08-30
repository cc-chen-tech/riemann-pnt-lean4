import PrimeNumberTheorem.MWKFCubicAFEShiftedIntegral

open Filter MeasureTheory
open scoped BigOperators

namespace PrimeNumberTheorem.MWKFCubic

-- Fail if the sign is reversed or subtraction is truncated in the naturals.
example : cubicAFEReducedShift 6 10 (0, 0) = 2 := by decide
example : cubicAFEReducedShift 6 10 (1, 0) = -1 := by decide
example : cubicAFEReducedShift 6 10 (4, 2) = 0 := by decide

-- The phase retains the full logarithm, including negative shifts.
#check (@cubicAFECombinedLogPhase_eq_reducedShift :
  ∀ (p : ℕ × ℕ) {d e : ℕ}, 0 < d → 0 < e →
    cubicAFECombinedLogPhase p d e =
      Real.log (1 + (cubicAFEReducedShift d e p : ℝ) /
        (((p.1 + 1 : ℕ) : ℝ) * ((d / Nat.gcd d e : ℕ) : ℝ))))

-- The actual integrated off-diagonal, not an arbitrary function or a
-- caller-supplied summable model, must equal the nonzero-shift expression.
#check (@cubicAFEOffDiagonalMomentFinite_eq_shifted :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 →
    ∀ {X : ℝ}, 1 / 2 < X → ∀ V : ℝ,
      cubicAFEOffDiagonalMomentFinite W T X V =
        cubicAFEShiftedMomentFinite W T X V)

#check (@tendsto_cubicAFEDiagonal_add_shifted :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 →
    ∀ {X : ℝ}, 1 / 2 < X →
      Tendsto (fun V : ℝ ↦ cubicAFEDiagonalMomentFinite W T X V +
        cubicAFEShiftedMomentFinite W T X V)
        atTop (nhds (cubicMollifiedSecondMoment W T : ℂ)))

end PrimeNumberTheorem.MWKFCubic
