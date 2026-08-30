import PrimeNumberTheorem.MWKFCubicAFEDiagonalSplit

open Filter MeasureTheory
open scoped BigOperators

namespace PrimeNumberTheorem.MWKFCubic

-- This is a split of the actual finite-height physical integral.  It must
-- not require a supplied summability or decomposition hypothesis.
#check (@cubicAFEMollifiedMomentFinite_eq_diagonal_add_offDiagonal :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 →
    ∀ {X : ℝ}, 1 / 2 < X → ∀ V : ℝ,
      cubicAFEMollifiedMomentFinite W T X V =
        cubicAFEDiagonalMomentFinite W T X V +
          cubicAFEOffDiagonalMomentFinite W T X V)

#check (@cubicAFEDiagonalMomentFinite_eq_ray :
  ∀ (W : CubicTestWeight) (T X V : ℝ),
    cubicAFEDiagonalMomentFinite W T X V =
      ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
        ∑' k : ℕ, ∫ t : ℝ,
          cubicAFECombinedSummandFinite W T X V d e t (cubicAFEDiagonalRay d e k))

-- Orientation regression: first positive index is l*(e/q), not l*(d/q).
example : cubicAFEDiagonalRay 6 10 0 = (4, 2) := by decide
example : cubicAFEDiagonalRay 6 10 2 = (14, 8) := by decide
example : cubicAFEDiagonalRay 7 7 3 = (3, 3) := by decide

-- The height limit is asserted only for the sum of both pieces.
#check (@tendsto_cubicAFEDiagonal_add_offDiagonal :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 →
    ∀ {X : ℝ}, 1 / 2 < X →
      Tendsto (fun V : ℝ ↦ cubicAFEDiagonalMomentFinite W T X V +
        cubicAFEOffDiagonalMomentFinite W T X V)
        atTop (nhds (cubicMollifiedSecondMoment W T : ℂ)))

end PrimeNumberTheorem.MWKFCubic
