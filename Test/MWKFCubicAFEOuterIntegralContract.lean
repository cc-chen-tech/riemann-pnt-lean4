import PrimeNumberTheorem.MWKFCubicAFEOuterIntegral

open Filter MeasureTheory
open scoped BigOperators

namespace PrimeNumberTheorem.MWKFCubic

-- The arithmetic series must be outside the physical integral.  Neither
-- absolute convergence nor interchange is an assumption supplied here.
#check (@cubicAFEMollifiedMomentFinite_eq_tripleIntegral :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 →
    ∀ {X : ℝ}, 1 / 2 < X → ∀ V : ℝ,
      cubicAFEMollifiedMomentFinite W T X V =
        ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
          ∑' p : ℕ × ℕ, ∫ t : ℝ,
            cubicAFECombinedSummandFinite W T X V d e t p)

#check (@tendsto_cubicAFETripleIntegral :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 →
    ∀ {X : ℝ}, 1 / 2 < X →
      Tendsto (fun V : ℝ ↦
        ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
          ∑' p : ℕ × ℕ, ∫ t : ℝ,
            cubicAFECombinedSummandFinite W T X V d e t p)
        atTop (nhds (cubicMollifiedSecondMoment W T : ℂ)))

end PrimeNumberTheorem.MWKFCubic
