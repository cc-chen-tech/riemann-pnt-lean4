import PrimeNumberTheorem.VKEdgeZeroClusterApproximationL2

open Complex Filter Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check normalizedFiniteZeroClusterApproximationErrorSecondMoment

#check
  (eventually_exists_goodHeight_normalizedApproximationErrorSecondMoment_lt :
    ∀ {beta L eta : ℝ},
      1 / 2 < beta →
      beta < 1 →
      0 ≤ L →
      0 < eta →
      ∀ᶠ a in atTop,
        ∃ T ∈ Set.Icc (Real.exp (a / 2)) (Real.exp (a / 2) + 1),
          ExplicitFormulaAux.goodHeight T ∧
            normalizedFiniteZeroClusterApproximationErrorSecondMoment
                T beta a L <
              eta)

end VKEdgePiOverTwo
end PrimeNumberTheorem
