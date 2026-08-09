import PrimeNumberTheorem.ExceptionalZeroEnergySeparatedWindows

open Complex MeasureTheory Set
open scoped BigOperators

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check rightHigherSeparatedWindowEnergy
#check rightHigherSeparatedCapacityKernel
#check rightHigherSeparatedAccumulatedCapacity

#check
  (rightHigherSeparatedWindowEnergy_le_accumulatedCapacity :
    ∀ (centers : Finset ℝ) (S : Finset ℂ)
      (L Told sigma T beta m : ℝ),
      MathlibAux.finiteCentersPairwiseSeparated centers L →
      0 < m →
      rightHigherSeparatedWindowEnergy
          centers S L Told sigma T beta m ≤
        rightHigherSeparatedAccumulatedCapacity
          centers S L Told sigma T beta m)

#check localSafeQ
#check localSafeAlpha

#check
  (localSafeQ_pos :
    ∀ {sigma beta : ℝ},
      1 / 2 < sigma → sigma < beta → beta < 1 →
      0 < localSafeQ sigma)

#check
  (localSafeAlpha_pos :
    ∀ {sigma beta : ℝ},
      1 / 2 < sigma → sigma < beta → beta < 1 →
      0 < localSafeAlpha sigma beta)

#check
  (localSafeAlpha_mul_q :
    ∀ {sigma beta : ℝ},
      1 / 2 < sigma → sigma < beta → beta < 1 →
      localSafeAlpha sigma beta * localSafeQ sigma =
        (beta - sigma) / 2)

#check
  (localSafeSquaredCapacityExponent_eq :
    ∀ {sigma beta : ℝ},
      1 / 2 < sigma → sigma < beta → beta < 1 →
      2 * (localSafeAlpha sigma beta * localSafeQ sigma + sigma - beta) =
        -(beta - sigma))

end PrimeNumberTheorem.VKEdgePiOverTwo
