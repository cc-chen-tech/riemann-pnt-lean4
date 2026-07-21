import HardyTheorem.SelbergSmallAbsGapDecomposition

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Contract for the gap-sum diagonal/off-diagonal decomposition

The example instantiates the decomposition at schematic parameters, exposing
the exact two remaining analytic inputs: the high-range fiber energy and the
off-diagonal Selberg bilinear form.
-/

example {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) {A B H : ℝ} (hAB : A ≤ B) :
    selbergShortDirichletGapSum N X A B H ≤
      (B - A) * (4 * H ^ 2 * (1 + Real.log (min N X : ℝ)) +
          ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
            (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
              selbergShortCollectedPairFiberEnergy N X k) +
        H ^ 2 * ∑ m ∈ Finset.Ioc 1 (N * X * X),
          ∑ n ∈ Finset.Ioc 1 (N * X * X),
            2 * ‖selbergShortDirichletCollectedCoeff N X m‖ *
              ‖selbergShortDirichletCollectedCoeff N X n‖ /
              |selbergShortDirichletCollectedFrequency m -
                selbergShortDirichletCollectedFrequency n| :=
  selbergShortDirichletGapSum_le_diagonal_add_offDiagonal hN hX hAB

#print axioms selbergShortDirichletGapSum_le_diagonal_add_offDiagonal

end HardyTheorem
