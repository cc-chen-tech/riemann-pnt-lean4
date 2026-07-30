import HardyTheorem.SelbergSqrtZetaCollectedWeightedEnergy

open Complex
open scoped BigOperators

namespace Test.SelbergSqrtZetaCollectedWeightedEnergyContract

open HardyTheorem

#check card_selbergShortDirichletTriples_le_sq
#check mul_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_sq_sq
#check sum_mul_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_mul_sq_sq
#check sum_mul_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_mul_pow_six

example {N X : ℕ} (hX : 2 ≤ X) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        (k : ℝ) *
          ‖selbergSqrtZetaShortDirichletCollectedCoeff N X k‖ ^ 2) ≤
      (N : ℝ) * (X : ℝ) ^ 6 :=
  sum_mul_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_mul_pow_six
    hX

end Test.SelbergSqrtZetaCollectedWeightedEnergyContract
