import HardyTheorem.SelbergShortHighRange

open scoped BigOperators

namespace Test.SelbergShortHighRangeContract

#check HardyTheorem.sum_normSq_selbergShortDirichletCollectedCoeff_highRange_eq_sharpSupport

example {N X : ℕ} (hX : 2 ≤ X) :
    (∑ k ∈ Finset.Ioc N (N * X * (X - 1)),
        Complex.normSq
          (HardyTheorem.selbergShortDirichletCollectedCoeff N X k)) =
      ∑ k ∈ Finset.Ioc N (N * (X - 1) * (X - 1)),
        Complex.normSq
          (HardyTheorem.selbergShortDirichletCollectedCoeff N X k) :=
  HardyTheorem.sum_normSq_selbergShortDirichletCollectedCoeff_highRange_eq_sharpSupport hX

#print axioms HardyTheorem.sum_normSq_selbergShortDirichletCollectedCoeff_highRange_eq_sharpSupport

end Test.SelbergShortHighRangeContract
