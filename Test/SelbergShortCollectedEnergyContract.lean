import HardyTheorem.SelbergShortCollectedEnergy

open Complex
open scoped BigOperators

namespace Test.SelbergShortCollectedEnergyContract

#check HardyTheorem.selbergShortCollectedPairTerm
#check HardyTheorem.selbergShortDirichletCollectedCoeff_eq_pairSum
#check HardyTheorem.normSq_selbergShortDirichletCollectedCoeff_le_pairFiber
#check HardyTheorem.sum_normSq_selbergShortDirichletCollectedCoeff_le_pairFiberEnergy

example (N X k : ℕ) :
    HardyTheorem.selbergShortDirichletCollectedCoeff N X k =
      ∑ p ∈ HardyTheorem.selbergMollifiedDirichletPairs (N * X) X k,
        HardyTheorem.selbergShortCollectedPairTerm N X k p :=
  HardyTheorem.selbergShortDirichletCollectedCoeff_eq_pairSum N X k

example (N X k : ℕ) :
    Complex.normSq
        (HardyTheorem.selbergShortDirichletCollectedCoeff N X k) ≤
      (HardyTheorem.selbergMollifiedDirichletPairs (N * X) X k).card *
        ∑ p ∈ HardyTheorem.selbergMollifiedDirichletPairs (N * X) X k,
          Complex.normSq
            (HardyTheorem.selbergShortCollectedPairTerm N X k p) :=
  HardyTheorem.normSq_selbergShortDirichletCollectedCoeff_le_pairFiber N X k

example (N X : ℕ) :
    (∑ k ∈ HardyTheorem.selbergShortDirichletCollectedSupport N X,
        Complex.normSq
          (HardyTheorem.selbergShortDirichletCollectedCoeff N X k)) ≤
      ∑ k ∈ HardyTheorem.selbergShortDirichletCollectedSupport N X,
        (HardyTheorem.selbergMollifiedDirichletPairs (N * X) X k).card *
          ∑ p ∈ HardyTheorem.selbergMollifiedDirichletPairs (N * X) X k,
            Complex.normSq
              (HardyTheorem.selbergShortCollectedPairTerm N X k p) :=
  HardyTheorem.sum_normSq_selbergShortDirichletCollectedCoeff_le_pairFiberEnergy N X

#print axioms HardyTheorem.selbergShortDirichletCollectedCoeff_eq_pairSum
#print axioms HardyTheorem.normSq_selbergShortDirichletCollectedCoeff_le_pairFiber
#print axioms HardyTheorem.sum_normSq_selbergShortDirichletCollectedCoeff_le_pairFiberEnergy

end Test.SelbergShortCollectedEnergyContract
