import HardyTheorem.SelbergShortCompleteRangeArithmetic

open scoped BigOperators

namespace HardyTheorem

#check selbergShortCompleteRangePairs
#check selbergShortDirichletTriples_eq_completeRangePairs_image
#check selbergShortCollectedDirichletConvolution_eq_completeRange

example {N X k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    selbergShortCollectedDirichletConvolution N X k =
      ∑ p ∈ selbergShortCompleteRangePairs X k,
        selbergMoebiusCoeff X p.1 * selbergMoebiusCoeff X p.2 := by
  exact selbergShortCollectedDirichletConvolution_eq_completeRange hk1 hkN

#print axioms selbergShortDirichletTriples_eq_completeRangePairs_image
#print axioms selbergShortCollectedDirichletConvolution_eq_completeRange

end HardyTheorem
