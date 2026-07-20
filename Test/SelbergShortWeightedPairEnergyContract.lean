import HardyTheorem.SelbergShortWeightedPairEnergy

open Complex
open scoped BigOperators

namespace Test.SelbergShortWeightedPairEnergyContract

#check HardyTheorem.normSq_finset_sum_mul_le_sum_normSq_mul_sum_normSq
#check HardyTheorem.normSq_selbergShortDirichletCollectedCoeff_le_weightedPairEnergy

example {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g : ι → ℂ) :
    Complex.normSq (∑ i ∈ s, f i * g i) ≤
      (∑ i ∈ s, Complex.normSq (f i)) *
        ∑ i ∈ s, Complex.normSq (g i) :=
  HardyTheorem.normSq_finset_sum_mul_le_sum_normSq_mul_sum_normSq s f g

example (N X k : ℕ) :
    Complex.normSq
        (HardyTheorem.selbergShortDirichletCollectedCoeff N X k) ≤
      (∑ p ∈ HardyTheorem.selbergMollifiedDirichletPairs (N * X) X k,
          Complex.normSq
            ((HardyTheorem.selbergMollifiedDirichletCoeff N X p.1 : ℂ) *
              (Real.sqrt (p.1 : ℝ) : ℂ)⁻¹)) *
        ∑ p ∈ HardyTheorem.selbergMollifiedDirichletPairs (N * X) X k,
          Complex.normSq
            ((HardyTheorem.selbergMoebiusCoeff X p.2 : ℂ) *
              (Real.sqrt (p.2 : ℝ) : ℂ)⁻¹) :=
  HardyTheorem.normSq_selbergShortDirichletCollectedCoeff_le_weightedPairEnergy
    N X k

#print axioms HardyTheorem.normSq_finset_sum_mul_le_sum_normSq_mul_sum_normSq
#print axioms HardyTheorem.normSq_selbergShortDirichletCollectedCoeff_le_weightedPairEnergy

end Test.SelbergShortWeightedPairEnergyContract
