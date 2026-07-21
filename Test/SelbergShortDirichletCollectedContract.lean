import HardyTheorem.SelbergShortDirichletCollected

open Complex

namespace Test.SelbergShortDirichletCollectedContract

#check HardyTheorem.selbergShortDirichletCollectedSupport
#check HardyTheorem.selbergShortDirichletTriples
#check HardyTheorem.selbergShortDirichletCollectedCoeff
#check HardyTheorem.selbergShortDirichletCollectedFrequency
#check HardyTheorem.selbergShortDirichletCollectedPolynomial
#check HardyTheorem.selbergShortDirichletTriplePolynomial_eq_collectedPolynomial
#check HardyTheorem.selbergShortDirichletCollectedFrequency_injective_on_support
#check HardyTheorem.selbergShortDirichletCollectedCoeff_one
#check HardyTheorem.selbergShortDirichletCollectedPolynomial_sub_one_eq

example (N X : ℕ) (t : ℝ) :
    HardyTheorem.selbergShortDirichletTriplePolynomial N X t =
      HardyTheorem.selbergShortDirichletCollectedPolynomial N X t :=
  HardyTheorem.selbergShortDirichletTriplePolynomial_eq_collectedPolynomial N X t

example {N X j k : ℕ}
    (hj : j ∈ HardyTheorem.selbergShortDirichletCollectedSupport N X)
    (hk : k ∈ HardyTheorem.selbergShortDirichletCollectedSupport N X)
    (hfreq : HardyTheorem.selbergShortDirichletCollectedFrequency j =
      HardyTheorem.selbergShortDirichletCollectedFrequency k) :
    j = k :=
  HardyTheorem.selbergShortDirichletCollectedFrequency_injective_on_support
    hj hk hfreq

example {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    HardyTheorem.selbergShortDirichletCollectedCoeff N X 1 = 1 :=
  HardyTheorem.selbergShortDirichletCollectedCoeff_one hN hX

#print axioms HardyTheorem.selbergShortDirichletTriplePolynomial_eq_collectedPolynomial
#print axioms HardyTheorem.selbergShortDirichletCollectedFrequency_injective_on_support
#print axioms HardyTheorem.selbergShortDirichletCollectedCoeff_one
#print axioms HardyTheorem.selbergShortDirichletCollectedPolynomial_sub_one_eq

end Test.SelbergShortDirichletCollectedContract
