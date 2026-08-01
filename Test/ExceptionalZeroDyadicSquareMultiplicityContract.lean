import PrimeNumberTheorem.ExceptionalZeroDyadicSquareMultiplicity

open Complex Filter Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem

#check squareMultiplicityCapacity_le_max_mul_linearMultiplicityCapacity
#check
  (squareMultiplicityCapacity_sdiff_le :
    ∀ {α : Type*} [DecidableEq α] (R S : Finset α) (m w : α → ℝ),
      (∀ a ∈ R, 0 ≤ w a) →
      (∑ a ∈ R \ S, m a ^ 2 * w a) ≤ ∑ a ∈ R, m a ^ 2 * w a)
#check squareMultiplicityCapacity_sdiff_le
#check ExplicitFormulaAux.exists_analyticOrderNatAt_riemannZeta_le_log_im_of_nontrivialZero
#check actualZetaDyadicZeroBlock
#check actualZetaDyadicSquareReciprocalCapacityExcluding
#check actualZetaDyadicSquareReciprocalCapacityExcluding_le_linear
#check exists_actualZetaDyadicSquareReciprocalCapacityExcluding_le_log_linear

end PrimeNumberTheorem
