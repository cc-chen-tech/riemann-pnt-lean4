import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeExponentCriterion

/-!
# Contract for the target-amplitude exponent criterion
-/

namespace PrimeNumberTheorem

#check targetAmplitudePintzCarlsonExponent
#check targetAmplitudePintzCarlsonExponent_neg_iff
#check targetAmplitudePintzCarlsonExponent_nonneg_of_target_le_strip
#check not_targetAmplitudePintzCarlsonExponent_neg_of_target_le_strip
#check carlsonPolynomialHeightDensityExponent
#check polynomialHeight_targetAmplitudeExponent_neg_iff
#check exists_polynomialHeight_targetAmplitude_decay_iff

example {beta sigma A : ℝ} (hslope : 0 < A * (1 - sigma)) :
    (∃ alpha : ℝ,
        1 - beta < alpha ∧
        targetAmplitudePintzCarlsonExponent beta sigma
          (carlsonPolynomialHeightDensityExponent alpha A sigma) < 0) ↔
      (1 - beta) * (A * (1 - sigma)) < beta - sigma :=
  exists_polynomialHeight_targetAmplitude_decay_iff hslope

end PrimeNumberTheorem
