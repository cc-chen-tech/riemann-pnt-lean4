import PrimeNumberTheorem.ExceptionalZeroTargetDyadicOccupancy

open Complex

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check dynamicComplementZeroPacket_card_le_unitBucketMultiplicity
#check exists_dynamicComplementDyadicOccupancy_le_log
#check exists_rightHigherDyadic_fartherRight_or_gram_le_logOccupancy

#check
  (exists_dynamicComplementDyadicOccupancy_le_log :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Finset ℂ) (T : ℝ) (k : ℕ), 4 ≤ 2 ^ k →
        (dynamicComplementDyadicOccupancy S T k : ℝ) ≤
          C * (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)))

end VKEdgePiOverTwo
end PrimeNumberTheorem
