import PrimeNumberTheorem.ExceptionalZeroDyadicCapacityReindex

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check dynamicComplementDyadicLinearReciprocalCapacity

#check
  (dynamicComplementZeroPacket_eq_zeroOrdinateUnitBucket_sdiff_of_dyadic :
    ∀ (S : Finset ℂ) {T : ℝ} {k n : ℕ},
      n ∈ dyadicUnitBucketIndexSet k →
      (2 : ℝ) ^ (k + 1) ≤ T →
      dynamicComplementZeroPacket S T n = zeroOrdinateUnitBucket n \ S)

#check
  (dynamicComplementDyadicSquareReciprocalCapacity_eq_actual :
    ∀ (S : Finset ℂ) {T : ℝ} (k : ℕ),
      (2 : ℝ) ^ (k + 1) ≤ T →
      dynamicComplementDyadicSquareReciprocalCapacity S T k =
        actualZetaDyadicSquareReciprocalCapacityExcluding k S)

#check
  (dynamicComplementDyadicLinearReciprocalCapacity_eq_actual :
    ∀ (S : Finset ℂ) {T : ℝ} (k : ℕ),
      (2 : ℝ) ^ (k + 1) ≤ T →
      dynamicComplementDyadicLinearReciprocalCapacity S T k =
        actualZetaDyadicLinearReciprocalCapacityExcluding k S)

end PrimeNumberTheorem.VKEdgePiOverTwo
