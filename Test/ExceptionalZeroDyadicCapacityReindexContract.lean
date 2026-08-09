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

#check
  (exists_dynamicComplementDyadicOccupancy_le_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset ℂ) (T : ℝ) (k : ℕ),
      2 ≤ k →
      (dynamicComplementDyadicOccupancy S T k : ℝ) ≤
        C * (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)))

#check
  (low_actualZetaDyadicZero_mem_rightHigherExclusionSet :
    ∀ (S : Finset ℂ) {Told sigma T : ℝ} {k : ℕ} {rho : ℂ},
      rho ∈ actualZetaDyadicZeroBlock k →
      |rho.im| < 4 → 4 ≤ Told → (2 : ℝ) ^ (k + 1) ≤ T →
      rho ∈ rightHigherExclusionSet S Told sigma T)

#check
  (exists_rightHigherDyadicSquareCapacity_le_log_linear :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (S : Finset ℂ) (Told sigma T : ℝ) (k : ℕ),
        4 ≤ Told → (2 : ℝ) ^ (k + 1) ≤ T →
        actualZetaDyadicSquareReciprocalCapacityExcluding k
            (rightHigherExclusionSet S Told sigma T) ≤
          (B * (1 + Real.log ((2 : ℝ) ^ (k + 1) + 6))) *
            actualZetaDyadicLinearReciprocalCapacityExcluding k
              (rightHigherExclusionSet S Told sigma T))

#check
  (rightHigherActualZetaDyadicLinearCapacity_le_zeroDensityCount :
    ∀ (S : Finset ℂ) {Told sigma T : ℝ} (k : ℕ),
      0 ≤ Told → (2 : ℝ) ^ (k + 1) ≤ T →
      actualZetaDyadicLinearReciprocalCapacityExcluding k
          (rightHigherExclusionSet S Told sigma T) ≤
        (((2 : ℝ) ^ k) ^ 2)⁻¹ *
          (ZeroDensity.zeroDensityCount sigma ((2 : ℝ) ^ (k + 1)) : ℝ))

end PrimeNumberTheorem.VKEdgePiOverTwo
