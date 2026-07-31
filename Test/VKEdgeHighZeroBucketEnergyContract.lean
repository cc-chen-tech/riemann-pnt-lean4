import PrimeNumberTheorem.VKEdgeHighZeroBucketEnergy

open Filter
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check zeroOrdinateUnitBucket
#check zeroOrdinateUnitBucketMultiplicity
#check zeroOrdinateUnitBucketCoefficientMass

#check
  (exists_zeroOrdinateUnitBucketMultiplicity_le_log :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, 4 ≤ n →
        zeroOrdinateUnitBucketMultiplicity n ≤
          C * (1 + Real.log (n + 7)))

#check
  (exists_zeroOrdinateUnitBucketCoefficientMass_le_log_div :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, 4 ≤ n →
        zeroOrdinateUnitBucketCoefficientMass n ≤
          C * (1 + Real.log (n + 7)) / n)

#check
  (summable_sq_zeroOrdinateUnitBucketCoefficientMass :
    Summable (fun n : ℕ =>
      zeroOrdinateUnitBucketCoefficientMass n ^ 2))

#check
  (eventually_sum_Icc_sq_zeroOrdinateUnitBucketCoefficientMass_lt :
    ∀ {eta : ℝ}, 0 < eta →
      ∀ᶠ H : ℕ in atTop,
        ∀ N : ℕ, H ≤ N →
          (∑ n ∈ Finset.Icc H N,
            zeroOrdinateUnitBucketCoefficientMass n ^ 2) < eta)

end VKEdgePiOverTwo
end PrimeNumberTheorem
