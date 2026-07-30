import PrimeNumberTheorem.VKEdgeHighZeroGaussianEnergy

open Filter
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check zeroReciprocalMultiplicityCoefficient
#check zeroOrdinateBucketGaussianEnergy

#check
  (zeroOrdinateBucketGaussianEnergy_le :
    ∀ (H N : ℕ) {m : ℝ}, 1 ≤ m →
      zeroOrdinateBucketGaussianEnergy H N m ≤
        MathlibAux.gaussianBucketSchurConstant *
          ∑ n ∈ Finset.Icc H N,
            zeroOrdinateUnitBucketCoefficientMass n ^ 2)

#check
  (eventually_zeroOrdinateBucketGaussianEnergy_lt :
    ∀ {eta : ℝ}, 0 < eta →
      ∀ᶠ H : ℕ in atTop,
        ∀ N : ℕ, H ≤ N →
          ∀ m : ℝ, 1 ≤ m →
            zeroOrdinateBucketGaussianEnergy H N m < eta)

end VKEdgePiOverTwo
end PrimeNumberTheorem
