import PrimeNumberTheorem.ExceptionalZeroDyadicDirectL2

open Complex Filter
open scoped BigOperators

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check zeroOrdinateDyadicGaussianEnergy

#check
  (zeroOrdinateDyadicGaussianEnergy_le :
    ∀ (k : ℕ) {m : ℝ}, 1 ≤ m →
      zeroOrdinateDyadicGaussianEnergy k m ≤
        MathlibAux.gaussianBucketSchurConstant *
          ∑ n ∈ Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1),
            zeroOrdinateUnitBucketCoefficientMass n ^ 2)

end PrimeNumberTheorem.VKEdgePiOverTwo
