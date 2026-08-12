import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicLowSummedGaussianL2

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem

example (beta sigma tau gamma : ℝ) (S : Finset ℂ)
    (t width : ℝ) (m : ℕ) :
    actualCubicNormalizedLowDyadicGaussianGramExcluding
        beta sigma tau gamma S t width m =
      ∑ n ∈ Finset.range (actualCubicDyadicPolynomialCut gamma m + 1),
        actualCubicDyadicStripGaussianGramExcluding
          (m : ℝ) beta sigma tau n S t width := rfl

example {beta sigma tau gamma t width : ℝ} {S : Finset ℂ}
    {m occupancy : ℕ}
    (ht : 0 ≤ t) (hwidth : 1 ≤ width)
    (hoccupancy :
      ∀ n ∈ Finset.range (actualCubicDyadicPolynomialCut gamma m + 1),
        ∀ q ∈ Finset.image actualCubicDyadicUnitBucket
            (actualCarlsonDyadicZeroStrip sigma tau n \ S),
          (Finset.filter
            (fun rho => actualCubicDyadicUnitBucket rho = q)
            (actualCarlsonDyadicZeroStrip sigma tau n \ S)).card ≤
              occupancy + 1) :
    actualCubicNormalizedLowDyadicGaussianGramExcluding
        beta sigma tau gamma S t width m ≤
      MathlibAux.gaussianBucketSchurConstant * (occupancy + 1 : ℕ) *
        actualCubicNormalizedSmoothedStripEnergyUpTo
          beta sigma tau gamma S m := by
  exact actualCubicNormalizedLowDyadicGaussianGramExcluding_le_occupancy_mul_energy
    ht hwidth hoccupancy

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N : ℕ,
      ∀ (beta tau gamma : ℝ) (S : Finset ℂ)
        (t width : ℝ) (occupancy m : ℕ),
        1 ≤ m → 0 ≤ t → 1 ≤ width →
        (∀ n ∈ Finset.range (actualCubicDyadicPolynomialCut gamma m + 1),
          ∀ q ∈ Finset.image actualCubicDyadicUnitBucket
              (actualCarlsonDyadicZeroStrip sigma tau n \ S),
            (Finset.filter
              (fun rho => actualCubicDyadicUnitBucket rho = q)
              (actualCarlsonDyadicZeroStrip sigma tau n \ S)).card ≤
                occupancy + 1) →
        actualCubicNormalizedLowDyadicGaussianGramExcluding
            beta sigma tau gamma S t width m ≤
          MathlibAux.gaussianBucketSchurConstant * (occupancy + 1 : ℕ) *
            actualCubicNormalizedLowDyadicL2CapacityMajorant
              certificate B beta tau gamma N m := by
  exact
    exists_actualCubicNormalizedLowDyadicGaussianGramExcluding_le_lowDyadicL2CapacityMajorant
      certificate

end PrimeNumberTheorem
