import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicLowDyadicCapacity

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem

noncomputable section

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    (B x tau : ℝ) (N n : ℕ) :
    actualCubicLowDyadicL2BlockCapacityMajorant certificate B x tau N n =
      if n < N then
        actualCubicDyadicStripSquareCapacity x sigma tau n
      else
        actualCubicCarlsonDyadicLogFifthMajorant
          (actualCubicCarlsonUniformCoefficient certificate B * x ^ (2 * tau))
          sigma n := rfl

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    (B beta tau gamma : ℝ) (N : ℕ) (m : ℕ) :
    actualCubicNormalizedLowDyadicL2CapacityMajorant
        certificate B beta tau gamma N m =
      (m : ℝ) ^ (-2 * beta) *
        ∑ n ∈ Finset.range (actualCubicDyadicPolynomialCut gamma m + 1),
          actualCubicLowDyadicL2BlockCapacityMajorant
            certificate B (m : ℝ) tau N n := rfl

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    (B x tau : ℝ) (N n : ℕ) (hn : n < N) :
    actualCubicLowDyadicL2BlockCapacityMajorant certificate B x tau N n =
      actualCubicDyadicStripSquareCapacity x sigma tau n :=
  actualCubicLowDyadicL2BlockCapacityMajorant_eq_capacity_of_lt
    certificate B x tau N n hn

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    (B x tau : ℝ) (N n : ℕ) (hn : N ≤ n) :
    actualCubicLowDyadicL2BlockCapacityMajorant certificate B x tau N n =
      actualCubicCarlsonDyadicLogFifthMajorant
        (actualCubicCarlsonUniformCoefficient certificate B * x ^ (2 * tau))
        sigma n :=
  actualCubicLowDyadicL2BlockCapacityMajorant_eq_logFifth_of_ge
    certificate B x tau N n hn

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N : ℕ,
      ∀ (beta tau gamma : ℝ) (S : Finset ℂ) (m : ℕ),
        1 ≤ m →
        actualCubicNormalizedSmoothedStripEnergyUpTo
            beta sigma tau gamma S m ≤
          actualCubicNormalizedLowDyadicL2CapacityMajorant
            certificate B beta tau gamma N m :=
  exists_actualCubicNormalizedSmoothedStripEnergyUpTo_le_lowDyadicL2CapacityMajorant
    certificate

end

end PrimeNumberTheorem
