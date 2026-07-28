import PrimeNumberTheorem.VKEdgeZeroDensityResidualL2

open Complex MeasureTheory
open Filter
open PrimeNumberTheorem
open PrimeNumberTheorem.VKEdgePiOverTwo

namespace Test

#check
  (positiveZeroDensityResidualFinset :
    ℂ → ℝ → ℝ → Finset ℂ)

#check
  (normalizedPositiveZeroDensityResidualContribution :
    ℂ → ℝ → ℝ → ℝ → ℝ → ℂ)

#check
  (@norm_normalizedPositiveZeroDensityResidualContribution_le_count :
    ∀ {rho0 : ℂ} {beta sigma T delta y : ℝ},
      1 / 2 ≤ sigma →
      0 ≤ y →
      (∀ rho ∈ positiveZeroDensityResidualFinset rho0 sigma T,
        rho.re ≤ beta - delta) →
      ‖normalizedPositiveZeroDensityResidualContribution
          rho0 beta sigma T y‖ ≤
        2 * Real.exp (-delta * y) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ))

#check
  (@integral_normSq_normalizedPositiveZeroDensityResidualContribution_le_count_sq :
    ∀ {rho0 : ℂ} {beta sigma T delta a b : ℝ},
      1 / 2 ≤ sigma →
      0 ≤ delta →
      0 ≤ a →
      a ≤ b →
      (∀ rho ∈ positiveZeroDensityResidualFinset rho0 sigma T,
        rho.re ≤ beta - delta) →
      (∫ y in Set.Icc a b,
        Complex.normSq
          (normalizedPositiveZeroDensityResidualContribution
            rho0 beta sigma T y)) ≤
        4 * (b - a) * Real.exp (-2 * delta * a) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ^ 2)

#check
  (@integral_normSq_normalizedPositiveZeroDensityResidualContribution_le_of_count_exp :
    ∀ {rho0 : ℂ} {beta sigma T delta a b C kappa : ℝ},
      1 / 2 ≤ sigma →
      0 ≤ delta →
      0 ≤ a →
      a ≤ b →
      (∀ rho ∈ positiveZeroDensityResidualFinset rho0 sigma T,
        rho.re ≤ beta - delta) →
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        C * Real.exp (kappa * a) →
      (∫ y in Set.Icc a b,
        Complex.normSq
          (normalizedPositiveZeroDensityResidualContribution
            rho0 beta sigma T y)) ≤
        4 * (b - a) * C ^ 2 *
          Real.exp (-2 * (delta - kappa) * a))

#check
  (@eventually_zeroDensityCount_exp_height_le_of_carlson :
    ∀ {sigma tau eta : ℝ},
      1 / 2 < sigma →
      sigma < 1 →
      0 < tau →
      0 < eta →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ a : ℝ in atTop,
          (ZeroDensity.zeroDensityCount sigma
              (Real.exp (tau * a)) : ℝ) ≤
            C * Real.exp
              ((4 * sigma * (1 - sigma) * tau + eta) * a))

#check
  (@eventually_integral_normSq_positiveZeroDensityResidual_le_of_carlson :
    ∀ {rho0 : ℂ} {beta sigma tau eta delta L : ℝ},
      1 / 2 < sigma →
      sigma < 1 →
      0 < tau →
      0 < eta →
      0 ≤ delta →
      0 ≤ L →
      (∀ᶠ a : ℝ in atTop,
        ∀ rho ∈ positiveZeroDensityResidualFinset
            rho0 sigma (Real.exp (tau * a)),
          rho.re ≤ beta - delta) →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ a : ℝ in atTop,
          (∫ y in Set.Icc a (a + L),
            Complex.normSq
              (normalizedPositiveZeroDensityResidualContribution
                rho0 beta sigma (Real.exp (tau * a)) y)) ≤
            4 * L * C ^ 2 *
              Real.exp
                (-2 *
                  (delta -
                    (4 * sigma * (1 - sigma) * tau + eta)) * a))

#check
  (@carlsonResidualDecayRate_pos :
    ∀ {sigma tau eta delta : ℝ},
      4 * sigma * (1 - sigma) * tau + eta < delta →
      0 < delta - (4 * sigma * (1 - sigma) * tau + eta))

#check
  (@exists_exponentialTruncationScale_iff :
    ∀ {beta sigma eta delta : ℝ},
      0 < 4 * sigma * (1 - sigma) →
      ((∃ tau : ℝ,
        1 - beta < tau ∧
          4 * sigma * (1 - sigma) * tau + eta < delta) ↔
        4 * sigma * (1 - sigma) * (1 - beta) + eta < delta))

#check
  (@no_exponentialTruncationScale_of_gap_le :
    ∀ {beta sigma eta delta : ℝ},
      0 < 4 * sigma * (1 - sigma) →
      delta ≤ 4 * sigma * (1 - sigma) * (1 - beta) + eta →
      ¬ ∃ tau : ℝ,
        1 - beta < tau ∧
          4 * sigma * (1 - sigma) * tau + eta < delta)

end Test
