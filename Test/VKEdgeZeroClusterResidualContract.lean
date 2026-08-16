import PrimeNumberTheorem.VKEdgeZeroClusterResidual

open Complex MeasureTheory
open Filter
open PrimeNumberTheorem
open PrimeNumberTheorem.VKEdgePiOverTwo

namespace Test

#check
  (positiveZeroDensityResidualTopBandCluster :
    ℂ → ℝ → ℝ → ℝ → ℝ → Finset ℂ)

#check
  (positiveZeroDensityResidualLeftRemainder :
    ℂ → ℝ → ℝ → ℝ → ℝ → Finset ℂ)

#check
  (normalizedPositiveZeroDensityContributionOn :
    Finset ℂ → ℝ → ℝ → ℂ)

#check
  (@positiveZeroDensityResidualTopBandCluster_union_leftRemainder :
    ∀ (rho0 : ℂ) (beta sigma T delta : ℝ),
      positiveZeroDensityResidualTopBandCluster
          rho0 beta sigma T delta ∪
        positiveZeroDensityResidualLeftRemainder
          rho0 beta sigma T delta =
        positiveZeroDensityResidualFinset rho0 sigma T)

#check
  (@sum_order_positiveZeroDensityResidualTopBandCluster_le_count :
    ∀ (rho0 : ℂ) (beta sigma T delta : ℝ),
      (∑ rho ∈ positiveZeroDensityResidualTopBandCluster
          rho0 beta sigma T delta,
        analyticOrderNatAt riemannZeta rho) ≤
      ZeroDensity.zeroDensityCount sigma T)

#check
  (@normalizedPositiveZeroDensityResidualContribution_eq_cluster_add_left :
    ∀ (rho0 : ℂ) (beta sigma T delta y : ℝ),
      normalizedPositiveZeroDensityResidualContribution
          rho0 beta sigma T y =
        normalizedPositiveZeroDensityContributionOn
            (positiveZeroDensityResidualTopBandCluster
              rho0 beta sigma T delta) beta y +
          normalizedPositiveZeroDensityContributionOn
            (positiveZeroDensityResidualLeftRemainder
              rho0 beta sigma T delta) beta y)

#check
  (@norm_normalizedPositiveZeroDensityLeftRemainder_le_count :
    ∀ {rho0 : ℂ} {beta sigma T delta y : ℝ},
      1 / 2 ≤ sigma →
      0 ≤ y →
      ‖normalizedPositiveZeroDensityContributionOn
          (positiveZeroDensityResidualLeftRemainder
            rho0 beta sigma T delta) beta y‖ ≤
        2 * Real.exp (-delta * y) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ))

#check
  (@integral_normSq_normalizedPositiveZeroDensityLeftRemainder_le_count_sq :
    ∀ {rho0 : ℂ} {beta sigma T delta a b : ℝ},
      1 / 2 ≤ sigma →
      0 ≤ delta →
      0 ≤ a →
      a ≤ b →
      (∫ y in Set.Icc a b,
        Complex.normSq
          (normalizedPositiveZeroDensityContributionOn
            (positiveZeroDensityResidualLeftRemainder
              rho0 beta sigma T delta) beta y)) ≤
        4 * (b - a) * Real.exp (-2 * delta * a) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ^ 2)

#check
  (@eventually_integral_normSq_positiveZeroDensityLeftRemainder_le_of_carlson :
    ∀ {rho0 : ℂ} {beta sigma tau eta delta L : ℝ},
      1 / 2 < sigma →
      sigma < 1 →
      0 < tau →
      0 < eta →
      0 ≤ delta →
      0 ≤ L →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ a : ℝ in atTop,
          (∫ y in Set.Icc a (a + L),
            Complex.normSq
              (normalizedPositiveZeroDensityContributionOn
                (positiveZeroDensityResidualLeftRemainder
                  rho0 beta sigma (Real.exp (tau * a)) delta)
                beta y)) ≤
            4 * L * C ^ 2 *
              Real.exp
                (-2 *
                  (delta -
                    (4 * sigma * (1 - sigma) * tau + eta)) * a))

#check
  (@integral_normSq_normalizedPositiveResidual_ge_half_cluster_sub_left :
    ∀ (rho0 : ℂ) (beta sigma T delta a b : ℝ),
      (1 / 2 : ℝ) *
          (∫ y in Set.Icc a b,
            Complex.normSq
              (normalizedPositiveZeroDensityContributionOn
                (positiveZeroDensityResidualTopBandCluster
                  rho0 beta sigma T delta) beta y)) -
        (∫ y in Set.Icc a b,
          Complex.normSq
            (normalizedPositiveZeroDensityContributionOn
              (positiveZeroDensityResidualLeftRemainder
                rho0 beta sigma T delta) beta y)) ≤
      ∫ y in Set.Icc a b,
        Complex.normSq
          (normalizedPositiveZeroDensityResidualContribution
            rho0 beta sigma T y))

end Test
