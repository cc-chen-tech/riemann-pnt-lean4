import PrimeNumberTheorem.ZeroDensityClusterComparisonGrowth

namespace PrimeNumberTheorem

example (density : ZeroDensityCountingUpperInterface)
    (sigma H : ℝ) :
    ∀ᶠ T in Filter.atTop,
      density.N sigma (T + H) ≤ density.upper sigma (T + H) :=
  (density.shiftedCertificate sigma H).eventually_upper_shifted

example {ρ : Type*} (cluster : Finset ρ)
    (realPart ordinate : ρ → ℝ) (sigma H : ℝ) :
    ¬ Filter.Tendsto
        (fun T =>
          (localClusterLowerBound
            cluster realPart ordinate sigma T H : ℝ) - T)
        Filter.atTop Filter.atTop :=
  finiteCluster_gap_not_tendsto_atTop
    cluster realPart ordinate sigma H tendsto_id

end PrimeNumberTheorem
