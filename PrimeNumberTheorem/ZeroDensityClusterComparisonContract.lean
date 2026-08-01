import PrimeNumberTheorem.ZeroDensityClusterComparison

namespace PrimeNumberTheorem

example {ρ : Type*} (cluster : Finset ρ)
    (realPart ordinate : ρ → ℝ) (sigma H : ℝ) :
    ∀ᶠ T in Filter.atTop,
      (localClusterLowerBound
        cluster realPart ordinate sigma T H : ℝ) ≤ T :=
  finite_localClusterLowerBound_eventually_le_diverging_upper
    cluster realPart ordinate sigma H tendsto_id

example {lower count upper : ℝ → ℝ}
    (hlower : ∀ᶠ T in Filter.atTop, lower T ≤ count T)
    (hupper : ∀ᶠ T in Filter.atTop, count T ≤ upper T)
    (hgap :
      Filter.Tendsto (fun T => lower T - upper T)
        Filter.atTop Filter.atTop) :
    False :=
  cluster_density_contradiction_of_gap_tendsto_atTop
    hlower hupper hgap

end PrimeNumberTheorem
