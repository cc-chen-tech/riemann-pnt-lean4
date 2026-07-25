import PrimeNumberTheorem.ZeroDensityClusterComparison

/-!
# Shifted zero-density bounds and growing cluster families

This file turns the abstract comparison arithmetic into a theorem chain for a
fixed local-window length `H`.  It also proves that bounded lower counts,
including every fixed finite cluster, cannot satisfy the required diverging-gap
condition.
-/

namespace PrimeNumberTheorem

/-- Translation by a fixed real number preserves divergence to `+infinity`. -/
theorem tendsto_add_const_atTop (H : ℝ) :
    Filter.Tendsto (fun T : ℝ => T + H)
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  exact Filter.eventually_atTop.2
    ⟨b - H, by
      intro T hT
      linarith⟩

/--
Every global eventual zero-density upper bound automatically applies at the
shifted endpoint `T + H`.
-/
def ZeroDensityCountingUpperInterface.shiftedCertificate
    (density : ZeroDensityCountingUpperInterface)
    (sigma H : ℝ) :
    ShiftedZeroDensityUpperCertificate density sigma H where
  eventually_upper_shifted :=
    (tendsto_add_const_atTop H).eventually
      (density.eventually_upper sigma)

/--
A genuinely growing family of local clusters must provide a lower-count
function and prove that its distinct members inject into the ambient count
`N sigma (T + H)`.

This certificate is not supplied by repeated anti-cancellation witnesses from
one fixed cluster.
-/
structure GrowingLocalClusterLowerCertificate
    (density : ZeroDensityCountingUpperInterface)
    (sigma H : ℝ) where
  lower : ℝ → ℝ
  eventually_forces_count :
    ∀ᶠ T in Filter.atTop,
      lower T ≤ density.N sigma (T + H)

/--
The full abstract contradiction for a growing local cluster family versus an
eventual zero-density majorant.
-/
theorem GrowingLocalClusterLowerCertificate.density_contradiction_of_gap
    {density : ZeroDensityCountingUpperInterface}
    {sigma H : ℝ}
    (clusterFamily :
      GrowingLocalClusterLowerCertificate density sigma H)
    (hgap :
      Filter.Tendsto
        (fun T =>
          clusterFamily.lower T - density.upper sigma (T + H))
        Filter.atTop Filter.atTop) :
    False :=
  cluster_density_contradiction_of_gap_tendsto_atTop
    clusterFamily.eventually_forces_count
    (density.shiftedCertificate sigma H).eventually_upper_shifted
    hgap

/--
No uniformly bounded lower count can outgrow a majorant tending to infinity by
a diverging additive gap.
-/
theorem bounded_lower_sub_diverging_upper_not_tendsto_atTop
    {lower upper : ℝ → ℝ} (bound : ℝ)
    (hlower : ∀ T, lower T ≤ bound)
    (hupper :
      Filter.Tendsto upper Filter.atTop Filter.atTop) :
    ¬ Filter.Tendsto (fun T => lower T - upper T)
        Filter.atTop Filter.atTop := by
  intro hgap
  have hgapEventually :
      ∀ᶠ T in Filter.atTop, 1 ≤ lower T - upper T :=
    (Filter.tendsto_atTop.1 hgap) 1
  have hupperEventually :
      ∀ᶠ T in Filter.atTop, bound ≤ upper T :=
    (Filter.tendsto_atTop.1 hupper) bound
  rcases Filter.eventually_atTop.1 hgapEventually with ⟨A, hA⟩
  rcases Filter.eventually_atTop.1 hupperEventually with ⟨B, hB⟩
  let T := max A B
  have hAT : A ≤ T := le_max_left _ _
  have hBT : B ≤ T := le_max_right _ _
  have hGap := hA T hAT
  have hUpper := hB T hBT
  have hLower := hlower T
  linarith

/--
A fixed finite cluster cannot satisfy the growth premise needed to contradict
any density upper majorant tending to infinity.
-/
theorem finiteCluster_gap_not_tendsto_atTop
    {ρ : Type*} (cluster : Finset ρ)
    (realPart ordinate : ρ → ℝ)
    (sigma H : ℝ) {upper : ℝ → ℝ}
    (hupper :
      Filter.Tendsto upper Filter.atTop Filter.atTop) :
    ¬ Filter.Tendsto
        (fun T =>
          (localClusterLowerBound
            cluster realPart ordinate sigma T H : ℝ) - upper T)
        Filter.atTop Filter.atTop := by
  apply bounded_lower_sub_diverging_upper_not_tendsto_atTop
    (cluster.card : ℝ)
  · intro T
    exact_mod_cast
      localClusterLowerBound_le_card
        cluster realPart ordinate sigma T H
  · exact hupper

end PrimeNumberTheorem
