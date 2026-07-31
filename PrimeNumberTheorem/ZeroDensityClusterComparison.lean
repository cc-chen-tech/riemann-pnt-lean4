import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlson

/-!
# Local cluster lower bounds versus zero-density upper bounds

This file contains only the abstract counting and arithmetic comparison layer.
It does not assert a concrete Guth--Maynard estimate and does not draw an RH
conclusion.
-/

namespace PrimeNumberTheorem

/--
The number of members of a fixed finite cluster lying to the right of `sigma`
and with ordinate in the local window `[T, T + H]`.
-/
noncomputable def localClusterLowerBound
    {ρ : Type*} (cluster : Finset ρ)
    (realPart ordinate : ρ → ℝ)
    (sigma T H : ℝ) : ℕ := by
  classical
  exact
    (cluster.filter fun rho =>
      sigma ≤ realPart rho ∧
      T ≤ ordinate rho ∧ ordinate rho ≤ T + H).card

/-- A fixed finite cluster gives a uniformly bounded local lower count. -/
theorem localClusterLowerBound_le_card
    {ρ : Type*} (cluster : Finset ρ)
    (realPart ordinate : ρ → ℝ)
    (sigma T H : ℝ) :
    localClusterLowerBound cluster realPart ordinate sigma T H ≤
      cluster.card := by
  classical
  unfold localClusterLowerBound
  exact Finset.card_le_card (Finset.filter_subset _ _)

/--
Abstract Carlson/Guth--Maynard-style interface.  `N sigma T` is the ambient
zero count and `upper sigma T` is an eventual majorant.

Supplying a concrete theorem through this interface is separate future work.
-/
structure ZeroDensityCountingUpperInterface where
  N : ℝ → ℝ → ℝ
  upper : ℝ → ℝ → ℝ
  eventually_upper :
    ∀ sigma,
      ∀ᶠ T in Filter.atTop, N sigma T ≤ upper sigma T

/--
Shifted-window form of the abstract zero-density input.  It is stated as a
separate certificate so no unproved monotonicity or translation property is
hidden in the comparison layer.
-/
structure ShiftedZeroDensityUpperCertificate
    (density : ZeroDensityCountingUpperInterface)
    (sigma H : ℝ) : Prop where
  eventually_upper_shifted :
    ∀ᶠ T in Filter.atTop,
      density.N sigma (T + H) ≤ density.upper sigma (T + H)

/--
If an upper majorant diverges, every fixed finite cluster count is eventually
below it.  This is the precise reason a single zero or finite cluster cannot
contradict a growing density upper bound.
-/
theorem finite_localClusterLowerBound_eventually_le_diverging_upper
    {ρ : Type*} (cluster : Finset ρ)
    (realPart ordinate : ρ → ℝ)
    (sigma H : ℝ) {upper : ℝ → ℝ}
    (hupper :
      Filter.Tendsto upper Filter.atTop Filter.atTop) :
    ∀ᶠ T in Filter.atTop,
      (localClusterLowerBound
        cluster realPart ordinate sigma T H : ℝ) ≤ upper T := by
  have hcard :
      ∀ᶠ T in Filter.atTop, (cluster.card : ℝ) ≤ upper T :=
    (Filter.tendsto_atTop.1 hupper) (cluster.card : ℝ)
  filter_upwards [hcard] with T hT
  have hlocal :
      (localClusterLowerBound
        cluster realPart ordinate sigma T H : ℝ) ≤
          (cluster.card : ℝ) := by
    exact_mod_cast
      localClusterLowerBound_le_card
        cluster realPart ordinate sigma T H
  exact hlocal.trans hT

/--
An asymptotically diverging gap is a sufficient quantitative growth condition
for eventual strict separation of lower and upper bounds.
-/
theorem eventually_upper_lt_lower_of_gap_tendsto_atTop
    {lower upper : ℝ → ℝ}
    (hgap :
      Filter.Tendsto (fun T => lower T - upper T)
        Filter.atTop Filter.atTop) :
    ∀ᶠ T in Filter.atTop, upper T < lower T := by
  have hpositive :
      ∀ᶠ T in Filter.atTop, 1 ≤ lower T - upper T :=
    (Filter.tendsto_atTop.1 hgap) 1
  filter_upwards [hpositive] with T hT
  linarith

/--
The minimal arithmetic contradiction: an eventual lower bound on a count, an
eventual upper bound on the same count, and eventual strict separation cannot
coexist.
-/
theorem false_of_eventually_lower_count_upper_separated
    {lower count upper : ℝ → ℝ}
    (hlower :
      ∀ᶠ T in Filter.atTop, lower T ≤ count T)
    (hupper :
      ∀ᶠ T in Filter.atTop, count T ≤ upper T)
    (hseparated :
      ∀ᶠ T in Filter.atTop, upper T < lower T) :
    False := by
  rcases Filter.eventually_atTop.1 hlower with ⟨A, hA⟩
  rcases Filter.eventually_atTop.1 hupper with ⟨B, hB⟩
  rcases Filter.eventually_atTop.1 hseparated with ⟨C, hC⟩
  let T := max A (max B C)
  have hAT : A ≤ T := le_max_left _ _
  have hBT : B ≤ T :=
    (le_max_left B C).trans (le_max_right A (max B C))
  have hCT : C ≤ T :=
    (le_max_right B C).trans (le_max_right A (max B C))
  have hLowerCount := hA T hAT
  have hCountUpper := hB T hBT
  have hUpperLower := hC T hCT
  linarith

/--
Growth-rate contradiction criterion.  The cluster lower count must dominate
the zero-density upper majorant by an eventually positive, here diverging, gap.
-/
theorem cluster_density_contradiction_of_gap_tendsto_atTop
    {lower count upper : ℝ → ℝ}
    (hlower :
      ∀ᶠ T in Filter.atTop, lower T ≤ count T)
    (hupper :
      ∀ᶠ T in Filter.atTop, count T ≤ upper T)
    (hgap :
      Filter.Tendsto (fun T => lower T - upper T)
        Filter.atTop Filter.atTop) :
    False :=
  false_of_eventually_lower_count_upper_separated
    hlower hupper
      (eventually_upper_lt_lower_of_gap_tendsto_atTop hgap)

end PrimeNumberTheorem
