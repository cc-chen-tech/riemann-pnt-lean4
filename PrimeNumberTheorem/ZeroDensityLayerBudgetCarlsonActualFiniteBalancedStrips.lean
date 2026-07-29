import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualBalancedTwoHeightTransfer

/-!
# Finite families of balanced actual Carlson strips

Each real-part strip may use its own Carlson threshold and upper endpoint,
while sharing the outer polynomial height.  Pairwise disjointness turns the
finite sum of strip masses into the mass of their actual union.

No claim is made that this union contains every positive zeta zero.
-/

open Filter
open scoped BigOperators Topology

namespace PrimeNumberTheorem

/-- Union of a finite family of actual positive Carlson strips. -/
noncomputable def actualPositiveCarlsonFiniteStripUnion
    {n : ℕ} (sigma tau : Fin n → ℝ) (T : ℝ) : Finset ℂ :=
  (Finset.univ : Finset (Fin n)).biUnion
    fun i => actualPositiveCarlsonStrip (sigma i) (tau i) T

/-- Sum of multiplicity-weighted kernel masses over a finite strip family. -/
noncomputable def actualPositiveCarlsonFiniteStripMass
    {n : ℕ} (sigma tau : Fin n → ℝ) (alpha x : ℝ) : ℝ :=
  ∑ i : Fin n,
    ∑ rho ∈ actualPositiveCarlsonStrip (sigma i) (tau i)
        (carlsonPolynomialHeight alpha x),
      ‖pntRelativeZeroContribution x rho‖

theorem actualPositiveCarlsonFiniteStripUnion_mass_eq
    {n : ℕ} (sigma tau : Fin n → ℝ) (alpha x : ℝ)
    (hdisjoint :
      ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
        (fun i =>
          actualPositiveCarlsonStrip (sigma i) (tau i)
            (carlsonPolynomialHeight alpha x))) :
    (∑ rho ∈ actualPositiveCarlsonFiniteStripUnion sigma tau
          (carlsonPolynomialHeight alpha x),
        ‖pntRelativeZeroContribution x rho‖) =
      actualPositiveCarlsonFiniteStripMass sigma tau alpha x := by
  classical
  exact Finset.sum_biUnion hdisjoint

/-- Coordinatewise balanced endpoint conditions make the complete finite
family mass tend to zero. -/
theorem tendsto_actualPositiveCarlsonFiniteStripMass
    {n : ℕ} {sigma tau : Fin n → ℝ} {alpha epsilon : ℝ}
    (hhalf : ∀ i, 1 / 2 < sigma i)
    (hone : ∀ i, sigma i < 1)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (htau :
      ∀ i,
        tau i + epsilon <
          carlsonTwoHeightBalancedTauCeiling (sigma i) alpha) :
    Tendsto
      (actualPositiveCarlsonFiniteStripMass sigma tau alpha)
      atTop (nhds 0) := by
  unfold actualPositiveCarlsonFiniteStripMass
  simpa only [Finset.sum_const_zero] using
    tendsto_finset_sum
      (Finset.univ : Finset (Fin n))
      (fun i _ =>
        tendsto_sum_norm_actualPositiveCarlsonStrip_of_lt_balancedTauCeiling
          (hhalf i) (hone i) halpha hepsilon (htau i))

/-- If the real strips are disjoint at every scale, the mass of their actual
union tends to zero. -/
theorem tendsto_actualPositiveCarlsonFiniteStripUnion_mass
    {n : ℕ} {sigma tau : Fin n → ℝ} {alpha epsilon : ℝ}
    (hhalf : ∀ i, 1 / 2 < sigma i)
    (hone : ∀ i, sigma i < 1)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (htau :
      ∀ i,
        tau i + epsilon <
          carlsonTwoHeightBalancedTauCeiling (sigma i) alpha)
    (hdisjoint :
      ∀ x,
        ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
          (fun i =>
            actualPositiveCarlsonStrip (sigma i) (tau i)
              (carlsonPolynomialHeight alpha x))) :
    Tendsto
      (fun x =>
        ∑ rho ∈ actualPositiveCarlsonFiniteStripUnion sigma tau
            (carlsonPolynomialHeight alpha x),
          ‖pntRelativeZeroContribution x rho‖)
      atTop (nhds 0) := by
  apply
    (tendsto_actualPositiveCarlsonFiniteStripMass
      hhalf hone halpha hepsilon htau).congr'
  filter_upwards with x
  exact
    (actualPositiveCarlsonFiniteStripUnion_mass_eq
      sigma tau alpha x (hdisjoint x)).symm

end PrimeNumberTheorem
