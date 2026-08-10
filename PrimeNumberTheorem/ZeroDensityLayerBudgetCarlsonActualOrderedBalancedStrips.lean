import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualFiniteBalancedStrips

/-!
# Endpoint-ordered balanced Carlson strips

Real endpoint separation is a scale-independent certificate that the actual
zeta strips are pairwise disjoint.  This removes the dynamic finset
disjointness hypothesis from the finite-family transfer.
-/

open Filter
open scoped Topology

namespace PrimeNumberTheorem

theorem actualPositiveCarlsonStrip_disjoint_of_tau_le_sigma
    {sigma₁ tau₁ sigma₂ tau₂ T : ℝ}
    (hsep : tau₁ ≤ sigma₂) :
    Disjoint
      (actualPositiveCarlsonStrip sigma₁ tau₁ T)
      (actualPositiveCarlsonStrip sigma₂ tau₂ T) := by
  rw [Finset.disjoint_left]
  intro rho hleft hright
  have hleftRe :=
    (mem_actualPositiveCarlsonStrip.mp hleft).2.2.2.2
  have hrightRe :=
    (mem_actualPositiveCarlsonStrip.mp hright).2.2.2.1
  exact (not_lt_of_ge (hleftRe.trans hsep)) hrightRe

/-- Pairwise endpoint separation supplies pairwise disjoint actual strips at
every height. -/
theorem actualPositiveCarlsonStrips_pairwiseDisjoint_of_endpoints
    {n : ℕ} (sigma tau : Fin n → ℝ) (T : ℝ)
    (hsep :
      ∀ i j, i ≠ j →
        tau i ≤ sigma j ∨ tau j ≤ sigma i) :
    ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      (fun i => actualPositiveCarlsonStrip (sigma i) (tau i) T) := by
  intro i _ j _ hij
  rcases hsep i j hij with hijSep | hjiSep
  · exact actualPositiveCarlsonStrip_disjoint_of_tau_le_sigma hijSep
  · exact
      (actualPositiveCarlsonStrip_disjoint_of_tau_le_sigma hjiSep).symm

/-- Finite balanced transfer with only static endpoint ordering as the
disjointness certificate. -/
theorem tendsto_actualPositiveCarlsonOrderedStripUnion_mass
    {n : ℕ} {sigma tau : Fin n → ℝ} {alpha epsilon : ℝ}
    (hhalf : ∀ i, 1 / 2 < sigma i)
    (hone : ∀ i, sigma i < 1)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (htau :
      ∀ i,
        tau i + epsilon <
          carlsonTwoHeightBalancedTauCeiling (sigma i) alpha)
    (hsep :
      ∀ i j, i ≠ j →
        tau i ≤ sigma j ∨ tau j ≤ sigma i) :
    Tendsto
      (fun x =>
        ∑ rho ∈ actualPositiveCarlsonFiniteStripUnion sigma tau
            (carlsonPolynomialHeight alpha x),
          ‖pntRelativeZeroContribution x rho‖)
      atTop (nhds 0) := by
  exact tendsto_actualPositiveCarlsonFiniteStripUnion_mass
    hhalf hone halpha hepsilon htau
    (fun x =>
      actualPositiveCarlsonStrips_pairwiseDisjoint_of_endpoints
        sigma tau (carlsonPolynomialHeight alpha x) hsep)

end PrimeNumberTheorem
