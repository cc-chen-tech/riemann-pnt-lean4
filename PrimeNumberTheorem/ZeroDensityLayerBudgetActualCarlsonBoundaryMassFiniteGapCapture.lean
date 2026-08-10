import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryMassFiniteCapture

/-!
# Finite capture below a prescribed transfer gap

Finite summable capture can be calibrated directly to the strict coefficient
gap required by the Carlson boundary transfer: for every `q < c`, one can
choose a finite conjugation-stable cluster with `2 * boundaryMass < c - q`.
-/

namespace PrimeNumberTheorem

/-- Every strict target coefficient `q < c` admits a finite
conjugation-stable cluster whose remaining Carlson boundary loss fits inside
the transfer gap. -/
theorem
    exists_conjugationStable_actualCarlsonOutsideClusterBoundaryMass_two_mul_lt_gap
    {sigma beta c q : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hqC : q < c) :
    ∃ S : Finset ℂ,
      (∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < c - q := by
  have hepsilon : 0 < (c - q) / 2 := by
    linarith
  obtain ⟨S, hS, hmass⟩ :=
    exists_conjugationStable_actualCarlsonOutsideClusterBoundaryMass_lt
      (beta := beta) hhalf hone hepsilon
  refine ⟨S, hS, ?_⟩
  linarith

/-- In particular, every positive visible-cluster coefficient admits a finite
conjugation-stable cluster with boundary loss strictly below that
coefficient. -/
theorem
    exists_conjugationStable_actualCarlsonOutsideClusterBoundaryMass_two_mul_lt
    {sigma beta c : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hc : 0 < c) :
    ∃ S : Finset ℂ,
      (∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < c := by
  simpa using
    (exists_conjugationStable_actualCarlsonOutsideClusterBoundaryMass_two_mul_lt_gap
      (beta := beta) (q := 0) hhalf hone hc)

end PrimeNumberTheorem
