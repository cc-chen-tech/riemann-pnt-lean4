import PrimeNumberTheorem.ZeroDensityLayerBudgetActualPositiveZeroOrderedCoverTransfer

/-!
# Barrier for fixed finite Carlson covers

A fixed finite strip family has a fixed upper endpoint.  Consequently it
cannot absorb a zero whose real part escapes above that endpoint.  This is the
precise obstruction to deriving the moving Vinogradov--Korobov boundary from
the fixed-strip transfer alone.
-/

namespace PrimeNumberTheorem

open Filter
open scoped Topology

noncomputable section

/-- A point above a common upper endpoint cannot belong to the finite strip
union. -/
theorem not_mem_actualPositiveCarlsonFiniteStripUnion_of_upper_lt_re
    {n : ℕ} {sigma tau : Fin n → ℝ} {T upper : ℝ} {rho : ℂ}
    (hupper : ∀ i, tau i ≤ upper)
    (hre : upper < rho.re) :
    rho ∉ actualPositiveCarlsonFiniteStripUnion sigma tau T := by
  intro hmem
  rw [actualPositiveCarlsonFiniteStripUnion] at hmem
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hmem
  have hrhoTau : rho.re ≤ tau i :=
    (mem_actualPositiveCarlsonStrip.mp hi).2.2.2.2
  exact (not_lt_of_ge (hrhoTau.trans (hupper i))) hre

/-- A certified fixed cover imposes its common endpoint cap on every covered
right-half zero. -/
theorem re_le_of_actualPositiveCarlsonRightCover_of_endpoint_cap
    {n : ℕ} {sigma tau : Fin n → ℝ} {T upper : ℝ}
    (hupper : ∀ i, tau i ≤ upper)
    (hcover : ActualPositiveCarlsonRightCover sigma tau T)
    {rho : ℂ}
    (hrho : rho ∈ positiveNontrivialZerosFinset T)
    (hright : 1 / 2 < rho.re) :
    rho.re ≤ upper := by
  by_contra hnot
  have hre : upper < rho.re := lt_of_not_ge hnot
  exact
    (not_mem_actualPositiveCarlsonFiniteStripUnion_of_upper_lt_re
      hupper hre) (hcover rho hrho hright)

/-- One right-half zero above the common endpoint destroys the fixed cover. -/
theorem not_actualPositiveCarlsonRightCover_of_escapingZero
    {n : ℕ} {sigma tau : Fin n → ℝ} {T upper : ℝ}
    (hupper : ∀ i, tau i ≤ upper)
    {rho : ℂ}
    (hrho : rho ∈ positiveNontrivialZerosFinset T)
    (hright : 1 / 2 < rho.re)
    (hre : upper < rho.re) :
    ¬ActualPositiveCarlsonRightCover sigma tau T := by
  intro hcover
  exact
    (not_mem_actualPositiveCarlsonFiniteStripUnion_of_upper_lt_re
      hupper hre) (hcover rho hrho hright)

/-- If zeros eventually escape every fixed common endpoint, the corresponding
fixed Carlson cover eventually fails. -/
theorem eventually_not_actualPositiveCarlsonRightCover_of_escapingZeros
    {ι : Type*} {l : Filter ι} {n : ℕ}
    {sigma tau : Fin n → ℝ} {H : ι → ℝ} {upper : ℝ}
    (hupper : ∀ i, tau i ≤ upper)
    (hescape :
      ∀ᶠ x in l,
        ∃ rho,
          rho ∈ positiveNontrivialZerosFinset (H x) ∧
            1 / 2 < rho.re ∧ upper < rho.re) :
    ∀ᶠ x in l, ¬ActualPositiveCarlsonRightCover sigma tau (H x) := by
  filter_upwards [hescape] with x hx
  obtain ⟨rho, hrho, hright, hre⟩ := hx
  exact
    not_actualPositiveCarlsonRightCover_of_escapingZero
      hupper hrho hright hre

end

end PrimeNumberTheorem
