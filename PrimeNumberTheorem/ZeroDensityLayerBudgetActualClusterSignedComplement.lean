import PrimeNumberTheorem.ZeroDensityLayerBudgetActualFullTailExcludingClusterConjugation

/-!
# Exact visible-cluster and signed-complement decomposition

At a dynamic truncation height, the finite zeta-zero sum splits exactly into
the zeros currently visible in the distinguished cluster and the finite
difference outside that cluster.  Taking real parts produces the real-valued
main/complement decomposition used by the PNT transfer, while
`|re z| <= ‖z‖` supplies the required signed-complement domination.
-/

open scoped BigOperators

namespace PrimeNumberTheorem

/-- Multiplicity-weighted relative PNT contribution from the part of `S`
visible at the current dynamic height. -/
noncomputable def dynamicVisibleClusterPNTZeroSum
    (T : ℝ → ℝ) (S : Finset ℂ) (x : ℝ) : ℂ :=
  ∑ rho ∈ nontrivialZerosFinset (T x),
    if rho ∈ S then pntRelativeZeroContribution x rho else 0

/-- Actual multiplicity-weighted relative PNT zero sum outside `S`. -/
noncomputable def dynamicOutsideClusterPNTZeroSum
    (T : ℝ → ℝ) (S : Finset ℂ) (x : ℝ) : ℂ :=
  ∑ rho ∈ nontrivialZerosOutsideClusterFinset (T x) S,
    pntRelativeZeroContribution x rho

/-- Complete multiplicity-weighted relative PNT finite zero sum. -/
noncomputable def dynamicFinitePNTZeroSum
    (T : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∑ rho ∈ nontrivialZerosFinset (T x),
    pntRelativeZeroContribution x rho

/-- Exact finite-sum partition into the visible main cluster and its
outside-cluster complement. -/
theorem dynamicFinitePNTZeroSum_eq_visibleCluster_add_outsideCluster
    (T : ℝ → ℝ) (S : Finset ℂ) (x : ℝ) :
    dynamicFinitePNTZeroSum T x =
      dynamicVisibleClusterPNTZeroSum T S x +
        dynamicOutsideClusterPNTZeroSum T S x := by
  classical
  unfold dynamicFinitePNTZeroSum dynamicVisibleClusterPNTZeroSum
    dynamicOutsideClusterPNTZeroSum
    nontrivialZerosOutsideClusterFinset
  rw [← sum_clusterExcludedTerm_eq_sum_sdiff]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hS : rho ∈ S
  · simp [clusterExcludedTerm, hS]
  · simp [clusterExcludedTerm, hS]

/-- Real-valued visible-cluster main term. -/
noncomputable def dynamicVisibleClusterPNTMain
    (T : ℝ → ℝ) (S : Finset ℂ) (x : ℝ) : ℝ :=
  (dynamicVisibleClusterPNTZeroSum T S x).re

/-- Real-valued signed complementary-zero term outside `S`. -/
noncomputable def dynamicOutsideClusterPNTComplement
    (T : ℝ → ℝ) (S : Finset ℂ) (x : ℝ) : ℝ :=
  (dynamicOutsideClusterPNTZeroSum T S x).re

/-- Taking real parts preserves the exact visible-cluster decomposition. -/
theorem dynamicFinitePNTZeroSum_re_eq_main_add_complement
    (T : ℝ → ℝ) (S : Finset ℂ) (x : ℝ) :
    (dynamicFinitePNTZeroSum T x).re =
      dynamicVisibleClusterPNTMain T S x +
        dynamicOutsideClusterPNTComplement T S x := by
  have h :=
    congrArg Complex.re
      (dynamicFinitePNTZeroSum_eq_visibleCluster_add_outsideCluster
        T S x)
  simpa [dynamicVisibleClusterPNTMain,
    dynamicOutsideClusterPNTComplement] using h

/-- The actual signed complement is pointwise dominated by the exact
outside-cluster tail norm. -/
theorem abs_dynamicOutsideClusterPNTComplement_le_tailNorm
    (T : ℝ → ℝ) (S : Finset ℂ) (x : ℝ) :
    |dynamicOutsideClusterPNTComplement T S x| ≤
      dynamicFullOutsideClusterPNTZeroTailNorm T S x := by
  exact Complex.abs_re_le_norm
    (dynamicOutsideClusterPNTZeroSum T S x)

end PrimeNumberTheorem
