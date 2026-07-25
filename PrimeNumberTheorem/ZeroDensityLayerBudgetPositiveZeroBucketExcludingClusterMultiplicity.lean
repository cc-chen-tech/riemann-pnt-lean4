import PrimeNumberTheorem.ZeroDensityLayerBudgetPositiveZeroBucketExcludingCluster
import PrimeNumberTheorem.ZeroDensityLayerBudgetMultiplicityWeightedKernel

/-!
# Multiplicity-weighted zeta kernels outside a finite main cluster

Carlson's count is weighted by analytic multiplicity.  This module transfers
that exact count to buckets covering
`positiveNontrivialZerosFinset T \ S`, then aggregates the actual relative PNT
zero contribution over the cluster-excluded positive tail.
-/

open scoped BigOperators

namespace PrimeNumberTheorem

/-- Analytic multiplicity mass in an outside-cluster bucket is bounded by the
ordinary Carlson multiplicity count. -/
theorem
    PositiveZeroOutsideClusterBucketInput.layer_multiplicityMass_le_zeroDensityCount
    {T : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n) (i : Fin n) :
    analyticMultiplicityMass (input.layer i) ≤
      (ZeroDensity.zeroDensityCount (input.sigma i) T : ℝ) := by
  have hnat :
      (∑ ρ ∈ input.layer i, analyticOrderNatAt riemannZeta ρ) ≤
        ∑ ρ ∈ ZeroDensity.zeroDensityZerosFinset (input.sigma i) T,
          analyticOrderNatAt riemannZeta ρ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (input.layer_subset_zeroDensityZerosFinset i)
    intro ρ hρ hnot
    exact Nat.zero_le _
  unfold analyticMultiplicityMass ZeroDensity.zeroDensityCount
  exact_mod_cast hnat

/-- A pointwise simple-kernel bound is multiplied by analytic multiplicity
exactly once and then absorbed by Carlson's count. -/
theorem
    PositiveZeroOutsideClusterBucketInput.sum_norm_pntRelativeZeroContribution_layer_le_count
    {T x K : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n) (i : Fin n)
    (hK : 0 ≤ K)
    (hkernel :
      ∀ ρ ∈ input.layer i,
        ‖pntRelativeSimpleZeroKernel x ρ‖ ≤ K) :
    (∑ ρ ∈ input.layer i, ‖pntRelativeZeroContribution x ρ‖) ≤
      K * (ZeroDensity.zeroDensityCount (input.sigma i) T : ℝ) := by
  exact
    sum_norm_pntRelativeZeroContribution_le_kernel_mul_of_mass_le
      (input.layer i) x K
      (ZeroDensity.zeroDensityCount (input.sigma i) T : ℝ)
      hK hkernel
      (input.layer_multiplicityMass_le_zeroDensityCount i)

/-- The actual multiplicity-weighted relative PNT zero sum over positive
ordinates outside `S` is controlled by the corresponding Carlson aggregate. -/
theorem
    PositiveZeroOutsideClusterBucketInput.norm_positive_pntRelativeZeroContribution_sum_le
    {T x : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n)
    (hkernel :
      ∀ i, ∀ ρ ∈ input.layer i,
        ‖pntRelativeSimpleZeroKernel x ρ‖ ≤
          Real.exp (-Pintz.pintzZeroEnvelope x)) :
    ‖∑ ρ ∈ positiveNontrivialZerosOutsideClusterFinset T S,
        pntRelativeZeroContribution x ρ‖ ≤
      pintzCarlsonClassicalAggregatedDensityLayerTerm
        (Finset.univ : Finset (Fin n)) input.sigma () x T := by
  have hdecomp :
      (∑ ρ ∈ positiveNontrivialZerosOutsideClusterFinset T S,
        pntRelativeZeroContribution x ρ) =
        ∑ i : Fin n, ∑ ρ ∈ input.layer i,
          pntRelativeZeroContribution x ρ :=
    input.certificate.sum_decomposition (pntRelativeZeroContribution x)
  rw [hdecomp]
  calc
    ‖∑ i : Fin n, ∑ ρ ∈ input.layer i,
        pntRelativeZeroContribution x ρ‖ ≤
        ∑ i : Fin n, ‖∑ ρ ∈ input.layer i,
          pntRelativeZeroContribution x ρ‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ∑ ρ ∈ input.layer i,
        ‖pntRelativeZeroContribution x ρ‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sum_le _ _
    _ ≤ ∑ i : Fin n,
        Real.exp (-Pintz.pintzZeroEnvelope x) *
          (ZeroDensity.zeroDensityCount (input.sigma i) T : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact
        input.sum_norm_pntRelativeZeroContribution_layer_le_count i
          (Real.exp_nonneg _) (hkernel i)
    _ = pintzCarlsonClassicalAggregatedDensityLayerTerm
        (Finset.univ : Finset (Fin n)) input.sigma () x T := by
      simp [pintzCarlsonClassicalAggregatedDensityLayerTerm,
        pintzCarlsonAggregatedDensityLayerTerm, mul_comm]

end PrimeNumberTheorem
