import PrimeNumberTheorem.ZeroDensityLayerBudgetMultiplicityWeightedKernel

/-!
# Aggregating multiplicity-weighted PNT zero layers

The layerwise multiplicity estimate is summed over the positive-height
partition, then conjugation recovers the full finite zero sum.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem

/-- The actual multiplicity-weighted relative PNT zero sum over positive
ordinates is controlled by the Carlson aggregate. -/
theorem PositiveZeroBucketInput.norm_positive_pntRelativeZeroContribution_sum_le
    {T x : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n)
    (hkernel : ∀ i, ∀ ρ ∈ input.layer i,
      ‖pntRelativeSimpleZeroKernel x ρ‖ ≤
        Real.exp (-Pintz.pintzZeroEnvelope x)) :
    ‖∑ ρ ∈ positiveNontrivialZerosFinset T,
        pntRelativeZeroContribution x ρ‖ ≤
      pintzCarlsonClassicalAggregatedDensityLayerTerm
        (Finset.univ : Finset (Fin n)) input.sigma () x T := by
  have hdecomp :
      (∑ ρ ∈ positiveNontrivialZerosFinset T,
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
      exact input.sum_norm_pntRelativeZeroContribution_layer_le_count' i
        (hkernel i)
    _ = pintzCarlsonClassicalAggregatedDensityLayerTerm
        (Finset.univ : Finset (Fin n)) input.sigma () x T := by
      simp [pintzCarlsonClassicalAggregatedDensityLayerTerm,
        pintzCarlsonAggregatedDensityLayerTerm, mul_comm]

/-- Full multiplicity-weighted relative PNT zero sum: twice the positive-height
Carlson aggregate plus the explicit real-ordinate residual. -/
theorem PositiveZeroBucketInput.norm_full_pntRelativeZeroContribution_sum_le_weighted
    {T x : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n)
    (hx : 0 < x)
    (hkernel : ∀ i, ∀ ρ ∈ input.layer i,
      ‖pntRelativeSimpleZeroKernel x ρ‖ ≤
        Real.exp (-Pintz.pintzZeroEnvelope x)) :
    ‖∑ ρ ∈ nontrivialZerosFinset T,
        pntRelativeZeroContribution x ρ‖ ≤
      2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
        (Finset.univ : Finset (Fin n)) input.sigma () x T +
      ‖∑ ρ ∈ realOrdinateNontrivialZerosFinset T,
        pntRelativeZeroContribution x ρ‖ := by
  let positiveSum :=
    ∑ ρ ∈ positiveNontrivialZerosFinset T,
      pntRelativeZeroContribution x ρ
  let negativeSum :=
    ∑ ρ ∈ negativeNontrivialZerosFinset T,
      pntRelativeZeroContribution x ρ
  let realSum :=
    ∑ ρ ∈ realOrdinateNontrivialZerosFinset T,
      pntRelativeZeroContribution x ρ
  have hdecomp :
      (∑ ρ ∈ nontrivialZerosFinset T,
        pntRelativeZeroContribution x ρ) =
        positiveSum + negativeSum + realSum :=
    finiteZeroSum_eq_positive_add_negative_add_real T
      (pntRelativeZeroContribution x)
  have hnegative : negativeSum = conj positiveSum := by
    apply sum_negative_eq_conj_sum_positive
    intro ρ hρ
    exact pntRelativeZeroContribution_conj hx
      (mem_nontrivialZerosFinset.mp hρ).1
  have hpositive :
      ‖positiveSum‖ ≤
        pintzCarlsonClassicalAggregatedDensityLayerTerm
          (Finset.univ : Finset (Fin n)) input.sigma () x T :=
    input.norm_positive_pntRelativeZeroContribution_sum_le hkernel
  rw [hdecomp]
  calc
    ‖positiveSum + negativeSum + realSum‖ ≤
        ‖positiveSum‖ + ‖negativeSum‖ + ‖realSum‖ := by
      calc
        ‖positiveSum + negativeSum + realSum‖ ≤
            ‖positiveSum + negativeSum‖ + ‖realSum‖ := norm_add_le _ _
        _ ≤ ‖positiveSum‖ + ‖negativeSum‖ + ‖realSum‖ := by
          gcongr
          exact norm_add_le _ _
    _ = 2 * ‖positiveSum‖ + ‖realSum‖ := by
      rw [hnegative, norm_conj]
      ring
    _ ≤ 2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
          (Finset.univ : Finset (Fin n)) input.sigma () x T +
        ‖realSum‖ := by
      gcongr

end PrimeNumberTheorem
