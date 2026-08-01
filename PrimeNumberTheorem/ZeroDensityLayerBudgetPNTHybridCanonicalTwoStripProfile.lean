import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridActualSelectedHeightBidirectionalTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTParametricTwoStrip

/-!
# Canonical two-strip hybrid profile outside a visible zero cluster

The smallest structurally viable complete profile has two layers:

* `sigma 0 = 0`, containing zeros with real part at most `threshold`;
* `sigma 1 = threshold > 1 / 2`, containing the remaining zeros.

The low layer is counted globally and the high layer by Carlson.  An explicit
outside-cluster real-part cap `upper` supplies the high-layer endpoint.  The
two strict feasibility inequalities are exposed without hiding them:

* `threshold < 2 * beta - 1` for the global low layer;
* `4 * threshold * (1 - threshold) * (1 - beta) < beta - upper`
  for the Carlson high layer.
-/

namespace PrimeNumberTheorem

noncomputable section

/-- Endpoint profile paired with the parametric two-strip lower thresholds. -/
def pntHybridCanonicalTwoStripTau
    (threshold upper : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then threshold else upper

/-- Canonical complete two-strip classification after deleting the visible
cluster. -/
noncomputable def pntHybridCanonicalTwoStripOutsideClusterBucketInput
    (threshold T : ℝ) (S : Finset ℂ) :
    PositiveZeroOutsideClusterBucketInput T S 2 where
  bucket := fun rho => if threshold < rho.re then 1 else 0
  sigma := pntParametricTwoStripSigma threshold
  sigma_lt_re := by
    intro rho hrho
    by_cases hhigh : threshold < rho.re
    · simpa [pntParametricTwoStripSigma, hhigh] using hhigh
    · have hzero :=
        (mem_positiveNontrivialZerosOutsideClusterFinset.mp hrho).1
      simpa [pntParametricTwoStripSigma, hhigh] using hzero.2.1

@[simp]
theorem pntHybridCanonicalTwoStripOutsideClusterBucketInput_sigma
    (threshold T : ℝ) (S : Finset ℂ) (i : Fin 2) :
    (pntHybridCanonicalTwoStripOutsideClusterBucketInput
      threshold T S).sigma i =
      pntParametricTwoStripSigma threshold i :=
  rfl

/-- Membership in the low layer automatically gives its endpoint bound. -/
theorem pntHybridCanonicalTwoStripOutsideCluster_lowLayer_re_le
    {threshold T : ℝ} {S : Finset ℂ} {rho : ℂ}
    (hrho :
      rho ∈
        (pntHybridCanonicalTwoStripOutsideClusterBucketInput
          threshold T S).layer 0) :
    rho.re ≤ threshold := by
  have hbucket := (Finset.mem_filter.mp hrho).2
  by_contra hnot
  have hhigh : threshold < rho.re := lt_of_not_ge hnot
  simp [pntHybridCanonicalTwoStripOutsideClusterBucketInput, hhigh] at hbucket

/-- A cap on every high outside-cluster zero supplies the upper endpoint of
the high layer. -/
theorem pntHybridCanonicalTwoStripOutsideCluster_layer_re_le
    {threshold upper T : ℝ} {S : Finset ℂ}
    (hhighCap :
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
        threshold < rho.re → rho.re ≤ upper) :
    ∀ i : Fin 2, ∀ rho ∈
        (pntHybridCanonicalTwoStripOutsideClusterBucketInput
          threshold T S).layer i,
      rho.re ≤ pntHybridCanonicalTwoStripTau threshold upper i := by
  intro i rho hrho
  fin_cases i
  · simpa [pntHybridCanonicalTwoStripTau] using
      pntHybridCanonicalTwoStripOutsideCluster_lowLayer_re_le hrho
  · have hlayer := Finset.mem_filter.mp hrho
    have hbucket := hlayer.2
    have hhigh : threshold < rho.re := by
      by_contra hnot
      have hle : rho.re ≤ threshold := le_of_not_gt hnot
      simp [pntHybridCanonicalTwoStripOutsideClusterBucketInput,
        not_lt.mpr hle] at hbucket
    simpa [pntHybridCanonicalTwoStripTau] using
      hhighCap rho hlayer.1 hhigh

/-- The canonical endpoint profile is nonnegative when both supplied
endpoints are. -/
theorem pntHybridCanonicalTwoStripTau_nonneg
    {threshold upper : ℝ}
    (hthreshold : 0 ≤ threshold) (hupper : 0 ≤ upper) :
    ∀ i, 0 ≤ pntHybridCanonicalTwoStripTau threshold upper i := by
  intro i
  fin_cases i <;>
    simp [pntHybridCanonicalTwoStripTau, hthreshold, hupper]

/-- Exact sufficient feasibility conditions for the canonical mixed profile. -/
theorem pntHybridCanonicalTwoStrip_budget
    {beta threshold upper : ℝ}
    (hhalf : 1 / 2 < threshold)
    (hlow : threshold < 2 * beta - 1)
    (hhigh :
      4 * threshold * (1 - threshold) * (1 - beta) <
        beta - upper) :
    ∀ i : Fin 2,
      pntHybridAffineDensitySlope
            (pntParametricTwoStripSigma threshold) i *
          pntHybridAffineDensityFloor beta <
        pntHybridAffineDensityCeiling beta
          (pntHybridCanonicalTwoStripTau threshold upper) i := by
  intro i
  fin_cases i
  · simp [pntHybridAffineDensitySlope, pntHybridAffineDensityFloor,
      pntHybridAffineDensityCeiling, pntParametricTwoStripSigma,
      pntHybridCanonicalTwoStripTau]
    linarith
  · have hnotLow : ¬ threshold ≤ (2 : ℝ)⁻¹ := by
      norm_num
      exact hhalf
    simp [pntHybridAffineDensitySlope, pntHybridAffineDensityFloor,
      pntHybridAffineDensityCeiling, pntParametricTwoStripSigma,
      pntHybridCanonicalTwoStripTau, hnotLow,
      carlsonAffineDensitySlope, actualSelectedHeightStripCarlsonSlope]
    nlinarith

/-- Every high-density index of the canonical profile remains below one. -/
theorem pntHybridCanonicalTwoStrip_highSigma_lt_one
    {threshold : ℝ} (hthresholdOne : threshold < 1) :
    ∀ i ∈
        pintzCarlsonHighDensityIndices
          (pntParametricTwoStripSigma threshold),
      pntParametricTwoStripSigma threshold i < 1 :=
  pntParametricTwoStripSigma_high_lt_one hthresholdOne

end

end PrimeNumberTheorem
