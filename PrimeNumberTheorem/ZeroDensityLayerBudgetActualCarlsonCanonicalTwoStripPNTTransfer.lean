import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonSelectedHeightPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridCanonicalTwoStripProfile

/-!
# Canonical two-strip pointwise Carlson transfer

The canonical two-strip bucket is determined by the predicate
`rho.re ≤ sigma`.  This removes the abstract bucket input, selected bucket
index, low-strip real-part proof, and coverage proof from the public PNT
transfer interface.

The uniform norm lower bound on the canonical low strip remains explicit.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- The canonical low bucket contains only zeros with real part at most its
threshold. -/
theorem pntHybridCanonicalTwoStripOutsideCluster_low_re_le
    {threshold T : ℝ} {S : Finset ℂ} {rho : ℂ}
    (hrho :
      rho ∈
        (pntHybridCanonicalTwoStripOutsideClusterBucketInput
          threshold T S).layer (0 : Fin 2)) :
    rho.re ≤ threshold := by
  have hbucket := (Finset.mem_filter.mp hrho).2
  change (if threshold < rho.re then (1 : Fin 2) else 0) = 0 at hbucket
  by_contra hnot
  have hlt : threshold < rho.re := lt_of_not_ge hnot
  simp [hlt] at hbucket

/-- Every truncated positive zero with real part at most the threshold belongs
to the canonical low bucket. -/
theorem pntHybridCanonicalTwoStripOutsideCluster_low_cover
    {threshold T : ℝ} {S : Finset ℂ} {rho : ℂ}
    (_hrho : rho ∈ positiveNontrivialZerosOutsideClusterFinset T S)
    (hre : rho.re ≤ threshold) :
    (pntHybridCanonicalTwoStripOutsideClusterBucketInput
      threshold T S).bucket rho = (0 : Fin 2) := by
  change (if threshold < rho.re then (1 : Fin 2) else 0) = 0
  simp [not_lt.mpr hre]

/-- Actual-PNT cluster residual decay with automatic canonical two-strip
layering.  The high strip uses the pointwise condition `Re rho < beta`
outside `S`, not a uniform real-part margin. -/
theorem selectedUniformGoodHeightActualCarlsonCanonicalTwoStripPNTClusterResidual_targetNegligible
    {S : Finset ℂ} {sigma beta alpha kappa epsilon : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hbeta : 0 < beta)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hkappa : 0 < kappa)
    (hnorm :
      ∀ (x : ℝ),
        ∀ rho ∈
            (pntHybridCanonicalTwoStripOutsideClusterBucketInput
              sigma (selectedUniformGoodHeight alpha selection x) S).layer
                (0 : Fin 2),
          kappa ≤ ‖rho‖)
    (halpha : 0 < alpha)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta < alpha)
    (hepsilon : 0 < epsilon)
    (hlowMargin : sigma - beta + alpha + epsilon < 0)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index < beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    NaturalPointTargetAmplitudeNegligible
      (fun m => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m =>
        relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection) S (m : ℝ)) := by
  let input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (selectedUniformGoodHeight alpha selection x) S 2 :=
    fun x =>
      pntHybridCanonicalTwoStripOutsideClusterBucketInput
        sigma (selectedUniformGoodHeight alpha selection x) S
  apply
    selectedUniformGoodHeightActualCarlsonPNTClusterResidual_targetNegligible
      selection input (0 : Fin 2) hS hbeta hhalf hone hkappa
  · simpa [input] using hnorm
  · intro x rho hrho
    exact pntHybridCanonicalTwoStripOutsideCluster_low_re_le hrho
  · intro x rho hrho hre
    exact
      pntHybridCanonicalTwoStripOutsideCluster_low_cover hrho hre
  · exact halpha
  · exact halphaOne
  · exact hcontourMargin
  · exact hepsilon
  · exact hlowMargin
  · exact hreHigh
  · exact hreReal

end PrimeNumberTheorem
