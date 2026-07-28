import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedHeight
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryPNTTransfer

/-!
# Balanced Carlson boundary-mass transfer to the actual PNT error

The balanced height exponent, canonical two-strip partition, zero-kernel norm
lower bound, and selected-height contour certificate are all constructed
automatically.  Unlike the pointwise-gap transfer, high-strip zeros outside the
visible cluster may satisfy `Re rho = beta`.  Their nondecaying contribution is
retained explicitly as twice the positive-ordinate Carlson boundary mass.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- At the balanced selected height, the actual PNT residual outside a visible
cluster is eventually bounded by the Carlson boundary coefficient
`2 * boundaryMass + delta` on the target `x^(beta - 1)` scale. -/
theorem
    eventually_abs_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTClusterResidual_lt_automatic
    {S : Finset ℂ} {sigma beta delta : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ)| <
        (2 * actualCarlsonOutsideClusterBoundaryMass
              (sigma := sigma) beta S +
            delta) *
          targetZeroPowerAmplitude beta (m : ℝ) := by
  let alpha := actualCarlsonBalancedHeightExponent sigma
  let H := selectedUniformGoodHeight alpha selection
  let input :
      (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S 2 :=
    fun x =>
      pntHybridCanonicalTwoStripOutsideClusterBucketInput sigma (H x) S
  have hbeta : 0 < beta := by
    linarith
  have halpha : 0 < alpha := by
    simpa [alpha] using
      (show 0 < actualCarlsonBalancedHeightExponent sigma by
        unfold actualCarlsonBalancedHeightExponent
        linarith)
  have halphaOne : alpha ≤ 1 := by
    dsimp [alpha]
    unfold actualCarlsonBalancedHeightExponent
    linarith
  rcases
      exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
        H sigma S with
    ⟨kappa, hkappa, hnorm⟩
  have hinterval :=
    eventually_selectedUniformGoodHeight_mem halpha selection
  have hHle :
      ∀ᶠ x : ℝ in atTop, H x ≤ carlsonPolynomialHeight alpha x := by
    filter_upwards [hinterval] with x hx
    simpa [H, carlsonPolynomialHeight] using hx.2
  have hHtop : Tendsto H atTop atTop := by
    simpa [H] using selectedUniformGoodHeight_tendsto_atTop halpha selection
  apply
    eventually_abs_actualCarlsonSelectedHeightPNTClusterResidual_lt_boundaryCoefficient_mul_targetAmplitude
      input (0 : Fin 2) hS hHle hHtop hbeta hhalf hone hkappa
  · simpa [input] using hnorm
  · intro x rho hrho
    exact pntHybridCanonicalTwoStripOutsideCluster_low_re_le hrho
  · intro x rho hrho hre
    exact pntHybridCanonicalTwoStripOutsideCluster_low_cover hrho hre
  · exact halpha
  · exact actualCarlsonBalancedEpsilon_pos hbalance
  · simpa [alpha] using
      actualCarlsonBalancedHeight_low_margin_with_epsilon hbalance
  · exact hreHigh
  · exact hreReal
  · simpa [H, alpha] using
      selectedUniformGoodHeight_actualNaturalRemainderCertificate
        hbeta halpha halphaOne
          (actualCarlsonBalancedHeightExponent_contour_margin hbalance)
          selection
  · exact hdelta

end PrimeNumberTheorem
