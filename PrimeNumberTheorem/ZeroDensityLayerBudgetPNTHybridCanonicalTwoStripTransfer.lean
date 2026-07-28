import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridCanonicalTwoStripProfile

/-!
# Actual PNT transfer from the canonical hybrid two-strip profile

This specialization removes the external finite bucket family from the
bidirectional transfer theorem.  The two layers, their coverage, fixed lower
thresholds, endpoint bounds, and affine feasibility certificate are generated
automatically.

The remaining hypotheses are genuinely analytic: a denominator guard, a
real-part cap for high outside-cluster zeros, the real-ordinate gap, and the
visible-cluster oscillation witness.
-/

open scoped Topology

noncomputable section

namespace PrimeNumberTheorem

/-- Bidirectional actual-PNT transfer for the canonical complete two-strip
outside-cluster decomposition. -/
theorem actualHybridCanonicalTwoStripPNTBidirectionalTransfer
    {beta c threshold upper : ℝ}
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hc : 0 < c)
    (hhalf : 1 / 2 < threshold)
    (hthresholdOne : threshold < 1)
    (hupper : 0 ≤ upper)
    (hlow : threshold < 2 * beta - 1)
    (hhigh :
      4 * threshold * (1 - threshold) * (1 - beta) <
        beta - upper)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (kappa : Fin 2 → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈
          (pntHybridCanonicalTwoStripOutsideClusterBucketInput
            threshold
            (pntHybridAffineSelectedGoodHeight beta
              (pntParametricTwoStripSigma threshold)
              (pntHybridCanonicalTwoStripTau threshold upper)
              selection x)
            S).layer i,
        kappa i ≤ ‖rho‖)
    (hhighCap :
      ∀ x, ∀ rho ∈
          positiveNontrivialZerosOutsideClusterFinset
            (pntHybridAffineSelectedGoodHeight beta
              (pntParametricTwoStripSigma threshold)
              (pntHybridCanonicalTwoStripTau threshold upper)
              selection x)
            S,
        threshold < rho.re → rho.re ≤ upper)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hmain :
      S.Nonempty →
        HasFarNaturalPointTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (pntHybridAffineSelectedGoodHeight beta
                (pntParametricTwoStripSigma threshold)
                (pntHybridCanonicalTwoStripTau threshold upper)
                selection)
              S (m : ℝ))
          (fun m =>
            c * targetZeroPowerAmplitude beta (m : ℝ))) :
    ActualHybridSelectedHeightPNTBidirectionalTransferCertificate
      (beta := beta) (c := c)
      (pntParametricTwoStripSigma threshold)
      (pntHybridCanonicalTwoStripTau threshold upper)
      selection S := by
  let sigma := pntParametricTwoStripSigma threshold
  let tau := pntHybridCanonicalTwoStripTau threshold upper
  let H := pntHybridAffineSelectedGoodHeight beta sigma tau selection
  let input : (x : ℝ) →
      PositiveZeroOutsideClusterBucketInput (H x) S 2 :=
    fun x =>
      pntHybridCanonicalTwoStripOutsideClusterBucketInput
        threshold (H x) S
  have hthresholdNonneg : 0 ≤ threshold := by
    linarith
  have htau : ∀ i, 0 ≤ tau i := by
    exact pntHybridCanonicalTwoStripTau_nonneg
      hthresholdNonneg hupper
  have hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1 := by
    exact pntHybridCanonicalTwoStrip_highSigma_lt_one hthresholdOne
  have hbudget :
      ∀ i,
        pntHybridAffineDensitySlope sigma i *
              pntHybridAffineDensityFloor beta <
            pntHybridAffineDensityCeiling beta tau i := by
    exact pntHybridCanonicalTwoStrip_budget hhalf hlow hhigh
  have hfixedSigma : ∀ i x, (input x).sigma i = sigma i := by
    intro i x
    rfl
  have hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i := by
    intro i x rho hrho
    exact
      pntHybridCanonicalTwoStripOutsideCluster_layer_re_le
        (hhighCap x) i rho hrho
  exact
    actualHybridSelectedHeightPNTBidirectionalTransfer
      hbeta hbetaOne hc sigma tau htau hsigmaOneHigh hbudget
      selection input kappa hS hfixedSigma hkappa hnorm hre hreal hmain

end PrimeNumberTheorem
