import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridCanonicalTwoStripTransfer

/-!
# Canonical hybrid PNT transfer from one outside-cluster cap

This module replaces the separate high-strip and real-ordinate hypotheses in
the canonical two-strip transfer by one global real-part cap on every
nontrivial zeta zero outside the distinguished cluster.
-/

namespace PrimeNumberTheorem

/-- Every nontrivial zeta zero outside `S` has real part at most `upper`. -/
def OutsideClusterRealPartCap (S : Finset ℂ) (upper : ℝ) : Prop :=
  ∀ rho : ℂ,
    RiemannHypothesis.IsNontrivialZero rho →
      rho ∉ S →
        rho.re ≤ upper

/-- A global outside-cluster cap restricts the high bucket at every height. -/
theorem outsideClusterRealPartCap_highBucket
    {S : Finset ℂ} {upper threshold T : ℝ}
    (hcap : OutsideClusterRealPartCap S upper) :
    ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
      threshold < rho.re → rho.re ≤ upper := by
  intro rho hrho _
  rcases mem_positiveNontrivialZerosOutsideClusterFinset.mp hrho with
    ⟨hzero, _, _, hout⟩
  exact hcap rho hzero hout

/-- If the global cap lies below `beta`, all real-ordinate residual zeros have
the strict gap required by the target-amplitude transfer. -/
theorem outsideClusterRealPartCap_realOrdinateGap
    {S : Finset ℂ} {upper beta : ℝ}
    (hcap : OutsideClusterRealPartCap S upper)
    (hupperBeta : upper < beta) :
    ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
      rho.re < beta := by
  intro rho hrho
  rcases Finset.mem_sdiff.mp hrho with ⟨hreal, hout⟩
  have hzero : RiemannHypothesis.IsNontrivialZero rho :=
    (mem_nontrivialZerosFinset.mp
      (mem_realOrdinateNontrivialZerosFinset.mp hreal).1).1
  exact lt_of_le_of_lt (hcap rho hzero hout) hupperBeta

/--
Canonical two-strip bidirectional PNT transfer driven by one global
outside-cluster real-part cap.

The Carlson feasibility inequality itself forces `upper < beta`, so the same
cap supplies both the high positive-height strip bound and the strict
real-ordinate residual gap. The cluster oscillation witness and kernel norm
guards remain explicit analytic inputs.
-/
theorem actualHybridCanonicalOutsideClusterCapPNTBidirectionalTransfer
    {beta c threshold upper : ℝ}
    (hbeta : 0 < beta)
    (hbetaOne : beta < 1)
    (hc : 0 < c)
    (hhalf : 1 / 2 < threshold)
    (hthresholdOne : threshold < 1)
    (hupper : 0 ≤ upper)
    (hlow : threshold < 2 * beta - 1)
    (hhigh :
      4 * threshold * (1 - threshold) * (1 - beta) < beta - upper)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (kappa : Fin 2 → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x,
        ∀ rho ∈
          (pntHybridCanonicalTwoStripOutsideClusterBucketInput threshold
            (pntHybridAffineSelectedGoodHeight beta
              (pntParametricTwoStripSigma threshold)
              (pntHybridCanonicalTwoStripTau threshold upper)
              selection x) S).layer i,
          kappa i ≤ ‖rho‖)
    (hcap : OutsideClusterRealPartCap S upper)
    (hmain :
      S.Nonempty →
        HasFarNaturalPointTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (pntHybridAffineSelectedGoodHeight beta
                (pntParametricTwoStripSigma threshold)
                (pntHybridCanonicalTwoStripTau threshold upper)
                selection) S m)
          (fun m => c * targetZeroPowerAmplitude beta m)) :
    ActualHybridSelectedHeightPNTBidirectionalTransferCertificate
      (beta := beta) (c := c)
      (pntParametricTwoStripSigma threshold)
      (pntHybridCanonicalTwoStripTau threshold upper)
      selection S := by
  have hthresholdPos : 0 < threshold := lt_trans (by norm_num) hhalf
  have hthresholdComplement : 0 < 1 - threshold := sub_pos.mpr hthresholdOne
  have hbetaComplement : 0 < 1 - beta := sub_pos.mpr hbetaOne
  have hpositive :
      0 < 4 * threshold * (1 - threshold) * (1 - beta) := by
    exact
      mul_pos
        (mul_pos (mul_pos (by norm_num) hthresholdPos) hthresholdComplement)
        hbetaComplement
  have hupperBeta : upper < beta := by
    linarith
  apply actualHybridCanonicalTwoStripPNTBidirectionalTransfer
      hbeta hbetaOne hc hhalf hthresholdOne hupper hlow hhigh
      selection kappa hS hkappa hnorm
  · intro x
    exact outsideClusterRealPartCap_highBucket hcap
  · exact outsideClusterRealPartCap_realOrdinateGap hcap hupperBeta
  · exact hmain

end PrimeNumberTheorem
