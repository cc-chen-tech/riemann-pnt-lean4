import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridCanonicalAutomaticKernelGuardTransfer

/-!
# Canonical beta-dependent threshold for hybrid PNT transfer

For `beta > 3/4`, the explicit choice `threshold = beta - 1/4` lies strictly
between `1/2` and the low-layer feasibility ceiling `2 * beta - 1`. This
removes the strip threshold as an external parameter.
-/

namespace PrimeNumberTheorem

/-- A concrete two-strip boundary adapted to the target zero exponent. -/
noncomputable def pntHybridCanonicalBetaThreshold (beta : ℝ) : ℝ :=
  beta - 1 / 4

theorem pntHybridCanonicalBetaThreshold_half_lt
    {beta : ℝ} (hbeta : 3 / 4 < beta) :
    1 / 2 < pntHybridCanonicalBetaThreshold beta := by
  simp [pntHybridCanonicalBetaThreshold]
  linarith

theorem pntHybridCanonicalBetaThreshold_lt_one
    {beta : ℝ} (hbeta : beta < 1) :
    pntHybridCanonicalBetaThreshold beta < 1 := by
  simp [pntHybridCanonicalBetaThreshold]
  linarith

theorem pntHybridCanonicalBetaThreshold_lowBudget
    {beta : ℝ} (hbeta : 3 / 4 < beta) :
    pntHybridCanonicalBetaThreshold beta < 2 * beta - 1 := by
  simp [pntHybridCanonicalBetaThreshold]
  linarith

/--
Canonical bidirectional PNT transfer with the explicit threshold
`beta - 1/4`.

The low-layer and critical-half constraints are automatic from
`beta > 3/4`. The sole remaining density feasibility condition is the
displayed high-strip Carlson budget against the outside-cluster cap.
-/
theorem actualHybridCanonicalBetaThresholdPNTBidirectionalTransfer
    {beta c upper : ℝ}
    (hbeta : 3 / 4 < beta)
    (hbetaOne : beta < 1)
    (hc : 0 < c)
    (hupper : 0 ≤ upper)
    (hhigh :
      4 * pntHybridCanonicalBetaThreshold beta *
          (1 - pntHybridCanonicalBetaThreshold beta) * (1 - beta) <
        beta - upper)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (hS : IsConjugationInvariantCluster S)
    (hcap : OutsideClusterRealPartCap S upper)
    (hmain :
      S.Nonempty →
        HasFarNaturalPointTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (pntHybridAffineSelectedGoodHeight beta
                (pntParametricTwoStripSigma
                  (pntHybridCanonicalBetaThreshold beta))
                (pntHybridCanonicalTwoStripTau
                  (pntHybridCanonicalBetaThreshold beta) upper)
                selection) S m)
          (fun m => c * targetZeroPowerAmplitude beta m)) :
    ActualHybridSelectedHeightPNTBidirectionalTransferCertificate
      (beta := beta) (c := c)
      (pntParametricTwoStripSigma
        (pntHybridCanonicalBetaThreshold beta))
      (pntHybridCanonicalTwoStripTau
        (pntHybridCanonicalBetaThreshold beta) upper)
      selection S := by
  apply actualHybridCanonicalAutomaticKernelGuardPNTBidirectionalTransfer
      (beta := beta) (c := c)
  · linarith
  · exact hbetaOne
  · exact hc
  · exact pntHybridCanonicalBetaThreshold_half_lt hbeta
  · exact pntHybridCanonicalBetaThreshold_lt_one hbetaOne
  · exact hupper
  · exact pntHybridCanonicalBetaThreshold_lowBudget hbeta
  · exact hhigh
  · exact hS
  · exact hcap
  · exact hmain

end PrimeNumberTheorem
