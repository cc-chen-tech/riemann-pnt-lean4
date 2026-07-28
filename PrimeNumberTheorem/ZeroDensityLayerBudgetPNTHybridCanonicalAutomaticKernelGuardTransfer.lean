import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridCanonicalOutsideClusterCapTransfer

/-!
# Automatic kernel guards for the canonical hybrid PNT transfer

Continuity of `riemannZeta` at the origin and `riemannZeta 0 ≠ 0` give a
uniform positive lower bound for the norm of every nontrivial zero. This
supplies the denominator guard needed by both canonical real-part buckets.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- Nontrivial zeta zeros are uniformly separated from the origin. -/
theorem exists_positive_normLowerBound_of_isNontrivialZero :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
          kappa ≤ ‖rho‖ := by
  have hcontinuous : ContinuousAt riemannZeta (0 : ℂ) :=
    (differentiableAt_riemannZeta (by norm_num)).continuousAt
  have hzero : riemannZeta (0 : ℂ) ≠ 0 := by
    rw [riemannZeta_zero]
    norm_num
  have heventually :
      ∀ᶠ z in 𝓝 (0 : ℂ), riemannZeta z ≠ 0 :=
    hcontinuous.eventually_ne hzero
  rcases Metric.eventually_nhds_iff.mp heventually with
    ⟨kappa, hkappa, hball⟩
  refine ⟨kappa, hkappa, ?_⟩
  intro rho hrho
  apply le_of_not_gt
  intro hnorm
  exact hball (by simpa using hnorm) hrho.1

/-- One global zero-norm gap supplies constant positive guards for both
canonical buckets, uniformly in the selected dynamic height. -/
theorem exists_canonicalTwoStripKernelNormGuards
    (beta threshold upper : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (S : Finset ℂ) :
    ∃ kappa : Fin 2 → ℝ,
      (∀ i, 0 < kappa i) ∧
      ∀ i x,
        ∀ rho ∈
          (pntHybridCanonicalTwoStripOutsideClusterBucketInput threshold
            (pntHybridAffineSelectedGoodHeight beta
              (pntParametricTwoStripSigma threshold)
              (pntHybridCanonicalTwoStripTau threshold upper)
              selection x) S).layer i,
          kappa i ≤ ‖rho‖ := by
  rcases exists_positive_normLowerBound_of_isNontrivialZero with
    ⟨bound, hbound, hnorm⟩
  refine ⟨fun _ => bound, fun _ => hbound, ?_⟩
  intro i x rho hrho
  have houtside :=
    mem_positiveNontrivialZerosOutsideClusterFinset.mp
      (Finset.mem_filter.mp hrho).1
  exact hnorm rho houtside.1

/--
Canonical bidirectional PNT transfer with automatic kernel norm guards.

Compared with
`actualHybridCanonicalOutsideClusterCapPNTBidirectionalTransfer`, the caller
no longer supplies `kappa`, its positivity, or any pointwise denominator
bound. The remaining analytic inputs are the global outside-cluster
real-part cap and the external cluster oscillation witness.
-/
theorem actualHybridCanonicalAutomaticKernelGuardPNTBidirectionalTransfer
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
    (hS : IsConjugationInvariantCluster S)
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
  rcases exists_canonicalTwoStripKernelNormGuards
      beta threshold upper selection S with
    ⟨kappa, hkappa, hnorm⟩
  exact
    actualHybridCanonicalOutsideClusterCapPNTBidirectionalTransfer
      hbeta hbetaOne hc hhalf hthresholdOne hupper hlow hhigh
      selection kappa hS hkappa hnorm hcap hmain

end PrimeNumberTheorem
