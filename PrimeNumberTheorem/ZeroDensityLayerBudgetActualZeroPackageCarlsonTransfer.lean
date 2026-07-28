import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageVisibleClusterTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClusterComplementUnifiedTransfer

/-!
# Actual zero-package energy in the Carlson PNT transfer

The existing actual Carlson transfer normalizes the target power coefficient
to one.  The equal-real-part mean-square theorem instead supplies the exact
coefficient `sqrt(energy)`.  This module preserves that coefficient throughout
the normalized residual estimates and the final PNT witness.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter
open ZeroForcedOscillation

/-- Target-negligibility is unchanged when the target amplitude is multiplied
by a fixed positive coefficient. -/
theorem TargetAmplitudeNegligible.const_mul_amplitude
    {amplitude remainder : ℝ → ℝ}
    (hnegligible : TargetAmplitudeNegligible amplitude remainder)
    (c : ℝ) :
    TargetAmplitudeNegligible (fun x => c * amplitude x) remainder := by
  unfold TargetAmplitudeNegligible at hnegligible ⊢
  have hscaled :
      Tendsto
        (fun x => c⁻¹ * (|remainder x| / amplitude x))
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hnegligible
  apply hscaled.congr'
  exact Filter.Eventually.of_forall fun x => by
    simp only [div_eq_mul_inv, mul_inv]
    ring

/-- A cluster-excluded complement certificate can be normalized by any fixed
positive multiple of its original amplitude. -/
theorem ClusterExcludedTargetComplementCertificate.const_mul_amplitude
    {amplitude complement excludedTailNorm : ℝ → ℝ}
    (certificate :
      ClusterExcludedTargetComplementCertificate
        amplitude complement excludedTailNorm)
    {c : ℝ} (hc : 0 < c) :
    ClusterExcludedTargetComplementCertificate
      (fun x => c * amplitude x) complement excludedTailNorm where
  amplitude_eventually_pos := by
    filter_upwards [certificate.amplitude_eventually_pos] with x hx
    exact mul_pos hc hx
  complement_dominated := certificate.complement_dominated
  excluded_tail_negligible :=
    certificate.excluded_tail_negligible.const_mul_amplitude c

/--
Concrete coefficient-preserving Carlson transfer for the actual
equal-real-part zeta package.

The conclusion combines:

* the parametric PNT upper bound;
* the actual equal-real-part mean-square witness;
* the actual cluster-excluded Carlson tail;
* the actual polynomial-height explicit-formula remainder.

The only lower coefficient is the audited
`sqrt(actualEqualRealPartZeroPackageEnergy T beta L)`, and the common transfer
loses exactly a factor `1 / 2`.
-/
theorem
    unified_parametricPNTUpper_actualZeroPackageEnergyCarlsonLower
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {T beta alpha : ℝ} (hbeta : 0 < beta)
    (L : ℝ) (hL : 0 < L)
    (henergy : 0 < actualEqualRealPartZeroPackageEnergy T beta L)
    (hmargin : 1 - beta < alpha)
    {n : ℕ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x)
          (equalRealPartZeroPackage T beta) n}
    (certificate :
      ActualCarlsonOutsideClusterFiniteStripCertificate
        beta alpha (equalRealPartZeroPackage T beta) n input)
    (remainderCertificate :
      ActualPolynomialExplicitFormulaRemainderCertificate alpha) :
    (∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0)) ∧
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x =>
        (Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
            targetZeroPowerAmplitude beta x) / 2) := by
  let c := Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L)
  have hc : 0 < c := Real.sqrt_pos.2 henergy
  have hheight :
      Tendsto (carlsonPolynomialHeight alpha) atTop atTop := by
    simpa [carlsonPolynomialHeight] using
      (tendsto_rpow_atTop certificate.alpha_pos)
  have hmain :
      HasFarTargetAmplitudeWitness
        (dynamicVisibleClusterPNTMain
          (carlsonPolynomialHeight alpha)
          (equalRealPartZeroPackage T beta))
        (fun x => c * targetZeroPowerAmplitude beta x) := by
    exact
      hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster
        (carlsonPolynomialHeight alpha) hheight T beta L hL
  have hcomplement :=
    certificate.actualSignedComplementCertificate.const_mul_amplitude hc
  have hclosed :
      TargetAmplitudeNegligible
        (fun x => c * targetZeroPowerAmplitude beta x)
        actualPNTClosedRealAxisRelativeTerm :=
    TargetAmplitudeNegligible.const_mul_amplitude
      (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible hbeta) c
  have hremainder :
      TargetAmplitudeNegligible
        (fun x => c * targetZeroPowerAmplitude beta x)
        (actualPNTExplicitFormulaRelativeRemainder
          (carlsonPolynomialHeight alpha)) :=
    TargetAmplitudeNegligible.const_mul_amplitude
      (remainderCertificate.targetAmplitudeNegligible hmargin) c
  exact
    unified_parametricPNTUpper_clusterExcludedComplementLower
      threshold hhalf hlt hcomplement hclosed hremainder hmain
      (relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
        (carlsonPolynomialHeight alpha)
        (equalRealPartZeroPackage T beta))

end PrimeNumberTheorem
