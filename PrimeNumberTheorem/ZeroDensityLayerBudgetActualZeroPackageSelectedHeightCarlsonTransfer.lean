import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageEnergyPositive
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightUnifiedTransfer

/-!
# Actual zero-package energy at a Carlson-selected height

This module combines the exact mean-square coefficient of an actual finite
equal-real-part zeta-zero package with the existing selected-good-height
Carlson complement and selected-height explicit-formula remainder.

Unlike the normalized selected-height facade, the lower-bound amplitude keeps
the coefficient `sqrt(actualEqualRealPartZeroPackageEnergy T beta L)`.
-/

namespace PrimeNumberTheorem

open Filter ZeroForcedOscillation

/-- Selected-height Pintz--Carlson--explicit-formula transfer preserving the
actual finite zero-package energy coefficient. -/
theorem
    unified_parametricPNTUpper_actualZeroPackageEnergySelectedHeightCarlsonLower
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {T beta alpha : ℝ} (hbeta : 0 < beta)
    (L : ℝ) (hL : 0 < L)
    (henergy : 0 < actualEqualRealPartZeroPackageEnergy T beta L)
    (hmargin : 1 - beta < alpha)
    {n : ℕ} {H : ℝ → ℝ}
    (hH : Tendsto H atTop atTop)
    {input : (x : ℝ) →
      PositiveZeroOutsideClusterBucketInput
        (H x) (equalRealPartZeroPackage T beta) n}
    (certificate :
      ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate beta alpha
        (equalRealPartZeroPackage T beta) n H input)
    (remainderCertificate :
      ActualSelectedHeightExplicitFormulaRemainderCertificate alpha H) :
    (∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0)) ∧
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x =>
        Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
            targetZeroPowerAmplitude beta x /
          2) := by
  let c := Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L)
  have hc : 0 < c := Real.sqrt_pos.2 henergy
  have hcomplement :
      ClusterExcludedTargetComplementCertificate
        (fun x => c * targetZeroPowerAmplitude beta x)
        (dynamicOutsideClusterPNTComplement H
          (equalRealPartZeroPackage T beta))
        (dynamicFullOutsideClusterPNTZeroTailNorm H
          (equalRealPartZeroPackage T beta)) :=
    certificate.actualSignedComplementCertificate.const_mul_amplitude hc
  have hreal :
      TargetAmplitudeNegligible
        (fun x => c * targetZeroPowerAmplitude beta x)
        actualPNTClosedRealAxisRelativeTerm :=
    TargetAmplitudeNegligible.const_mul_amplitude
      (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible hbeta) c
  have hcontour :
      TargetAmplitudeNegligible
        (fun x => c * targetZeroPowerAmplitude beta x)
        (actualPNTExplicitFormulaRelativeRemainder H) :=
    TargetAmplitudeNegligible.const_mul_amplitude
      (remainderCertificate.targetAmplitudeNegligible hmargin) c
  have hmain :
      HasFarTargetAmplitudeWitness
        (dynamicVisibleClusterPNTMain H
          (equalRealPartZeroPackage T beta))
        (fun x => c * targetZeroPowerAmplitude beta x) := by
    simpa [c] using
      hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster
        H hH T beta L hL
  simpa [c] using
    unified_parametricPNTUpper_clusterExcludedComplementLower
      threshold hhalf hlt hcomplement hreal hcontour hmain
        (fun x =>
          relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
            H (equalRealPartZeroPackage T beta) x)

/-- The selected-height energy-preserving transfer with the logarithmic
window chosen automatically from nonemptiness of the actual package. -/
theorem
    unified_parametricPNTUpper_actualZeroPackageSelectedHeightCarlsonLower_of_nonempty
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {T beta alpha : ℝ} (hbeta : 0 < beta)
    (hnonempty : (equalRealPartZeroPackage T beta).Nonempty)
    (hmargin : 1 - beta < alpha)
    {n : ℕ} {H : ℝ → ℝ}
    (hH : Tendsto H atTop atTop)
    {input : (x : ℝ) →
      PositiveZeroOutsideClusterBucketInput
        (H x) (equalRealPartZeroPackage T beta) n}
    (certificate :
      ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate beta alpha
        (equalRealPartZeroPackage T beta) n H input)
    (remainderCertificate :
      ActualSelectedHeightExplicitFormulaRemainderCertificate alpha H) :
    ∃ L : ℝ, 0 < L ∧
      ((∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
        Tendsto
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          atTop (nhds 0)) ∧
      HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x =>
          Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
              targetZeroPowerAmplitude beta x /
            2)) := by
  obtain ⟨L, hL, henergy⟩ :=
    exists_actualEqualRealPartZeroPackageEnergy_pos_of_nonempty hnonempty
  exact ⟨L, hL,
    unified_parametricPNTUpper_actualZeroPackageEnergySelectedHeightCarlsonLower
      threshold hhalf hlt hbeta L hL henergy hmargin hH certificate
        remainderCertificate⟩

end PrimeNumberTheorem
