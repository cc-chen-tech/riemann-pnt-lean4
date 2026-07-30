import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageNaturalWitness
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalTransfer

/-!
# Full PNT lower transfer from the naturally sampled actual zero package

The actual equal-real-part zero package now supplies the natural-point main
witness required by the selected-height explicit-formula lower assembler.
This module performs the final conditional assembly at the exact package-energy
scale.

The Carlson good-height certificate and the natural-point contour remainder
certificate remain explicit hypotheses.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

/--
Negligibility relative to an amplitude is preserved when the amplitude is
multiplied by a nonzero constant.
-/
theorem NaturalPointTargetAmplitudeNegligible.const_mul_amplitude
    {amplitude remainder : ℕ → ℝ} (c : ℝ)
    (h : NaturalPointTargetAmplitudeNegligible amplitude remainder) :
    NaturalPointTargetAmplitudeNegligible
      (fun m => c * amplitude m) remainder := by
  unfold NaturalPointTargetAmplitudeNegligible at h ⊢
  have hscaled := h.div_const c
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled

/--
Conditional full relative-PNT lower transfer from an actual equal-real-part
zero package.

The retained amplitude is the naturally sampled package amplitude, with the
strict floor loss `q < 1` and the standard factor `1/2` used to absorb the
three negligible remainders.
-/
theorem actualZeroPackage_naturalPointRemainder_lowerTransfer
    {beta alpha : ℝ} (hbeta : 0 < beta)
    {n : ℕ} {H : ℝ → ℝ}
    (hH : Tendsto H atTop atTop)
    {T L q : ℝ} (hL : 0 < L)
    (henergy : 0 < actualEqualRealPartZeroPackageEnergy T beta L)
    (hqpos : 0 < q) (hq : q < 1)
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (H x) (ZeroForcedOscillation.equalRealPartZeroPackage T beta) n}
    (certificate :
      ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate
        beta alpha (ZeroForcedOscillation.equalRealPartZeroPackage T beta)
          n H input)
    (remainderCertificate :
      ActualSelectedHeightNaturalPointRemainderCertificate beta H) :
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x =>
        (q * Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
          targetZeroPowerAmplitude beta x) / 2) := by
  let c : ℝ :=
    q * Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L)
  have hcpos : 0 < c := by
    exact mul_pos hqpos (Real.sqrt_pos.2 henergy)
  have hamplitude :
      ∀ᶠ m : ℕ in atTop,
        0 < c * targetZeroPowerAmplitude beta (m : ℝ) := by
    filter_upwards [
      eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta)] with m hm
    exact mul_pos hcpos hm
  have hrealAxis :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ => actualPNTClosedRealAxisRelativeTerm (m : ℝ)) :=
    NaturalPointTargetAmplitudeNegligible.const_mul_amplitude c
      (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible hbeta).naturalPoint
  have hcontour :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)) :=
    NaturalPointTargetAmplitudeNegligible.const_mul_amplitude c
      remainderCertificate.negligible
  have hcomplement :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          dynamicOutsideClusterPNTComplement H
            (ZeroForcedOscillation.equalRealPartZeroPackage T beta)
            (m : ℝ)) :=
    NaturalPointTargetAmplitudeNegligible.const_mul_amplitude c
      certificate.actualSignedComplementCertificate.complement_negligible.naturalPoint
  have hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (ZeroForcedOscillation.equalRealPartZeroPackage T beta) (m : ℝ))
        (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ)) := by
    simpa [c, mul_assoc] using
      hasFarNaturalPointTargetAmplitudeWitness_actualZeroPackage_visibleCluster
        H hH T beta L q hL henergy hq
  apply HasFarNaturalPointTargetAmplitudeWitness.toReal
  simpa [c, mul_assoc] using
    hasFarNaturalPointTargetAmplitudeWitness_of_three_remainders
      hamplitude hrealAxis hcontour hcomplement hmain
      (fun m =>
        relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
          H (ZeroForcedOscillation.equalRealPartZeroPackage T beta) (m : ℝ))

end PrimeNumberTheorem
