import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageNaturalSampling

/-!
# Natural-point witnesses from the actual equal-real-part zero package

This module transfers the continuous far witness supplied by the actual
equal-real-part zeta-zero package to natural-number evaluation points.

The energy positivity assumption is explicit.  The output is a witness for the
zero-package main term, not yet for the full PNT error.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

theorem tendsto_abs_actualEqualRealPartZeroPackagePNTMain_re_natFloor_error
    (T beta : ℝ) :
    Tendsto
      (fun x =>
        |(actualEqualRealPartZeroPackagePNTMain (Nat.floor x) T beta).re -
            (actualEqualRealPartZeroPackagePNTMain x T beta).re| /
          targetZeroPowerAmplitude beta x)
      atTop (𝓝 0) := by
  apply squeeze_zero'
    (g := fun x =>
      ‖actualEqualRealPartZeroPackagePNTMain (Nat.floor x) T beta -
          actualEqualRealPartZeroPackagePNTMain x T beta‖ /
        targetZeroPowerAmplitude beta x)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_nonneg (abs_nonneg _)
      (le_of_lt (Real.rpow_pos_of_pos hx (beta - 1)))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hA : 0 ≤ targetZeroPowerAmplitude beta x :=
      le_of_lt (Real.rpow_pos_of_pos hx (beta - 1))
    exact div_le_div_of_nonneg_right
      (by
        have hre := Complex.abs_re_le_norm
          (actualEqualRealPartZeroPackagePNTMain (Nat.floor x) T beta -
            actualEqualRealPartZeroPackagePNTMain x T beta)
        simpa only [Complex.sub_re] using hre)
      hA
  · exact tendsto_actualEqualRealPartZeroPackagePNTMain_natFloor_error T beta

theorem tendsto_abs_actualEqualRealPartZeroPackagePNTMain_re_natFloor_error_scaled
    {T beta L : ℝ} (henergy : 0 < actualEqualRealPartZeroPackageEnergy T beta L) :
    Tendsto
      (fun x =>
        |(actualEqualRealPartZeroPackagePNTMain (Nat.floor x) T beta).re -
            (actualEqualRealPartZeroPackagePNTMain x T beta).re| /
          (Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
            targetZeroPowerAmplitude beta x))
      atTop (𝓝 0) := by
  have hc : Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) ≠ 0 :=
    Real.sqrt_ne_zero'.2 henergy
  have hbase :=
    (tendsto_abs_actualEqualRealPartZeroPackagePNTMain_re_natFloor_error T beta).div_const
      (Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L))
  refine Tendsto.congr' ?_ (by simpa using hbase)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hA : targetZeroPowerAmplitude beta x ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hx (beta - 1))
  field_simp [hc, hA]

theorem tendsto_dynamicVisibleClusterPNTMain_actualZeroPackage_natFloor_error
    (H : ℝ → ℝ) (hH : Tendsto H atTop atTop)
    {T beta L : ℝ} (henergy : 0 < actualEqualRealPartZeroPackageEnergy T beta L) :
    Tendsto
      (fun x =>
        |dynamicVisibleClusterPNTMain H
              (ZeroForcedOscillation.equalRealPartZeroPackage T beta) (Nat.floor x) -
            dynamicVisibleClusterPNTMain H
              (ZeroForcedOscillation.equalRealPartZeroPackage T beta) x| /
          (Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
            targetZeroPowerAmplitude beta x))
      atTop (𝓝 0) := by
  have hfloorTop : Tendsto (fun x : ℝ => (Nat.floor x : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_nat_floor_atTop
  have hHx : ∀ᶠ x : ℝ in atTop, T ≤ H x :=
    hH.eventually_ge_atTop T
  have hHfloor : ∀ᶠ x : ℝ in atTop, T ≤ H (Nat.floor x) :=
    (hH.comp hfloorTop).eventually_ge_atTop T
  refine Tendsto.congr' ?_
    (tendsto_abs_actualEqualRealPartZeroPackagePNTMain_re_natFloor_error_scaled
      henergy)
  filter_upwards [hHx, hHfloor] with x hx hfloor
  simp only [dynamicVisibleClusterPNTMain]
  rw [dynamicVisibleClusterPNTZeroSum_eq_actualZeroPackagePNTMain H hfloor,
    dynamicVisibleClusterPNTZeroSum_eq_actualZeroPackagePNTMain H hx]

theorem hasFarNaturalPointTargetAmplitudeWitness_actualZeroPackage_visibleCluster
    (H : ℝ → ℝ) (hH : Tendsto H atTop atTop)
    (T beta L q : ℝ) (hL : 0 < L)
    (henergy : 0 < actualEqualRealPartZeroPackageEnergy T beta L)
    (hq : q < 1) :
    HasFarNaturalPointTargetAmplitudeWitness
      (fun m =>
        dynamicVisibleClusterPNTMain H
          (ZeroForcedOscillation.equalRealPartZeroPackage T beta) m)
      (fun m =>
        q * (Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
          targetZeroPowerAmplitude beta m)) := by
  let amplitude : ℝ → ℝ := fun x =>
    Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
      targetZeroPowerAmplitude beta x
  have hc : 0 < Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) :=
    Real.sqrt_pos.2 henergy
  apply HasFarTargetAmplitudeWitness.toNatural_natFloor_of_normalized_stability
    (f := dynamicVisibleClusterPNTMain H
      (ZeroForcedOscillation.equalRealPartZeroPackage T beta))
    (amplitude := amplitude)
    hq
    (hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster
      H hH T beta L hL)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos hc (Real.rpow_pos_of_pos hx (beta - 1))
  · have hratio := targetZeroPowerAmplitude_natFloor_ratio_tendsto beta
    refine Tendsto.congr' ?_ hratio
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hA : targetZeroPowerAmplitude beta x ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hx (beta - 1))
    dsimp [amplitude]
    field_simp [ne_of_gt hc, hA]
  · simpa [amplitude] using
      tendsto_dynamicVisibleClusterPNTMain_actualZeroPackage_natFloor_error
        H hH henergy

end PrimeNumberTheorem
