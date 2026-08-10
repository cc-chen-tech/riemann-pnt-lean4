import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryDominatedTail
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryTruncatedSplit
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageVisibleClusterTransfer

/-!
# Complete actual tail outside a dynamic boundary package

The moving equal-real-part package absorbs every boundary zero visible at the
selected height.  For the positive-ordinate complement, a low strip with a
fixed real-part gap is combined with the dominated-convergence Carlson high
tail.  Conjugation then recovers the negative ordinates, while the
real-ordinate residual remains a separate, explicit input.

The resulting theorem controls the genuine signed complementary term from the
explicit formula at the target scale.  It does not assert an oscillation
theorem: the dynamic package main term still requires a separate
anti-cancellation argument.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- The selected low positive-ordinate layer, normalized at the target zero
amplitude. -/
noncomputable def actualDynamicBoundaryLowNormalizedSum
    {n : ℕ} (H : ℝ → ℝ) (beta : ℝ)
    (input :
      (m : ℕ) →
        PositiveZeroOutsideClusterBucketInput
          (H (m : ℝ))
          (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) n)
    (i : Fin n) (m : ℕ) : ℝ :=
  ‖∑ rho ∈ (input m).layer i,
      pntRelativeZeroContribution (m : ℝ) rho‖ /
    targetZeroPowerAmplitude beta (m : ℝ)

/-- The complete positive-ordinate complement outside the moving boundary
package, normalized at the target zero amplitude. -/
noncomputable def actualDynamicBoundaryPositiveNormalizedSum
    (H : ℝ → ℝ) (beta : ℝ) (m : ℕ) : ℝ :=
  dynamicPositiveOutsideClusterPNTTailNorm H
      (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) (m : ℝ) /
    targetZeroPowerAmplitude beta (m : ℝ)

/-- The real-ordinate complement outside the moving boundary package,
normalized at the target zero amplitude. -/
noncomputable def actualDynamicBoundaryRealNormalizedSum
    (H : ℝ → ℝ) (beta : ℝ) (m : ℕ) : ℝ :=
  dynamicRealOrdinateOutsideClusterPNTZeroTailNorm H
      (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) (m : ℝ) /
    targetZeroPowerAmplitude beta (m : ℝ)

/-- The complete zero complement outside the moving boundary package,
normalized at the target zero amplitude. -/
noncomputable def actualDynamicBoundaryFullNormalizedSum
    (H : ℝ → ℝ) (beta : ℝ) (m : ℕ) : ℝ :=
  dynamicFullOutsideClusterPNTZeroTailNorm H
      (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) (m : ℝ) /
    targetZeroPowerAmplitude beta (m : ℝ)

/--
A negligible fixed-gap low layer and the summable Carlson high tail imply
decay of the complete positive-ordinate complement outside the moving
boundary package.
-/
theorem actualDynamicBoundaryPositiveNormalizedSum_tendsto_zero
    {n : ℕ} {sigma beta : ℝ} {H : ℝ → ℝ}
    (input :
      (m : ℕ) →
        PositiveZeroOutsideClusterBucketInput
          (H (m : ℝ))
          (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) n)
    (i : Fin n)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hH : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (hreLow :
      ∀ m, ∀ rho ∈ (input m).layer i, rho.re ≤ sigma)
    (hlowCover :
      ∀ m : ℕ,
        ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset
            (H (m : ℝ))
            (dynamicEqualRealPartZeroPackage H beta (m : ℝ)),
          rho.re ≤ sigma → (input m).bucket rho = i)
    (hright :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hlow :
      Tendsto
        (actualDynamicBoundaryLowNormalizedSum H beta input i)
        atTop (nhds 0)) :
    Tendsto
      (actualDynamicBoundaryPositiveNormalizedSum H beta)
      atTop (nhds 0) := by
  have hhigh :
      Tendsto
        (fun m : ℕ =>
          actualCarlsonOutsideClusterNormalizedKernelTail
            (sigma := sigma) beta
            (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) m)
        atTop (nhds 0) :=
    actualCarlsonDynamicBoundaryNormalizedKernelTail_tendsto_zero
      hhalf hone hH hright
  have hmajor :
      Tendsto
        (fun m : ℕ =>
          actualDynamicBoundaryLowNormalizedSum H beta input i m +
            actualCarlsonOutsideClusterNormalizedKernelTail
              (sigma := sigma) beta
              (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) m)
        atTop (nhds 0) := by
    simpa using hlow.add hhigh
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact div_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le m)) _)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hsplit :=
      truncatedPositiveZeroKernelSum_div_target_le_low_add_CarlsonTail_of_le
        (input m) i (hreLow m) (hlowCover m)
        hhalf hone (fun index _ => hright index) hm
    simpa [actualDynamicBoundaryPositiveNormalizedSum,
      actualDynamicBoundaryLowNormalizedSum,
      dynamicPositiveOutsideClusterPNTTailNorm,
      targetZeroPowerAmplitude] using hsplit

/--
After restoring negative ordinates by conjugation, positive-tail decay and
real-ordinate decay imply decay of the complete moving-package zero tail.
-/
theorem actualDynamicBoundaryFullNormalizedSum_tendsto_zero
    {beta : ℝ} {H : ℝ → ℝ}
    (hpositive :
      Tendsto
        (actualDynamicBoundaryPositiveNormalizedSum H beta)
        atTop (nhds 0))
    (hreal :
      Tendsto
        (actualDynamicBoundaryRealNormalizedSum H beta)
        atTop (nhds 0)) :
    Tendsto
      (actualDynamicBoundaryFullNormalizedSum H beta)
      atTop (nhds 0) := by
  have hmajor :
      Tendsto
        (fun m =>
          2 * actualDynamicBoundaryPositiveNormalizedSum H beta m +
            actualDynamicBoundaryRealNormalizedSum H beta m)
        atTop (nhds 0) := by
    convert (hpositive.const_mul 2).add hreal using 1 <;> norm_num
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact div_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le m)) _)
  · filter_upwards [eventually_gt_atTop (0 : ℕ),
      eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta)] with
        m hm hAmplitude
    have hcluster :
        IsConjugationInvariantCluster
          (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) := by
      exact equalRealPartZeroPackage_isConjugationInvariant
        (H (m : ℝ)) beta
    have htail :=
      dynamicFullOutsideClusterPNTZeroTailNorm_le_two_positive_add_real
        (T := H) hcluster
          (show 0 < (m : ℝ) by exact_mod_cast hm)
    have hdivided :=
      (div_le_div_iff_of_pos_right hAmplitude).2 htail
    simpa [actualDynamicBoundaryFullNormalizedSum,
      actualDynamicBoundaryPositiveNormalizedSum,
      actualDynamicBoundaryRealNormalizedSum, add_div, two_mul] using hdivided

/--
The genuine signed complementary-zero term in the explicit formula is
negligible at the target amplitude once the complete moving-package tail is.
-/
theorem
    abs_dynamicOutsideDynamicBoundaryPNTComplement_div_target_tendsto_zero
    {beta : ℝ} {H : ℝ → ℝ}
    (hfull :
      Tendsto
        (actualDynamicBoundaryFullNormalizedSum H beta)
        atTop (nhds 0)) :
    Tendsto
      (fun m : ℕ =>
        |dynamicOutsideClusterPNTComplement H
            (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) (m : ℝ)| /
          targetZeroPowerAmplitude beta (m : ℝ))
      atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ hfull
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact div_nonneg (abs_nonneg _)
      (Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le m)) _)
  · filter_upwards [
      eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta)] with
        m hAmplitude
    exact (div_le_div_iff_of_pos_right hAmplitude).2
      (abs_dynamicOutsideClusterPNTComplement_le_tailNorm H
        (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) (m : ℝ))

end PrimeNumberTheorem
