import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingClusterComplementMajorant
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualReciprocalOutsideClusterLowLayer

/-!
# Reciprocal control of moving-cluster complements

The complement of a moving right-edge cluster is already a single strict
real-part layer.  Keeping the reciprocal zero coefficient inside that layer
removes the polynomial-height loss from the old two-height majorant.  Hence
the complete moving complement is negligible at `x^(beta-1)` whenever its
real-part cap `tau` is strictly below `beta`.
-/

open Complex Filter
open scoped BigOperators Topology

namespace PrimeNumberTheorem

noncomputable section

/-- Pointwise reciprocal-mass bound for the positive tail outside an
arbitrary scale-dependent cluster. -/
theorem movingPositiveOutsideClusterPNTTailNorm_le_rpow_mul_globalReciprocal
    {H : ℝ → ℝ} {S : ℝ → Finset ℂ} {tau x : ℝ}
    (hx : 1 ≤ x)
    (hcap : ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) (S x),
      rho.re ≤ tau) :
    dynamicPositiveOutsideClusterPNTTailNorm H (S x) x ≤
      x ^ (tau - 1) *
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity (H x) := by
  let input :=
    pntHybridCanonicalTwoStripOutsideClusterBucketInput tau (H x) (S x)
  have hre : ∀ rho ∈ input.layer (0 : Fin 2), rho.re ≤ tau := by
    intro rho hrho
    exact pntHybridCanonicalTwoStripOutsideCluster_lowLayer_re_le hrho
  have hcover :
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) (S x),
        rho.re ≤ tau → input.bucket rho = (0 : Fin 2) := by
    intro rho hrho hrhoRe
    exact pntHybridCanonicalTwoStripOutsideCluster_low_cover hrho hrhoRe
  have hlayer :
      input.layer (0 : Fin 2) =
        positiveNontrivialZerosOutsideClusterFinset (H x) (S x) := by
    rw [lowLayer_eq_filter_re_le input (0 : Fin 2) hre hcover]
    exact Finset.filter_eq_self.mpr hcap
  unfold dynamicPositiveOutsideClusterPNTTailNorm
  rw [← hlayer]
  exact input.norm_layer_sum_le_rpow_mul_globalReciprocal
    (0 : Fin 2) hx hre

/-- A moving positive outside tail with uniform cap `Re rho <= tau` is
negligible on the target `x^(beta-1)` scale under the reciprocal margin. -/
theorem tendsto_movingPositiveOutsideClusterPNTTailNorm_div_target_zero_reciprocal
    {H : ℝ → ℝ} {S : ℝ → Finset ℂ}
    {beta tau alpha epsilon : ℝ}
    (hHle : ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : tau - beta + epsilon < 0)
    (hcap : ∀ x rho,
      rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) (S x) →
        rho.re ≤ tau) :
    Tendsto
      (fun x : ℝ =>
        dynamicPositiveOutsideClusterPNTTailNorm H (S x) x /
          targetZeroPowerAmplitude beta x)
      atTop (nhds 0) := by
  rcases ExplicitFormulaAux.exists_globalReciprocalZeroMultiplicity_le_log_sq with
    ⟨C, hC, hglobal⟩
  have hlog :=
    eventually_one_add_log_polynomialHeight_add_six_le_log_four halpha
  have hmajor :
      Tendsto
        (actualReciprocalLowNormalizedLogPowerMajorant C alpha beta tau)
        atTop (nhds 0) :=
    tendsto_actualReciprocalLowNormalizedLogPowerMajorant_zero
      hepsilon hmargin
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (zero_le_one.trans hx) _)
  · filter_upwards [
      eventually_ge_atTop (1 : ℝ),
      hHtop.eventually (eventually_ge_atTop (4 : ℝ)),
      hHle, hlog] with x hx hHfour hHupper hlogBound
    have hxPos : 0 < x := zero_lt_one.trans_le hx
    have hxNonneg : 0 ≤ x := hxPos.le
    have hAmplitude : 0 < targetZeroPowerAmplitude beta x :=
      Real.rpow_pos_of_pos hxPos _
    have hphysical :=
      movingPositiveOutsideClusterPNTTailNorm_le_rpow_mul_globalReciprocal
        hx (hcap x)
    have hglobalBound :
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity (H x) ≤
          C * (1 + Real.log (H x + 6)) ^ 2 :=
      hglobal (H x) hHfour
    have hlogMono :
        1 + Real.log (H x + 6) ≤
          1 + Real.log (x ^ alpha + 6) := by
      have hlogRaw :
          Real.log (H x + 6) ≤ Real.log (x ^ alpha + 6) := by
        apply Real.log_le_log
        · linarith
        · simpa [carlsonPolynomialHeight] using hHupper
      linarith
    have hleftNonneg : 0 ≤ 1 + Real.log (H x + 6) := by
      have hlogPos : 0 < Real.log (H x + 6) :=
        Real.log_pos (by linarith)
      linarith
    have hlogCombined :
        1 + Real.log (H x + 6) ≤
          (alpha + 2) * Real.log x ^ 4 :=
      hlogMono.trans hlogBound
    have hrightNonneg :
        0 ≤ (alpha + 2) * Real.log x ^ 4 :=
      hleftNonneg.trans hlogCombined
    have hfactorNonneg :
        0 ≤
          ((alpha + 2) * Real.log x ^ 4 -
              (1 + Real.log (H x + 6))) *
            ((alpha + 2) * Real.log x ^ 4 +
              (1 + Real.log (H x + 6))) :=
      mul_nonneg (sub_nonneg.mpr hlogCombined)
        (add_nonneg hrightNonneg hleftNonneg)
    have hlogSquare :
        (1 + Real.log (H x + 6)) ^ 2 ≤
          ((alpha + 2) * Real.log x ^ 4) ^ 2 := by
      nlinarith
    have hreciprocal :
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity (H x) ≤
          C * ((alpha + 2) * Real.log x ^ 4) ^ 2 :=
      hglobalBound.trans
        (mul_le_mul_of_nonneg_left hlogSquare hC)
    have hphysicalBound :
        dynamicPositiveOutsideClusterPNTTailNorm H (S x) x ≤
          x ^ (tau - 1) *
            (C * ((alpha + 2) * Real.log x ^ 4) ^ 2) :=
      hphysical.trans
        (mul_le_mul_of_nonneg_left hreciprocal
          (Real.rpow_nonneg hxNonneg _))
    have hnormalized :
        dynamicPositiveOutsideClusterPNTTailNorm H (S x) x /
            targetZeroPowerAmplitude beta x ≤
          (x ^ (tau - 1) *
              (C * ((alpha + 2) * Real.log x ^ 4) ^ 2)) /
            targetZeroPowerAmplitude beta x :=
      (div_le_div_iff_of_pos_right hAmplitude).2 hphysicalBound
    calc
      dynamicPositiveOutsideClusterPNTTailNorm H (S x) x /
          targetZeroPowerAmplitude beta x
          ≤ (x ^ (tau - 1) *
                (C * ((alpha + 2) * Real.log x ^ 4) ^ 2)) /
              targetZeroPowerAmplitude beta x := hnormalized
      _ = C * ((alpha + 2) * Real.log x ^ 4) ^ 2 *
            (x ^ (tau - 1) / x ^ (beta - 1)) := by
        unfold targetZeroPowerAmplitude
        ring_nf
      _ = C * ((alpha + 2) * Real.log x ^ 4) ^ 2 *
            x ^ ((tau - 1) - (beta - 1)) := by
        rw [← Real.rpow_sub hxPos]
      _ = actualReciprocalLowNormalizedLogPowerMajorant
            C alpha beta tau x := by
        unfold actualReciprocalLowNormalizedLogPowerMajorant
        ring_nf

/-- Reciprocal positive-tail negligibility outside the moving right-edge
cluster.  The only real-part condition is the strict gap `tau < beta`, encoded
by a positive epsilon margin. -/
theorem selectedMovingRightEdgePositiveOutsideClusterTail_targetAmplitudeNegligible_reciprocal
    {H : ℝ → ℝ} {beta tau alpha epsilon : ℝ}
    (hHle : ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : tau - beta + epsilon < 0) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (fun x =>
        dynamicPositiveOutsideClusterPNTTailNorm H
          (movingRightEdgeExceptionalCluster H tau x) x) := by
  have hcap : ∀ x rho,
      rho ∈ positiveNontrivialZerosOutsideClusterFinset
          (H x) (movingRightEdgeExceptionalCluster H tau x) →
        rho.re ≤ tau := by
    intro x rho hrho
    rcases mem_positiveNontrivialZerosOutsideClusterFinset.mp hrho with
      ⟨hzero, him, hheight, hout⟩
    exact
      (positiveNontrivialZero_re_lt_of_not_mem_movingRightEdgeExceptionalCluster
        hzero him hheight hout).le
  have h :=
    tendsto_movingPositiveOutsideClusterPNTTailNorm_div_target_zero_reciprocal
      (S := movingRightEdgeExceptionalCluster H tau)
      hHle hHtop halpha hepsilon hmargin hcap
  unfold TargetAmplitudeNegligible
  refine Tendsto.congr' ?_ h
  filter_upwards with x
  rw [abs_of_nonneg]
  exact norm_nonneg _

/-- The complete moving right-edge outside tail is reciprocal-negligible at
the target amplitude.  Real-ordinate zeros contribute exactly zero because
the moving cluster captures their complete finite slice. -/
theorem selectedMovingRightEdgeFullOutsideClusterTail_targetAmplitudeNegligible_reciprocal
    {H : ℝ → ℝ} {beta tau alpha epsilon : ℝ}
    (hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x)
    (hHle : ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : tau - beta + epsilon < 0) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (movingRightEdgeFullOutsideClusterPNTZeroTailNorm H tau) := by
  let S := movingRightEdgeExceptionalCluster H tau
  have hpositive :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        (fun x => dynamicPositiveOutsideClusterPNTTailNorm H (S x) x) := by
    simpa [S] using
      selectedMovingRightEdgePositiveOutsideClusterTail_targetAmplitudeNegligible_reciprocal
        hHle hHtop halpha hepsilon hmargin
  have hamplitude :
      ∀ᶠ x : ℝ in atTop, 0 < targetZeroPowerAmplitude beta x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simpa [targetZeroPowerAmplitude] using
      (Real.rpow_pos_of_pos hx (beta - 1))
  have hmajorant :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        (fun x =>
          dynamicPositiveOutsideClusterPNTTailNorm H (S x) x +
            dynamicPositiveOutsideClusterPNTTailNorm H (S x) x) :=
    hpositive.add hamplitude hpositive
  apply hmajorant.of_eventually_abs_le hamplitude
  filter_upwards [hHnonneg, eventually_gt_atTop (0 : ℝ)] with x hHx hx
  have hfull :=
    dynamicFullOutsideClusterPNTZeroTailNorm_le_two_positive_add_real
      (T := H)
      (movingRightEdgeExceptionalCluster_conjugationInvariant H tau x)
      hx
  have hreal :=
    movingRightEdgeRealOrdinateOutsideTailNorm_eq_zero
      (H := H) (tau := tau) hHx
  rw [hreal] at hfull
  have hfullNonneg :
      0 ≤ dynamicFullOutsideClusterPNTZeroTailNorm H
        (movingRightEdgeExceptionalCluster H tau x) x :=
    norm_nonneg _
  unfold movingRightEdgeFullOutsideClusterPNTZeroTailNorm
  rw [abs_of_nonneg hfullNonneg]
  simpa [S] using hfull

/-- The signed explicit-formula complement outside the moving right-edge
cluster is reciprocal-negligible under `tau - beta + epsilon < 0`. -/
theorem selectedMovingRightEdgeOutsideClusterComplement_targetAmplitudeNegligible_reciprocal
    {H : ℝ → ℝ} {beta tau alpha epsilon : ℝ}
    (hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x)
    (hHle : ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : tau - beta + epsilon < 0) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (movingRightEdgeOutsideClusterPNTComplement H tau) := by
  have hfull :=
    selectedMovingRightEdgeFullOutsideClusterTail_targetAmplitudeNegligible_reciprocal
      hHnonneg hHle hHtop halpha hepsilon hmargin
  have hamplitude :
      ∀ᶠ x : ℝ in atTop, 0 < targetZeroPowerAmplitude beta x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simpa [targetZeroPowerAmplitude] using
      (Real.rpow_pos_of_pos hx (beta - 1))
  apply hfull.of_eventually_abs_le hamplitude
  filter_upwards with x
  exact
    abs_dynamicOutsideClusterPNTComplement_le_tailNorm
      H (movingRightEdgeExceptionalCluster H tau x) x

end
end PrimeNumberTheorem
