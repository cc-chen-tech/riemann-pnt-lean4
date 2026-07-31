import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingRightEdgeExceptionalCluster
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightTwoHeightFullTail

/-!
# Uniform majorants for moving-cluster complements

The low layer outside an arbitrary scale-dependent cluster is dominated by the
fixed empty-cluster polynomial-envelope mass. Combined with a pointwise high
strip cap, this yields a uniform positive-tail bound. For the moving right-edge
cluster, conjugation and complete real-ordinate capture then control the actual
signed complement.
-/

open Complex Filter
open scoped BigOperators Topology

namespace PrimeNumberTheorem

/-- A selected layer outside the moving cluster is contained in the
polynomial-envelope layer outside the empty cluster. -/
theorem canonicalMovingSelectedLayer_subset_emptyPolynomialLayer
    {H : ℝ → ℝ} {S : ℝ → Finset ℂ}
    {alpha sigma x : ℝ} (i : Fin 2)
    (hHle : H x ≤ carlsonPolynomialHeight alpha x) :
    (pntHybridCanonicalTwoStripOutsideClusterBucketInput
        sigma (H x) (S x)).layer i ⊆
      (pntHybridCanonicalTwoStripOutsideClusterBucketInput
        sigma (carlsonPolynomialHeight alpha x) ∅).layer i := by
  intro rho hrho
  have hlayer := Finset.mem_filter.mp hrho
  have hselected :=
    mem_positiveNontrivialZerosOutsideClusterFinset.mp hlayer.1
  apply Finset.mem_filter.mpr
  constructor
  · apply mem_positiveNontrivialZerosOutsideClusterFinset.mpr
    exact
      ⟨hselected.1, hselected.2.1,
        hselected.2.2.1.trans hHle, by simp⟩
  · simpa [pntHybridCanonicalTwoStripOutsideClusterBucketInput] using
      hlayer.2

/-- The moving selected low-layer norm is uniformly dominated by the
empty-cluster polynomial two-height mass. -/
theorem canonicalMovingSelectedLowLayerNorm_le_emptyPolynomialTwoHeightMass
    {H : ℝ → ℝ} {S : ℝ → Finset ℂ}
    {alpha gamma sigma x : ℝ}
    (hHle : H x ≤ carlsonPolynomialHeight alpha x) :
    dynamicPositiveOutsideClusterPNTLayerNorm H (S x)
        (fun y =>
          pntHybridCanonicalTwoStripOutsideClusterBucketInput
            sigma (H y) (S x))
        0 x ≤
      dynamicOutsideClusterLowOrdinateMass
          (carlsonPolynomialHeight alpha)
          (carlsonPolynomialHeight gamma) ∅
          (fun y =>
            pntHybridCanonicalTwoStripOutsideClusterBucketInput
              sigma (carlsonPolynomialHeight alpha y) ∅)
          0 x +
        dynamicOutsideClusterHighAnnulusMass
          (carlsonPolynomialHeight alpha)
          (carlsonPolynomialHeight gamma) ∅
          (fun y =>
            pntHybridCanonicalTwoStripOutsideClusterBucketInput
              sigma (carlsonPolynomialHeight alpha y) ∅)
          0 x := by
  unfold dynamicPositiveOutsideClusterPNTLayerNorm
  calc
    ‖∑ rho ∈
        (pntHybridCanonicalTwoStripOutsideClusterBucketInput
          sigma (H x) (S x)).layer 0,
        pntRelativeZeroContribution x rho‖ ≤
      ∑ rho ∈
        (pntHybridCanonicalTwoStripOutsideClusterBucketInput
          sigma (H x) (S x)).layer 0,
        ‖pntRelativeZeroContribution x rho‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈
        (pntHybridCanonicalTwoStripOutsideClusterBucketInput
          sigma (carlsonPolynomialHeight alpha x) ∅).layer 0,
        ‖pntRelativeZeroContribution x rho‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (canonicalMovingSelectedLayer_subset_emptyPolynomialLayer
          0 hHle)
        (fun _ _ _ => norm_nonneg _)
    _ = _ :=
      dynamicOutsideClusterLayerMass_eq_low_add_high
        (carlsonPolynomialHeight alpha)
        (carlsonPolynomialHeight gamma) ∅
        (fun y =>
          pntHybridCanonicalTwoStripOutsideClusterBucketInput
            sigma (carlsonPolynomialHeight alpha y) ∅)
        0 x

/-- The moving selected high layer lies in the common actual Carlson strip
under a pointwise moving-cluster cap. -/
theorem canonicalMovingSelectedHighLayer_subset_polynomialCarlsonStrip
    {H : ℝ → ℝ} {S : ℝ → Finset ℂ}
    {alpha sigma tau x : ℝ}
    (hHle : H x ≤ carlsonPolynomialHeight alpha x)
    (hcap :
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) (S x),
        sigma < rho.re → rho.re ≤ tau) :
    (pntHybridCanonicalTwoStripOutsideClusterBucketInput
        sigma (H x) (S x)).layer 1 ⊆
      actualPositiveCarlsonStrip sigma tau
        (carlsonPolynomialHeight alpha x) := by
  intro rho hrho
  have hlayer := Finset.mem_filter.mp hrho
  have hselected :
      rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) (S x) :=
    hlayer.1
  have hmem :=
    mem_positiveNontrivialZerosOutsideClusterFinset.mp hselected
  have hright : sigma < rho.re := by
    have hbucket := hlayer.2
    by_contra hnot
    simp [pntHybridCanonicalTwoStripOutsideClusterBucketInput,
      hnot] at hbucket
  exact mem_actualPositiveCarlsonStrip.mpr
    ⟨hmem.1, hmem.2.1, hmem.2.2.1.trans hHle,
      hright, hcap rho hselected hright⟩

/-- Pointwise moving positive-tail majorant by the fixed empty-cluster low
mass and the common actual Carlson strip. -/
theorem movingSelectedPositiveOutsideClusterPNTTailNorm_le
    {H : ℝ → ℝ} {S : ℝ → Finset ℂ}
    {alpha gamma sigma tau x : ℝ}
    (hHle : H x ≤ carlsonPolynomialHeight alpha x)
    (hcap :
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) (S x),
        sigma < rho.re → rho.re ≤ tau) :
    dynamicPositiveOutsideClusterPNTTailNorm H (S x) x ≤
      (dynamicOutsideClusterLowOrdinateMass
          (carlsonPolynomialHeight alpha)
          (carlsonPolynomialHeight gamma) ∅
          (fun y =>
            pntHybridCanonicalTwoStripOutsideClusterBucketInput
              sigma (carlsonPolynomialHeight alpha y) ∅)
          0 x +
        dynamicOutsideClusterHighAnnulusMass
          (carlsonPolynomialHeight alpha)
          (carlsonPolynomialHeight gamma) ∅
          (fun y =>
            pntHybridCanonicalTwoStripOutsideClusterBucketInput
              sigma (carlsonPolynomialHeight alpha y) ∅)
          0 x) +
      ∑ rho ∈ actualPositiveCarlsonStrip sigma tau
          (carlsonPolynomialHeight alpha x),
        ‖pntRelativeZeroContribution x rho‖ := by
  let selectedInput := fun y =>
    pntHybridCanonicalTwoStripOutsideClusterBucketInput
      sigma (H y) (S x)
  calc
    dynamicPositiveOutsideClusterPNTTailNorm H (S x) x ≤
      ∑ i,
        dynamicPositiveOutsideClusterPNTLayerNorm
          H (S x) selectedInput i x :=
      dynamicPositiveOutsideClusterPNTTailNorm_le_sum_layerNorms
        selectedInput x
    _ =
      dynamicPositiveOutsideClusterPNTLayerNorm
          H (S x) selectedInput 0 x +
        dynamicPositiveOutsideClusterPNTLayerNorm
          H (S x) selectedInput 1 x := by
      rw [Fin.sum_univ_two]
    _ ≤ _ := add_le_add
      (canonicalMovingSelectedLowLayerNorm_le_emptyPolynomialTwoHeightMass
        hHle)
      (by
        unfold dynamicPositiveOutsideClusterPNTLayerNorm
        calc
          ‖∑ rho ∈
              (pntHybridCanonicalTwoStripOutsideClusterBucketInput
                sigma (H x) (S x)).layer 1,
              pntRelativeZeroContribution x rho‖ ≤
            ∑ rho ∈
              (pntHybridCanonicalTwoStripOutsideClusterBucketInput
                sigma (H x) (S x)).layer 1,
              ‖pntRelativeZeroContribution x rho‖ :=
            norm_sum_le _ _
          _ ≤ _ :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (canonicalMovingSelectedHighLayer_subset_polynomialCarlsonStrip
                hHle hcap)
              (fun _ _ _ => norm_nonneg _))

/-- Positive-tail target-amplitude decay uniformly over an arbitrary moving
cluster family. -/
theorem selectedMovingPositiveOutsideClusterTail_targetAmplitudeNegligible
    {H : ℝ → ℝ} {S : ℝ → Finset ℂ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow : gammaLow + sigma - beta + epsilonLow < 0)
    (hlowHigh :
      alpha + sigma - beta - gammaLow + epsilonLow < 0)
    (hgammaHigh : 0 < gammaHigh)
    (hgammaHighAlpha : gammaHigh ≤ alpha)
    (hepsilonHigh : 0 < epsilonHigh)
    (hstripLow :
      targetAmplitudeCarlsonTwoHeightLowExponent
          beta sigma tau gammaHigh + epsilonHigh < 0)
    (hstripHigh :
      targetAmplitudeCarlsonTwoHeightHighExponent
          beta sigma tau alpha gammaHigh + epsilonHigh < 0)
    (hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
    (hcap :
      ∀ x rho,
        rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) (S x) →
          sigma < rho.re →
            rho.re ≤ tau) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (fun x =>
        dynamicPositiveOutsideClusterPNTTailNorm H (S x) x) := by
  let polynomialInput := fun y =>
    pntHybridCanonicalTwoStripOutsideClusterBucketInput
      sigma (carlsonPolynomialHeight alpha y) ∅
  rcases
      exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
        (carlsonPolynomialHeight alpha) sigma ∅ with
    ⟨kappa, hkappa, hnorm⟩
  have hlow :=
    tendsto_dynamicOutsideClusterTwoHeightMass_div_target
      polynomialInput 0 hkappa hnorm
      (fun _ _ hrho =>
        pntHybridCanonicalTwoStripOutsideCluster_lowLayer_re_le hrho)
      halpha hgammaLow hepsilonLow hlowLow hlowHigh
  have hstrip :=
    tendsto_actualPositiveCarlsonStripTargetAmplitudeMass_twoHeight
      hsigma hsigmaOne halpha hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh
  have hmajor := hlow.add hstrip
  unfold TargetAmplitudeNegligible
  refine squeeze_zero' ?_ ?_ (by simpa using hmajor)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (abs_nonneg _)
      (Real.rpow_nonneg (zero_le_one.trans hx) _)
  · filter_upwards
      [eventually_ge_atTop (1 : ℝ), hHle] with x hx hHx
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hamp : 0 < targetZeroPowerAmplitude beta x :=
      Real.rpow_pos_of_pos hx0 _
    have hp :=
      movingSelectedPositiveOutsideClusterPNTTailNorm_le
        (S := S) (gamma := gammaLow) hHx (hcap x)
    have hdiv := (div_le_div_iff_of_pos_right hamp).2 hp
    simpa [dynamicPositiveOutsideClusterPNTTailNorm,
      actualPositiveCarlsonStripTargetAmplitudeMass, add_div] using hdiv

/-- The real-ordinate tail outside the moving right-edge exceptional cluster
is exactly zero at every nonnegative height. -/
theorem movingRightEdgeRealOrdinateOutsideTailNorm_eq_zero
    {H : ℝ → ℝ} {tau x : ℝ}
    (hH : 0 ≤ H x) :
    dynamicRealOrdinateOutsideClusterPNTZeroTailNorm H
      (movingRightEdgeExceptionalCluster H tau x) x = 0 := by
  have hset :
      realOrdinateNontrivialZerosOutsideClusterFinset (H x)
          (movingRightEdgeExceptionalCluster H tau x) = ∅ := by
    rw [realOrdinateNontrivialZerosOutsideClusterFinset_eq_zeroHeight hH]
    unfold movingRightEdgeExceptionalCluster
    exact
      realOrdinateNontrivialZerosOutsideClusterFinset_adjoin_eq_empty
        (rightEdgeNontrivialZerosFinset tau (H x))
  unfold dynamicRealOrdinateOutsideClusterPNTZeroTailNorm
  rw [hset]
  simp

/-- Full outside-tail norm for the moving right-edge exceptional cluster. -/
noncomputable def movingRightEdgeFullOutsideClusterPNTZeroTailNorm
    (H : ℝ → ℝ) (tau x : ℝ) : ℝ :=
  dynamicFullOutsideClusterPNTZeroTailNorm H
    (movingRightEdgeExceptionalCluster H tau x) x

/-- The complete moving outside-cluster zero tail is negligible at the target
amplitude. -/
theorem selectedMovingRightEdgeFullOutsideClusterTail_targetAmplitudeNegligible
    {H : ℝ → ℝ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow : gammaLow + sigma - beta + epsilonLow < 0)
    (hlowHigh :
      alpha + sigma - beta - gammaLow + epsilonLow < 0)
    (hgammaHigh : 0 < gammaHigh)
    (hgammaHighAlpha : gammaHigh ≤ alpha)
    (hepsilonHigh : 0 < epsilonHigh)
    (hstripLow :
      targetAmplitudeCarlsonTwoHeightLowExponent
          beta sigma tau gammaHigh + epsilonHigh < 0)
    (hstripHigh :
      targetAmplitudeCarlsonTwoHeightHighExponent
          beta sigma tau alpha gammaHigh + epsilonHigh < 0)
    (hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x)
    (hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (movingRightEdgeFullOutsideClusterPNTZeroTailNorm H tau) := by
  let S := movingRightEdgeExceptionalCluster H tau
  have hcap :
      ∀ x rho,
        rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) (S x) →
          sigma < rho.re →
            rho.re ≤ tau := by
    intro x rho hrho _hright
    rcases mem_positiveNontrivialZerosOutsideClusterFinset.mp hrho with
      ⟨hzero, him, hheight, hout⟩
    exact
      (positiveNontrivialZero_re_lt_of_not_mem_movingRightEdgeExceptionalCluster
        hzero him hheight hout).le
  have hpositive :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        (fun x =>
          dynamicPositiveOutsideClusterPNTTailNorm H (S x) x) :=
    selectedMovingPositiveOutsideClusterTail_targetAmplitudeNegligible
      hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh hHle hcap
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
      0 ≤
        dynamicFullOutsideClusterPNTZeroTailNorm H
          (movingRightEdgeExceptionalCluster H tau x) x :=
    norm_nonneg _
  unfold movingRightEdgeFullOutsideClusterPNTZeroTailNorm
  rw [abs_of_nonneg hfullNonneg]
  simpa [S] using hfull

/-- The actual signed complement outside the moving right-edge exceptional
cluster is negligible at the target amplitude. -/
theorem
    selectedMovingRightEdgeOutsideClusterComplement_targetAmplitudeNegligible
    {H : ℝ → ℝ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow : gammaLow + sigma - beta + epsilonLow < 0)
    (hlowHigh :
      alpha + sigma - beta - gammaLow + epsilonLow < 0)
    (hgammaHigh : 0 < gammaHigh)
    (hgammaHighAlpha : gammaHigh ≤ alpha)
    (hepsilonHigh : 0 < epsilonHigh)
    (hstripLow :
      targetAmplitudeCarlsonTwoHeightLowExponent
          beta sigma tau gammaHigh + epsilonHigh < 0)
    (hstripHigh :
      targetAmplitudeCarlsonTwoHeightHighExponent
          beta sigma tau alpha gammaHigh + epsilonHigh < 0)
    (hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x)
    (hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (movingRightEdgeOutsideClusterPNTComplement H tau) := by
  have hfull :=
    selectedMovingRightEdgeFullOutsideClusterTail_targetAmplitudeNegligible
      hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh hHnonneg hHle
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

end PrimeNumberTheorem
