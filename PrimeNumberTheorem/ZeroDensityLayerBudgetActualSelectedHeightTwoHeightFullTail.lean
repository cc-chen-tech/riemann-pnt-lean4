import PrimeNumberTheorem.ZeroDensityLayerBudgetActualTargetAmplitudeFullTailConjugation
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualRealOrdinateExcludingCluster

/-!
# Selected-height two-height full zero tail

A selected height dominated by the polynomial envelope inherits the
stack37 low-layer mass bound and the stack36 high-strip bound by finite-set
inclusion.
-/

open Complex Filter
open scoped BigOperators Topology

namespace PrimeNumberTheorem

/-- A canonical selected-height layer is contained in the corresponding
canonical polynomial-envelope layer. -/
theorem canonicalSelectedLayer_subset_polynomialLayer
    {H alpha sigma x : ℝ} {S : Finset ℂ} (i : Fin 2)
    (hHle : H ≤ carlsonPolynomialHeight alpha x) :
    (pntHybridCanonicalTwoStripOutsideClusterBucketInput
        sigma H S).layer i ⊆
      (pntHybridCanonicalTwoStripOutsideClusterBucketInput
        sigma (carlsonPolynomialHeight alpha x) S).layer i := by
  intro rho hrho
  have hlayer := Finset.mem_filter.mp hrho
  have hselected :=
    mem_positiveNontrivialZerosOutsideClusterFinset.mp hlayer.1
  apply Finset.mem_filter.mpr
  constructor
  · apply mem_positiveNontrivialZerosOutsideClusterFinset.mpr
    exact
      ⟨hselected.1, hselected.2.1,
        hselected.2.2.1.trans hHle, hselected.2.2.2⟩
  · simpa [pntHybridCanonicalTwoStripOutsideClusterBucketInput] using
      hlayer.2

/-- The selected canonical low-layer norm inherits the polynomial-envelope
two-height mass bound. -/
theorem canonicalSelectedLowLayerNorm_le_polynomialTwoHeightMass
    {H : ℝ → ℝ} {alpha gamma sigma x : ℝ} {S : Finset ℂ}
    (hHle : H x ≤ carlsonPolynomialHeight alpha x) :
    dynamicPositiveOutsideClusterPNTLayerNorm H S
        (fun y =>
          pntHybridCanonicalTwoStripOutsideClusterBucketInput
            sigma (H y) S)
        0 x ≤
      dynamicOutsideClusterLowOrdinateMass
          (carlsonPolynomialHeight alpha)
          (carlsonPolynomialHeight gamma) S
          (fun y =>
            pntHybridCanonicalTwoStripOutsideClusterBucketInput
              sigma (carlsonPolynomialHeight alpha y) S)
          0 x +
        dynamicOutsideClusterHighAnnulusMass
          (carlsonPolynomialHeight alpha)
          (carlsonPolynomialHeight gamma) S
          (fun y =>
            pntHybridCanonicalTwoStripOutsideClusterBucketInput
              sigma (carlsonPolynomialHeight alpha y) S)
          0 x := by
  unfold dynamicPositiveOutsideClusterPNTLayerNorm
  calc
    ‖∑ rho ∈
        (pntHybridCanonicalTwoStripOutsideClusterBucketInput
          sigma (H x) S).layer 0,
        pntRelativeZeroContribution x rho‖ ≤
      ∑ rho ∈
        (pntHybridCanonicalTwoStripOutsideClusterBucketInput
          sigma (H x) S).layer 0,
        ‖pntRelativeZeroContribution x rho‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈
        (pntHybridCanonicalTwoStripOutsideClusterBucketInput
          sigma (carlsonPolynomialHeight alpha x) S).layer 0,
        ‖pntRelativeZeroContribution x rho‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (canonicalSelectedLayer_subset_polynomialLayer 0 hHle)
        (fun _ _ _ => norm_nonneg _)
    _ = _ :=
      dynamicOutsideClusterLayerMass_eq_low_add_high
        (carlsonPolynomialHeight alpha)
        (carlsonPolynomialHeight gamma) S
        (fun y =>
          pntHybridCanonicalTwoStripOutsideClusterBucketInput
            sigma (carlsonPolynomialHeight alpha y) S)
        0 x

/-- The selected canonical high layer lies in the polynomial-envelope actual
Carlson strip under the selected outside-cluster right cap. -/
theorem canonicalSelectedHighLayer_subset_polynomialCarlsonStrip
    {H : ℝ → ℝ} {alpha sigma tau x : ℝ} {S : Finset ℂ}
    (hHle : H x ≤ carlsonPolynomialHeight alpha x)
    (hcap :
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S,
        sigma < rho.re → rho.re ≤ tau) :
    (pntHybridCanonicalTwoStripOutsideClusterBucketInput
        sigma (H x) S).layer 1 ⊆
      actualPositiveCarlsonStrip sigma tau
        (carlsonPolynomialHeight alpha x) := by
  intro rho hrho
  have hlayer := Finset.mem_filter.mp hrho
  have hselected :
      rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S :=
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

/-- Complete selected positive tail bounded by the unchanged polynomial
two-height low mass plus actual Carlson strip mass. -/
theorem dynamicSelectedPositiveOutsideClusterPNTTailNorm_le
    {H : ℝ → ℝ} {alpha gamma sigma tau x : ℝ} {S : Finset ℂ}
    (hHle : H x ≤ carlsonPolynomialHeight alpha x)
    (hcap :
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S,
        sigma < rho.re → rho.re ≤ tau) :
    dynamicPositiveOutsideClusterPNTTailNorm H S x ≤
      (dynamicOutsideClusterLowOrdinateMass
          (carlsonPolynomialHeight alpha)
          (carlsonPolynomialHeight gamma) S
          (fun y =>
            pntHybridCanonicalTwoStripOutsideClusterBucketInput
              sigma (carlsonPolynomialHeight alpha y) S)
          0 x +
        dynamicOutsideClusterHighAnnulusMass
          (carlsonPolynomialHeight alpha)
          (carlsonPolynomialHeight gamma) S
          (fun y =>
            pntHybridCanonicalTwoStripOutsideClusterBucketInput
              sigma (carlsonPolynomialHeight alpha y) S)
          0 x) +
      ∑ rho ∈ actualPositiveCarlsonStrip sigma tau
          (carlsonPolynomialHeight alpha x),
        ‖pntRelativeZeroContribution x rho‖ := by
  let selectedInput := fun y =>
    pntHybridCanonicalTwoStripOutsideClusterBucketInput
      sigma (H y) S
  calc
    dynamicPositiveOutsideClusterPNTTailNorm H S x ≤
      ∑ i,
        dynamicPositiveOutsideClusterPNTLayerNorm
          H S selectedInput i x :=
      dynamicPositiveOutsideClusterPNTTailNorm_le_sum_layerNorms
        selectedInput x
    _ =
      dynamicPositiveOutsideClusterPNTLayerNorm
          H S selectedInput 0 x +
        dynamicPositiveOutsideClusterPNTLayerNorm
          H S selectedInput 1 x := by
      rw [Fin.sum_univ_two]
    _ ≤ _ := add_le_add
      (canonicalSelectedLowLayerNorm_le_polynomialTwoHeightMass hHle)
      (by
        unfold dynamicPositiveOutsideClusterPNTLayerNorm
        calc
          ‖∑ rho ∈
              (pntHybridCanonicalTwoStripOutsideClusterBucketInput
                sigma (H x) S).layer 1,
              pntRelativeZeroContribution x rho‖ ≤
            ∑ rho ∈
              (pntHybridCanonicalTwoStripOutsideClusterBucketInput
                sigma (H x) S).layer 1,
              ‖pntRelativeZeroContribution x rho‖ :=
            norm_sum_le _ _
          _ ≤ _ :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (canonicalSelectedHighLayer_subset_polynomialCarlsonStrip
                hHle hcap)
              (fun _ _ _ => norm_nonneg _))

/-- Selected positive-tail target-amplitude decay. -/
theorem selectedPositiveOutsideClusterTail_targetAmplitudeNegligible
    {H : ℝ → ℝ} {S : Finset ℂ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
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
        rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S →
        sigma < rho.re → rho.re ≤ tau) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicPositiveOutsideClusterPNTTailNorm H S) := by
  let polynomialInput := fun y =>
    pntHybridCanonicalTwoStripOutsideClusterBucketInput
      sigma (carlsonPolynomialHeight alpha y) S
  rcases
      exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
        (carlsonPolynomialHeight alpha) sigma S with
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
      dynamicSelectedPositiveOutsideClusterPNTTailNorm_le
        (gamma := gammaLow) hHx (hcap x)
    have hdiv := (div_le_div_iff_of_pos_right hamp).2 hp
    simpa [dynamicPositiveOutsideClusterPNTTailNorm,
      actualPositiveCarlsonStripTargetAmplitudeMass, add_div] using hdiv

/-- Complete selected-height full outside-cluster tail decay. -/
theorem selectedFullOutsideClusterTail_targetAmplitudeNegligible
    {H : ℝ → ℝ} {S : Finset ℂ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
    (hS : IsConjugationInvariantCluster S)
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
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
        H x ≤ carlsonPolynomialHeight alpha x)
    (hcap :
      ∀ x rho,
        rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S →
        sigma < rho.re → rho.re ≤ tau)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicFullOutsideClusterPNTZeroTailNorm H S) := by
  have hpositive :=
    selectedPositiveOutsideClusterTail_targetAmplitudeNegligible
      hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh hHle hcap
  have hrealNegligible :=
    dynamicRealOrdinateOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
      H S beta hHnonneg hreal
  have hamplitude :
      ∀ᶠ x : ℝ in atTop, 0 < targetZeroPowerAmplitude beta x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simpa [targetZeroPowerAmplitude] using
      (Real.rpow_pos_of_pos hx (beta - 1))
  exact
    dynamicFullOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
      hS hamplitude
      hpositive hrealNegligible

end PrimeNumberTheorem
