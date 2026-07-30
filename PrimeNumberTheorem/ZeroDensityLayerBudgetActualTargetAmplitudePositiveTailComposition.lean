import PrimeNumberTheorem.ZeroDensityLayerBudgetActualTargetAmplitudeLowLayerTwoHeight
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualTargetAmplitudeTwoHeightStrip
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonCanonicalTwoStripAutomaticNorm
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualPositiveZeroOrderedCoverTransfer

/-!
# Target-amplitude composition of the actual positive outside-cluster tail

The canonical low layer is discharged by the global-count two-height split,
and the canonical high layer is embedded in an actual Carlson strip.  This
produces one estimate for the complete positive-ordinate outside-cluster
zero tail.
-/

open Complex Filter
open scoped BigOperators Topology

namespace PrimeNumberTheorem

/-- Positive-ordinate outside-cluster zero tail divided by the target-zero
power amplitude. -/
noncomputable def actualPositiveOutsideClusterTailTargetAmplitudeNorm
    (beta alpha : ℝ) (S : Finset ℂ) (x : ℝ) : ℝ :=
  dynamicPositiveOutsideClusterPNTTailNorm
      (carlsonPolynomialHeight alpha) S x /
    targetZeroPowerAmplitude beta x

/-- Under an explicit right cap, canonical layer `1` is contained in the
actual Carlson strip with the same endpoints and height. -/
theorem canonicalOutsideClusterHighLayer_subset_actualPositiveCarlsonStrip
    {sigma tau T : ℝ} {S : Finset ℂ}
    (hcap :
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
        sigma < rho.re → rho.re ≤ tau) :
    (pntHybridCanonicalTwoStripOutsideClusterBucketInput
        sigma T S).layer 1 ⊆
      actualPositiveCarlsonStrip sigma tau T := by
  intro rho hrho
  have hlayer := Finset.mem_filter.mp hrho
  have houtside :
      rho ∈ positiveNontrivialZerosOutsideClusterFinset T S :=
    hlayer.1
  have hmem :=
    mem_positiveNontrivialZerosOutsideClusterFinset.mp houtside
  have hright : sigma < rho.re := by
    have hbucket := hlayer.2
    by_contra hnot
    simp [pntHybridCanonicalTwoStripOutsideClusterBucketInput,
      hnot] at hbucket
  exact mem_actualPositiveCarlsonStrip.mpr
    ⟨hmem.1, hmem.2.1, hmem.2.2.1, hright,
      hcap rho houtside hright⟩

/-- Canonical high-layer norm is bounded by the multiplicity-weighted actual
Carlson strip mass. -/
theorem canonicalOutsideClusterHighLayerNorm_le_actualCarlsonStripMass
    {alpha sigma tau x : ℝ} {S : Finset ℂ}
    (hcap :
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset
          (carlsonPolynomialHeight alpha x) S,
        sigma < rho.re → rho.re ≤ tau) :
    dynamicPositiveOutsideClusterPNTLayerNorm
        (carlsonPolynomialHeight alpha) S
        (fun y =>
          pntHybridCanonicalTwoStripOutsideClusterBucketInput
            sigma (carlsonPolynomialHeight alpha y) S)
        1 x ≤
      ∑ rho ∈ actualPositiveCarlsonStrip sigma tau
          (carlsonPolynomialHeight alpha x),
        ‖pntRelativeZeroContribution x rho‖ := by
  unfold dynamicPositiveOutsideClusterPNTLayerNorm
  calc
    ‖∑ rho ∈
        (pntHybridCanonicalTwoStripOutsideClusterBucketInput
          sigma (carlsonPolynomialHeight alpha x) S).layer 1,
        pntRelativeZeroContribution x rho‖ ≤
      ∑ rho ∈
        (pntHybridCanonicalTwoStripOutsideClusterBucketInput
          sigma (carlsonPolynomialHeight alpha x) S).layer 1,
        ‖pntRelativeZeroContribution x rho‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈ actualPositiveCarlsonStrip sigma tau
          (carlsonPolynomialHeight alpha x),
        ‖pntRelativeZeroContribution x rho‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (canonicalOutsideClusterHighLayer_subset_actualPositiveCarlsonStrip
          hcap)
        (fun _ _ _ => norm_nonneg _)

/-- Canonical low-layer norm is bounded by the exact stack37 ordinate
partition mass. -/
theorem canonicalOutsideClusterLowLayerNorm_le_twoHeightMass
    {alpha gamma sigma x : ℝ} {S : Finset ℂ} :
    dynamicPositiveOutsideClusterPNTLayerNorm
        (carlsonPolynomialHeight alpha) S
        (fun y =>
          pntHybridCanonicalTwoStripOutsideClusterBucketInput
            sigma (carlsonPolynomialHeight alpha y) S)
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
          sigma (carlsonPolynomialHeight alpha x) S).layer 0,
        pntRelativeZeroContribution x rho‖ ≤
      ∑ rho ∈
        (pntHybridCanonicalTwoStripOutsideClusterBucketInput
          sigma (carlsonPolynomialHeight alpha x) S).layer 0,
        ‖pntRelativeZeroContribution x rho‖ :=
      norm_sum_le _ _
    _ = _ :=
      dynamicOutsideClusterLayerMass_eq_low_add_high
        (carlsonPolynomialHeight alpha)
        (carlsonPolynomialHeight gamma) S
        (fun y =>
          pntHybridCanonicalTwoStripOutsideClusterBucketInput
            sigma (carlsonPolynomialHeight alpha y) S)
        0 x

/-- Pointwise composition of the full positive outside-cluster tail from the
low-layer two-height mass and the actual high Carlson strip. -/
theorem dynamicPositiveOutsideClusterPNTTailNorm_le_lowTwoHeight_add_strip
    {alpha gamma sigma tau x : ℝ} {S : Finset ℂ}
    (hcap :
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset
          (carlsonPolynomialHeight alpha x) S,
        sigma < rho.re → rho.re ≤ tau) :
    dynamicPositiveOutsideClusterPNTTailNorm
        (carlsonPolynomialHeight alpha) S x ≤
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
  let input := fun y =>
    pntHybridCanonicalTwoStripOutsideClusterBucketInput
      sigma (carlsonPolynomialHeight alpha y) S
  calc
    dynamicPositiveOutsideClusterPNTTailNorm
        (carlsonPolynomialHeight alpha) S x ≤
      ∑ i,
        dynamicPositiveOutsideClusterPNTLayerNorm
          (carlsonPolynomialHeight alpha) S input i x :=
      dynamicPositiveOutsideClusterPNTTailNorm_le_sum_layerNorms input x
    _ =
      dynamicPositiveOutsideClusterPNTLayerNorm
          (carlsonPolynomialHeight alpha) S input 0 x +
        dynamicPositiveOutsideClusterPNTLayerNorm
          (carlsonPolynomialHeight alpha) S input 1 x := by
      rw [Fin.sum_univ_two]
    _ ≤
      (dynamicOutsideClusterLowOrdinateMass
          (carlsonPolynomialHeight alpha)
          (carlsonPolynomialHeight gamma) S input 0 x +
        dynamicOutsideClusterHighAnnulusMass
          (carlsonPolynomialHeight alpha)
          (carlsonPolynomialHeight gamma) S input 0 x) +
      ∑ rho ∈ actualPositiveCarlsonStrip sigma tau
          (carlsonPolynomialHeight alpha x),
        ‖pntRelativeZeroContribution x rho‖ :=
      add_le_add canonicalOutsideClusterLowLayerNorm_le_twoHeightMass
        (canonicalOutsideClusterHighLayerNorm_le_actualCarlsonStripMass
          hcap)

/-- The complete actual positive outside-cluster tail is negligible on the
target-zero scale when the low global layer and high Carlson strip satisfy
their respective two-height margins. -/
theorem tendsto_actualPositiveOutsideClusterTailTargetAmplitudeNorm
    {S : Finset ℂ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow :
      gammaLow + sigma - beta + epsilonLow < 0)
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
    (hcap :
      ∀ x rho,
        rho ∈ positiveNontrivialZerosOutsideClusterFinset
          (carlsonPolynomialHeight alpha x) S →
        sigma < rho.re → rho.re ≤ tau) :
    Tendsto
      (actualPositiveOutsideClusterTailTargetAmplitudeNorm
        beta alpha S)
      atTop (nhds 0) := by
  let input := fun y =>
    pntHybridCanonicalTwoStripOutsideClusterBucketInput
      sigma (carlsonPolynomialHeight alpha y) S
  rcases
      exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
        (carlsonPolynomialHeight alpha) sigma S with
    ⟨kappa, hkappa, hnorm⟩
  have hlow :
      Tendsto
        (fun x =>
          (dynamicOutsideClusterLowOrdinateMass
              (carlsonPolynomialHeight alpha)
              (carlsonPolynomialHeight gammaLow) S input 0 x +
            dynamicOutsideClusterHighAnnulusMass
              (carlsonPolynomialHeight alpha)
              (carlsonPolynomialHeight gammaLow) S input 0 x) /
            targetZeroPowerAmplitude beta x)
        atTop (nhds 0) := by
    apply tendsto_dynamicOutsideClusterTwoHeightMass_div_target
      input 0 hkappa hnorm
    · intro x rho hrho
      exact
        pntHybridCanonicalTwoStripOutsideCluster_lowLayer_re_le hrho
    · exact halpha
    · exact hgammaLow
    · exact hepsilonLow
    · exact hlowLow
    · exact hlowHigh
  have hstrip :=
    tendsto_actualPositiveCarlsonStripTargetAmplitudeMass_twoHeight
      hsigma hsigmaOne halpha hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh
  have hmajor :
      Tendsto
        (fun x =>
          (dynamicOutsideClusterLowOrdinateMass
              (carlsonPolynomialHeight alpha)
              (carlsonPolynomialHeight gammaLow) S input 0 x +
            dynamicOutsideClusterHighAnnulusMass
              (carlsonPolynomialHeight alpha)
              (carlsonPolynomialHeight gammaLow) S input 0 x) /
              targetZeroPowerAmplitude beta x +
            actualPositiveCarlsonStripTargetAmplitudeMass
              beta sigma tau alpha x)
        atTop (nhds 0) := by
    simpa using hlow.add hstrip
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (zero_le_one.trans hx) _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hamp : 0 < targetZeroPowerAmplitude beta x :=
      Real.rpow_pos_of_pos hx0 _
    have hp :=
      dynamicPositiveOutsideClusterPNTTailNorm_le_lowTwoHeight_add_strip
        (gamma := gammaLow) (hcap x)
    unfold actualPositiveOutsideClusterTailTargetAmplitudeNorm
    have hdiv := (div_le_div_iff_of_pos_right hamp).2 hp
    simpa [actualPositiveCarlsonStripTargetAmplitudeMass, add_div] using hdiv

end PrimeNumberTheorem
