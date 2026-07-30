import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCriticalHalfDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualOrderedBalancedStrips
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridActualFiniteStrips

/-!
# Actual positive-zero transfer through a critical half and ordered Carlson cover

This module joins two estimates on the same explicit-formula kernel:

* the globally counted layer `re rho <= 1 / 2`;
* a finite ordered family of balanced Carlson strips covering `re rho > 1 / 2`.

The right-half coverage is an explicit hypothesis.  In particular, the theorem
does not silently replace the missing zero-free-region input by a fixed finite
strip family.
-/

namespace PrimeNumberTheorem

open Filter
open scoped BigOperators Topology

noncomputable section

/-- A finite family of actual Carlson strips covers every positive
nontrivial zero to the right of the critical line at height `T`. -/
def ActualPositiveCarlsonRightCover {n : ℕ}
    (sigma tau : Fin n → ℝ) (T : ℝ) : Prop :=
  ∀ rho ∈ positiveNontrivialZerosFinset T,
    1 / 2 < rho.re →
      rho ∈ actualPositiveCarlsonFiniteStripUnion sigma tau T

/-- Pointwise endpoint coverage implies membership in the finite Carlson
strip union. -/
theorem actualPositiveCarlsonRightCover_of_endpoints {n : ℕ}
    {sigma tau : Fin n → ℝ} {T : ℝ}
    (hcover :
      ∀ rho ∈ positiveNontrivialZerosFinset T,
        1 / 2 < rho.re →
          ∃ i, sigma i < rho.re ∧ rho.re ≤ tau i) :
    ActualPositiveCarlsonRightCover sigma tau T := by
  intro rho hrho hright
  obtain ⟨i, hsigma, htau⟩ := hcover rho hrho hright
  rw [actualPositiveCarlsonFiniteStripUnion]
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ i, ?_⟩
  have hzero := mem_positiveNontrivialZerosFinset.mp hrho
  exact mem_actualPositiveCarlsonStrip.mpr
    ⟨hzero.1, hzero.2.1, hzero.2.2, hsigma, htau⟩

/-- The high layer of the canonical critical-half split lies in any certified
right Carlson cover. -/
theorem actualCriticalHalfCanonicalInput_high_subset_stripUnion
    {n : ℕ} {sigma tau : Fin n → ℝ} {alpha x : ℝ}
    (hcover :
      ActualPositiveCarlsonRightCover sigma tau
        (carlsonPolynomialHeight alpha x)) :
    (actualCriticalHalfCanonicalInput alpha x).layer 1 ⊆
      actualPositiveCarlsonFiniteStripUnion sigma tau
        (carlsonPolynomialHeight alpha x) := by
  intro rho hrho
  have hlayer := Finset.mem_filter.mp hrho
  have hpositive :
      rho ∈ positiveNontrivialZerosFinset
        (carlsonPolynomialHeight alpha x) := by
    simpa [positiveNontrivialZerosOutsideClusterFinset] using hlayer.1
  have hright : 1 / 2 < rho.re := by
    have hbucket := hlayer.2
    by_contra hnot
    have hle : rho.re ≤ 1 / 2 := le_of_not_gt hnot
    simp [actualCriticalHalfCanonicalInput,
      pntHybridCanonicalTwoStripOutsideClusterBucketInput] at hbucket
    exact hnot (by simpa [one_div] using hbucket)
  exact hcover rho hpositive hright

/-- The canonical high-layer kernel norm is bounded by the mass of a certified
finite Carlson cover. -/
theorem actualCriticalHalfCanonicalInput_highLayerNorm_le_stripUnion
    {n : ℕ} {sigma tau : Fin n → ℝ} {alpha x : ℝ}
    (hcover :
      ActualPositiveCarlsonRightCover sigma tau
        (carlsonPolynomialHeight alpha x)) :
    dynamicPositiveOutsideClusterPNTLayerNorm
        (carlsonPolynomialHeight alpha) ∅
        (actualCriticalHalfCanonicalInput alpha) 1 x ≤
      ∑ rho ∈ actualPositiveCarlsonFiniteStripUnion sigma tau
          (carlsonPolynomialHeight alpha x),
        ‖pntRelativeZeroContribution x rho‖ := by
  unfold dynamicPositiveOutsideClusterPNTLayerNorm
  calc
    ‖∑ rho ∈ (actualCriticalHalfCanonicalInput alpha x).layer 1,
        pntRelativeZeroContribution x rho‖
        ≤ ∑ rho ∈ (actualCriticalHalfCanonicalInput alpha x).layer 1,
            ‖pntRelativeZeroContribution x rho‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈ actualPositiveCarlsonFiniteStripUnion sigma tau
          (carlsonPolynomialHeight alpha x),
        ‖pntRelativeZeroContribution x rho‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (actualCriticalHalfCanonicalInput_high_subset_stripUnion hcover)
        (fun rho _ _ => norm_nonneg _)

/-- Pointwise assembly: the full positive-zero kernel norm is bounded by the
critical-half layer plus the certified right-strip mass. -/
theorem dynamicPositivePNTTailNorm_le_criticalHalf_add_orderedStripUnion
    {n : ℕ} {sigma tau : Fin n → ℝ} {alpha x : ℝ}
    (hcover :
      ActualPositiveCarlsonRightCover sigma tau
        (carlsonPolynomialHeight alpha x)) :
    dynamicPositivePNTTailNorm (carlsonPolynomialHeight alpha) x ≤
      dynamicPositiveOutsideClusterPNTLayerNorm
          (carlsonPolynomialHeight alpha) ∅
          (actualCriticalHalfCanonicalInput alpha) 0 x +
        ∑ rho ∈ actualPositiveCarlsonFiniteStripUnion sigma tau
            (carlsonPolynomialHeight alpha x),
          ‖pntRelativeZeroContribution x rho‖ := by
  calc
    dynamicPositivePNTTailNorm (carlsonPolynomialHeight alpha) x =
        dynamicPositiveOutsideClusterPNTTailNorm
          (carlsonPolynomialHeight alpha) ∅ x := by
      simp [dynamicPositivePNTTailNorm,
        dynamicPositiveOutsideClusterPNTTailNorm,
        positiveNontrivialZerosOutsideClusterFinset]
    _ ≤ ∑ i,
        dynamicPositiveOutsideClusterPNTLayerNorm
          (carlsonPolynomialHeight alpha) ∅
          (actualCriticalHalfCanonicalInput alpha) i x :=
      dynamicPositiveOutsideClusterPNTTailNorm_le_sum_layerNorms
        (actualCriticalHalfCanonicalInput alpha) x
    _ =
        dynamicPositiveOutsideClusterPNTLayerNorm
            (carlsonPolynomialHeight alpha) ∅
            (actualCriticalHalfCanonicalInput alpha) 0 x +
          dynamicPositiveOutsideClusterPNTLayerNorm
            (carlsonPolynomialHeight alpha) ∅
            (actualCriticalHalfCanonicalInput alpha) 1 x := by
      rw [Fin.sum_univ_two]
    _ ≤
        dynamicPositiveOutsideClusterPNTLayerNorm
            (carlsonPolynomialHeight alpha) ∅
            (actualCriticalHalfCanonicalInput alpha) 0 x +
          ∑ rho ∈ actualPositiveCarlsonFiniteStripUnion sigma tau
              (carlsonPolynomialHeight alpha x),
            ‖pntRelativeZeroContribution x rho‖ :=
      add_le_add_right
        (actualCriticalHalfCanonicalInput_highLayerNorm_le_stripUnion hcover) _

/-- Full positive-zero decay from a critical-half budget and a finite ordered
balanced Carlson cover of the right half. -/
theorem tendsto_dynamicPositivePNTTailNorm_of_orderedCarlsonRightCover
    {n : ℕ} {sigma tau : Fin n → ℝ}
    {alpha epsilonLow epsilonRight : ℝ}
    (hhalf : ∀ i, 1 / 2 < sigma i)
    (hone : ∀ i, sigma i < 1)
    (halpha : 0 < alpha)
    (hepsilonLow : 0 < epsilonLow)
    (hlowMargin : alpha + epsilonLow < 1 / 2)
    (hepsilonRight : 0 < epsilonRight)
    (htau :
      ∀ i,
        tau i + epsilonRight <
          carlsonTwoHeightBalancedTauCeiling (sigma i) alpha)
    (hsep :
      ∀ i j, i ≠ j →
        tau i ≤ sigma j ∨ tau j ≤ sigma i)
    (hcover :
      ∀ x,
        ActualPositiveCarlsonRightCover sigma tau
          (carlsonPolynomialHeight alpha x)) :
    Tendsto
      (dynamicPositivePNTTailNorm (carlsonPolynomialHeight alpha))
      atTop (nhds 0) := by
  have hcritical :=
    tendsto_actualCriticalHalfCanonicalPNTLayerNorm
      halpha hepsilonLow hlowMargin
  have hright :=
    tendsto_actualPositiveCarlsonOrderedStripUnion_mass
      hhalf hone halpha hepsilonRight htau hsep
  have hmajorant :
      Tendsto
        (fun x =>
          dynamicPositiveOutsideClusterPNTLayerNorm
              (carlsonPolynomialHeight alpha) ∅
              (actualCriticalHalfCanonicalInput alpha) 0 x +
            ∑ rho ∈ actualPositiveCarlsonFiniteStripUnion sigma tau
                (carlsonPolynomialHeight alpha x),
              ‖pntRelativeZeroContribution x rho‖)
        atTop (nhds 0) := by
    simpa using hcritical.add hright
  refine squeeze_zero' ?_ ?_ hmajorant
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _
  · exact Filter.Eventually.of_forall fun x =>
      dynamicPositivePNTTailNorm_le_criticalHalf_add_orderedStripUnion
        (hcover x)

/-- The same transfer only needs the right Carlson cover eventually.  This is
the form intended for later zero-free-region input. -/
theorem tendsto_dynamicPositivePNTTailNorm_of_eventually_orderedCarlsonRightCover
    {n : ℕ} {sigma tau : Fin n → ℝ}
    {alpha epsilonLow epsilonRight : ℝ}
    (hhalf : ∀ i, 1 / 2 < sigma i)
    (hone : ∀ i, sigma i < 1)
    (halpha : 0 < alpha)
    (hepsilonLow : 0 < epsilonLow)
    (hlowMargin : alpha + epsilonLow < 1 / 2)
    (hepsilonRight : 0 < epsilonRight)
    (htau :
      ∀ i,
        tau i + epsilonRight <
          carlsonTwoHeightBalancedTauCeiling (sigma i) alpha)
    (hsep :
      ∀ i j, i ≠ j →
        tau i ≤ sigma j ∨ tau j ≤ sigma i)
    (hcover :
      ∀ᶠ x in atTop,
        ActualPositiveCarlsonRightCover sigma tau
          (carlsonPolynomialHeight alpha x)) :
    Tendsto
      (dynamicPositivePNTTailNorm (carlsonPolynomialHeight alpha))
      atTop (nhds 0) := by
  have hcritical :=
    tendsto_actualCriticalHalfCanonicalPNTLayerNorm
      halpha hepsilonLow hlowMargin
  have hright :=
    tendsto_actualPositiveCarlsonOrderedStripUnion_mass
      hhalf hone halpha hepsilonRight htau hsep
  have hmajorant :
      Tendsto
        (fun x =>
          dynamicPositiveOutsideClusterPNTLayerNorm
              (carlsonPolynomialHeight alpha) ∅
              (actualCriticalHalfCanonicalInput alpha) 0 x +
            ∑ rho ∈ actualPositiveCarlsonFiniteStripUnion sigma tau
                (carlsonPolynomialHeight alpha x),
              ‖pntRelativeZeroContribution x rho‖)
        atTop (nhds 0) := by
    simpa using hcritical.add hright
  refine squeeze_zero' ?_ ?_ hmajorant
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _
  · filter_upwards [hcover] with x hx
    exact
      dynamicPositivePNTTailNorm_le_criticalHalf_add_orderedStripUnion hx

/-- Endpoint-form corollary of the ordered-cover transfer. -/
theorem tendsto_dynamicPositivePNTTailNorm_of_orderedCarlsonEndpoints
    {n : ℕ} {sigma tau : Fin n → ℝ}
    {alpha epsilonLow epsilonRight : ℝ}
    (hhalf : ∀ i, 1 / 2 < sigma i)
    (hone : ∀ i, sigma i < 1)
    (halpha : 0 < alpha)
    (hepsilonLow : 0 < epsilonLow)
    (hlowMargin : alpha + epsilonLow < 1 / 2)
    (hepsilonRight : 0 < epsilonRight)
    (htau :
      ∀ i,
        tau i + epsilonRight <
          carlsonTwoHeightBalancedTauCeiling (sigma i) alpha)
    (hsep :
      ∀ i j, i ≠ j →
        tau i ≤ sigma j ∨ tau j ≤ sigma i)
    (hcover :
      ∀ x rho,
        rho ∈ positiveNontrivialZerosFinset
            (carlsonPolynomialHeight alpha x) →
          1 / 2 < rho.re →
            ∃ i, sigma i < rho.re ∧ rho.re ≤ tau i) :
    Tendsto
      (dynamicPositivePNTTailNorm (carlsonPolynomialHeight alpha))
      atTop (nhds 0) := by
  apply tendsto_dynamicPositivePNTTailNorm_of_orderedCarlsonRightCover
    hhalf hone halpha hepsilonLow hlowMargin hepsilonRight htau hsep
  intro x
  exact actualPositiveCarlsonRightCover_of_endpoints
    (fun rho hrho hright => hcover x rho hrho hright)

/-- Eventual endpoint-form corollary, matching an asymptotic zero-free
coverage statement. -/
theorem tendsto_dynamicPositivePNTTailNorm_of_eventually_orderedCarlsonEndpoints
    {n : ℕ} {sigma tau : Fin n → ℝ}
    {alpha epsilonLow epsilonRight : ℝ}
    (hhalf : ∀ i, 1 / 2 < sigma i)
    (hone : ∀ i, sigma i < 1)
    (halpha : 0 < alpha)
    (hepsilonLow : 0 < epsilonLow)
    (hlowMargin : alpha + epsilonLow < 1 / 2)
    (hepsilonRight : 0 < epsilonRight)
    (htau :
      ∀ i,
        tau i + epsilonRight <
          carlsonTwoHeightBalancedTauCeiling (sigma i) alpha)
    (hsep :
      ∀ i j, i ≠ j →
        tau i ≤ sigma j ∨ tau j ≤ sigma i)
    (hcover :
      ∀ᶠ x in atTop,
        ∀ rho,
          rho ∈ positiveNontrivialZerosFinset
              (carlsonPolynomialHeight alpha x) →
            1 / 2 < rho.re →
              ∃ i, sigma i < rho.re ∧ rho.re ≤ tau i) :
    Tendsto
      (dynamicPositivePNTTailNorm (carlsonPolynomialHeight alpha))
      atTop (nhds 0) := by
  apply
    tendsto_dynamicPositivePNTTailNorm_of_eventually_orderedCarlsonRightCover
      hhalf hone halpha hepsilonLow hlowMargin hepsilonRight htau hsep
  filter_upwards [hcover] with x hx
  exact actualPositiveCarlsonRightCover_of_endpoints
    (fun rho hrho hright => hx rho hrho hright)

end

end PrimeNumberTheorem
