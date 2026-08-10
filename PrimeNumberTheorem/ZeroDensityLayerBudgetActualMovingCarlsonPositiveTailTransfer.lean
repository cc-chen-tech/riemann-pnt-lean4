import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingCarlsonFullyAutomaticDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualPositiveZeroOrderedCoverTransfer

/-!
# Actual positive-zero transfer through a moving Carlson strip

This module separates the positive-ordinate explicit-formula zero sum into:

* the canonical critical-half layer;
* the middle strip `1 / 2 < re rho <= 1 - 2 * delta m`;
* the moving Carlson strip `1 - 2 * delta m < re rho <= 1 - delta m`.

The fully automatic Carlson theorem closes the last strip.  Consequently the
only remaining density input in the final transfer is decay of the explicitly
defined middle-strip mass.
-/

namespace PrimeNumberTheorem

open Filter
open scoped BigOperators Topology

noncomputable section

/-- The part of the positive zero sum between the critical line and the
fully automatic moving Carlson strip. -/
def actualMovingCarlsonMiddleMass
    (alpha : ℝ) (delta : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ rho ∈ actualPositiveCarlsonStrip
      (1 / 2) (1 - 2 * delta m)
      (carlsonPolynomialHeight alpha (m : ℝ)),
    ‖pntRelativeZeroContribution (m : ℝ) rho‖

/-- At the selected finite height, every positive nontrivial zero lies on or
to the left of the moving right edge `1 - delta m`. -/
def ActualMovingPositiveRightEdgeCap
    (alpha : ℝ) (delta : ℕ → ℝ) (m : ℕ) : Prop :=
  ∀ rho ∈ positiveNontrivialZerosFinset
      (carlsonPolynomialHeight alpha (m : ℝ)),
    rho.re ≤ 1 - delta m

/-- The high layer in the critical-half split is covered by the middle strip
and the fully automatic moving Carlson strip. -/
theorem actualCriticalHalfCanonicalInput_high_subset_movingMiddle_union_strip
    {alpha : ℝ} {delta : ℕ → ℝ} {m : ℕ}
    (hcap : ActualMovingPositiveRightEdgeCap alpha delta m) :
    (actualCriticalHalfCanonicalInput alpha (m : ℝ)).layer 1 ⊆
      actualPositiveCarlsonStrip
          (1 / 2) (1 - 2 * delta m)
          (carlsonPolynomialHeight alpha (m : ℝ)) ∪
        actualPositiveCarlsonStrip
          (1 - 2 * delta m) (1 - delta m)
          (carlsonPolynomialHeight alpha (m : ℝ)) := by
  intro rho hrho
  have hlayer := Finset.mem_filter.mp hrho
  have hpositive :
      rho ∈ positiveNontrivialZerosFinset
        (carlsonPolynomialHeight alpha (m : ℝ)) := by
    simpa [positiveNontrivialZerosOutsideClusterFinset] using hlayer.1
  have hright : 1 / 2 < rho.re := by
    have hbucket := hlayer.2
    by_contra hnot
    have hle : rho.re ≤ 1 / 2 := le_of_not_gt hnot
    simp [actualCriticalHalfCanonicalInput,
      pntHybridCanonicalTwoStripOutsideClusterBucketInput] at hbucket
    exact hnot (by simpa [one_div] using hbucket)
  have hzero := mem_positiveNontrivialZerosFinset.mp hpositive
  by_cases hmiddle : rho.re ≤ 1 - 2 * delta m
  · apply Finset.mem_union.mpr
    left
    exact mem_actualPositiveCarlsonStrip.mpr
      ⟨hzero.1, hzero.2.1, hzero.2.2, hright, hmiddle⟩
  · apply Finset.mem_union.mpr
    right
    exact mem_actualPositiveCarlsonStrip.mpr
      ⟨hzero.1, hzero.2.1, hzero.2.2,
        lt_of_not_ge hmiddle, hcap rho hpositive⟩

/-- The middle strip and moving strip are disjoint at their shared endpoint. -/
theorem actualMovingCarlsonMiddle_disjoint_strip
    {alpha : ℝ} {delta : ℕ → ℝ} {m : ℕ} :
    Disjoint
      (actualPositiveCarlsonStrip
        (1 / 2) (1 - 2 * delta m)
        (carlsonPolynomialHeight alpha (m : ℝ)))
      (actualPositiveCarlsonStrip
        (1 - 2 * delta m) (1 - delta m)
        (carlsonPolynomialHeight alpha (m : ℝ))) := by
  refine Finset.disjoint_left.mpr ?_
  intro rho hmiddle hmoving
  rcases mem_actualPositiveCarlsonStrip.mp hmiddle with
    ⟨_, _, _, _, hmiddleUpper⟩
  rcases mem_actualPositiveCarlsonStrip.mp hmoving with
    ⟨_, _, _, hmovingLower, _⟩
  exact (not_lt_of_ge hmiddleUpper) hmovingLower

/-- The canonical high-layer norm is bounded by the middle mass plus the
fully automatic moving-strip mass. -/
theorem actualCriticalHalfCanonicalInput_highLayerNorm_le_movingMasses
    {alpha : ℝ} {delta : ℕ → ℝ} {m : ℕ}
    (hcap : ActualMovingPositiveRightEdgeCap alpha delta m) :
    dynamicPositiveOutsideClusterPNTLayerNorm
        (carlsonPolynomialHeight alpha) ∅
        (actualCriticalHalfCanonicalInput alpha) 1 (m : ℝ) ≤
      actualMovingCarlsonMiddleMass alpha delta m +
        actualMovingCarlsonStripMass alpha delta m := by
  unfold dynamicPositiveOutsideClusterPNTLayerNorm
  calc
    ‖∑ rho ∈ (actualCriticalHalfCanonicalInput alpha (m : ℝ)).layer 1,
        pntRelativeZeroContribution (m : ℝ) rho‖
        ≤ ∑ rho ∈
            (actualCriticalHalfCanonicalInput alpha (m : ℝ)).layer 1,
            ‖pntRelativeZeroContribution (m : ℝ) rho‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈
          actualPositiveCarlsonStrip
              (1 / 2) (1 - 2 * delta m)
              (carlsonPolynomialHeight alpha (m : ℝ)) ∪
            actualPositiveCarlsonStrip
              (1 - 2 * delta m) (1 - delta m)
              (carlsonPolynomialHeight alpha (m : ℝ)),
          ‖pntRelativeZeroContribution (m : ℝ) rho‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (actualCriticalHalfCanonicalInput_high_subset_movingMiddle_union_strip
          hcap)
        (fun rho _ _ => norm_nonneg _)
    _ = actualMovingCarlsonMiddleMass alpha delta m +
          actualMovingCarlsonStripMass alpha delta m := by
      rw [Finset.sum_union actualMovingCarlsonMiddle_disjoint_strip]
      rfl

/-- Pointwise assembly of the complete positive zero tail into the critical
half, middle strip, and fully automatic moving strip. -/
theorem dynamicPositivePNTTailNorm_le_criticalHalf_add_movingMasses
    {alpha : ℝ} {delta : ℕ → ℝ} {m : ℕ}
    (hcap : ActualMovingPositiveRightEdgeCap alpha delta m) :
    dynamicPositivePNTTailNorm
        (carlsonPolynomialHeight alpha) (m : ℝ) ≤
      (dynamicPositiveOutsideClusterPNTLayerNorm
          (carlsonPolynomialHeight alpha) ∅
          (actualCriticalHalfCanonicalInput alpha) 0 (m : ℝ) +
        actualMovingCarlsonMiddleMass alpha delta m) +
      actualMovingCarlsonStripMass alpha delta m := by
  calc
    dynamicPositivePNTTailNorm
        (carlsonPolynomialHeight alpha) (m : ℝ) =
        dynamicPositiveOutsideClusterPNTTailNorm
          (carlsonPolynomialHeight alpha) ∅ (m : ℝ) := by
      simp [dynamicPositivePNTTailNorm,
        dynamicPositiveOutsideClusterPNTTailNorm,
        positiveNontrivialZerosOutsideClusterFinset]
    _ ≤ ∑ i,
        dynamicPositiveOutsideClusterPNTLayerNorm
          (carlsonPolynomialHeight alpha) ∅
          (actualCriticalHalfCanonicalInput alpha) i (m : ℝ) :=
      dynamicPositiveOutsideClusterPNTTailNorm_le_sum_layerNorms
        (actualCriticalHalfCanonicalInput alpha) (m : ℝ)
    _ =
        dynamicPositiveOutsideClusterPNTLayerNorm
            (carlsonPolynomialHeight alpha) ∅
            (actualCriticalHalfCanonicalInput alpha) 0 (m : ℝ) +
          dynamicPositiveOutsideClusterPNTLayerNorm
            (carlsonPolynomialHeight alpha) ∅
            (actualCriticalHalfCanonicalInput alpha) 1 (m : ℝ) := by
      rw [Fin.sum_univ_two]
    _ ≤
        dynamicPositiveOutsideClusterPNTLayerNorm
            (carlsonPolynomialHeight alpha) ∅
            (actualCriticalHalfCanonicalInput alpha) 0 (m : ℝ) +
          (actualMovingCarlsonMiddleMass alpha delta m +
            actualMovingCarlsonStripMass alpha delta m) :=
      add_le_add_right
        (actualCriticalHalfCanonicalInput_highLayerNorm_le_movingMasses hcap) _
    _ =
        (dynamicPositiveOutsideClusterPNTLayerNorm
            (carlsonPolynomialHeight alpha) ∅
            (actualCriticalHalfCanonicalInput alpha) 0 (m : ℝ) +
          actualMovingCarlsonMiddleMass alpha delta m) +
        actualMovingCarlsonStripMass alpha delta m := by
      ring

/-- Full positive-zero decay.  The moving Carlson strip is discharged
automatically; decay of the explicit middle strip is the sole remaining
density input. -/
theorem tendsto_dynamicPositivePNTTailNorm_of_actualMovingCarlson
    {alpha epsilonLow : ℝ} {delta : ℕ → ℝ}
    (halpha : 0 < alpha)
    (hepsilonLow : 0 < epsilonLow)
    (hlowMargin : alpha + epsilonLow < 1 / 2)
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8 ∧
        128 * alpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta)
    (hcap : ∀ᶠ m : ℕ in atTop,
      ActualMovingPositiveRightEdgeCap alpha delta m)
    (hmiddle :
      Tendsto (actualMovingCarlsonMiddleMass alpha delta)
        atTop (nhds 0)) :
    Tendsto
      (fun m : ℕ =>
        dynamicPositivePNTTailNorm
          (carlsonPolynomialHeight alpha) (m : ℝ))
      atTop (nhds 0) := by
  have hcriticalReal :=
    tendsto_actualCriticalHalfCanonicalPNTLayerNorm
      halpha hepsilonLow hlowMargin
  have hcritical :
      Tendsto
        (fun m : ℕ =>
          dynamicPositiveOutsideClusterPNTLayerNorm
            (carlsonPolynomialHeight alpha) ∅
            (actualCriticalHalfCanonicalInput alpha) 0 (m : ℝ))
        atTop (nhds 0) :=
    hcriticalReal.comp tendsto_natCast_atTop_atTop
  have hmoving :=
    tendsto_actualMovingCarlsonStripMass_zero_fullyAutomatic
      halpha hdelta hgap
  have hmajorant :
      Tendsto
        (fun m : ℕ =>
          (dynamicPositiveOutsideClusterPNTLayerNorm
              (carlsonPolynomialHeight alpha) ∅
              (actualCriticalHalfCanonicalInput alpha) 0 (m : ℝ) +
            actualMovingCarlsonMiddleMass alpha delta m) +
          actualMovingCarlsonStripMass alpha delta m)
        atTop (nhds 0) := by
    simpa using (hcritical.add hmiddle).add hmoving
  refine squeeze_zero' ?_ ?_ hmajorant
  · filter_upwards with m
    exact norm_nonneg _
  · filter_upwards [hcap] with m hm
    exact dynamicPositivePNTTailNorm_le_criticalHalf_add_movingMasses hm

end

end PrimeNumberTheorem
