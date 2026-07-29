import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightCriticalHalfDecay

/-!
# Positive-zero transfer at a selected moving Carlson height

This is the selected-good-height analogue of the exact polynomial-height
moving Carlson transfer.  The critical half and the rightmost moving strip
are discharged automatically.  The middle strip and the moving right-edge
cap remain explicit.
-/

namespace PrimeNumberTheorem

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Selected-height mass in the middle strip between the critical line and
the fully automatic moving Carlson strip. -/
def actualSelectedHeightMovingCarlsonMiddleMass
    (H : ℝ → ℝ) (delta : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ rho ∈ actualPositiveCarlsonStrip
      (1 / 2) (1 - 2 * delta m) (H (m : ℝ)),
    ‖pntRelativeZeroContribution (m : ℝ) rho‖

/-- At the selected height, all positive nontrivial zeros lie on or to the
left of the moving right edge. -/
def ActualSelectedHeightMovingPositiveRightEdgeCap
    (H : ℝ → ℝ) (delta : ℕ → ℝ) (m : ℕ) : Prop :=
  ∀ rho ∈ positiveNontrivialZerosFinset (H (m : ℝ)),
    rho.re ≤ 1 - delta m

theorem
    actualSelectedHeightCriticalHalf_high_subset_movingMiddle_union_strip
    {H : ℝ → ℝ} {delta : ℕ → ℝ} {m : ℕ}
    (hcap : ActualSelectedHeightMovingPositiveRightEdgeCap H delta m) :
    (actualSelectedHeightCriticalHalfCanonicalInput H (m : ℝ)).layer 1 ⊆
      actualPositiveCarlsonStrip
          (1 / 2) (1 - 2 * delta m) (H (m : ℝ)) ∪
        actualPositiveCarlsonStrip
          (1 - 2 * delta m) (1 - delta m) (H (m : ℝ)) := by
  intro rho hrho
  have hlayer := Finset.mem_filter.mp hrho
  have hpositive :
      rho ∈ positiveNontrivialZerosFinset (H (m : ℝ)) := by
    simpa [positiveNontrivialZerosOutsideClusterFinset] using hlayer.1
  have hright : 1 / 2 < rho.re := by
    have hbucket := hlayer.2
    by_contra hnot
    have hle : rho.re ≤ 1 / 2 := le_of_not_gt hnot
    simp [actualSelectedHeightCriticalHalfCanonicalInput,
      pntHybridCanonicalTwoStripOutsideClusterBucketInput] at hbucket
    exact hnot (by simpa [one_div] using hbucket)
  have hzero := mem_positiveNontrivialZerosFinset.mp hpositive
  by_cases hmiddle : rho.re ≤ 1 - 2 * delta m
  · exact Finset.mem_union.mpr <| Or.inl <|
      mem_actualPositiveCarlsonStrip.mpr
        ⟨hzero.1, hzero.2.1, hzero.2.2, hright, hmiddle⟩
  · exact Finset.mem_union.mpr <| Or.inr <|
      mem_actualPositiveCarlsonStrip.mpr
        ⟨hzero.1, hzero.2.1, hzero.2.2,
          lt_of_not_ge hmiddle, hcap rho hpositive⟩

theorem actualSelectedHeightMovingCarlsonMiddle_disjoint_strip
    {H : ℝ → ℝ} {delta : ℕ → ℝ} {m : ℕ} :
    Disjoint
      (actualPositiveCarlsonStrip
        (1 / 2) (1 - 2 * delta m) (H (m : ℝ)))
      (actualPositiveCarlsonStrip
        (1 - 2 * delta m) (1 - delta m) (H (m : ℝ))) := by
  refine Finset.disjoint_left.mpr ?_
  intro rho hmiddle hmoving
  rcases mem_actualPositiveCarlsonStrip.mp hmiddle with
    ⟨_, _, _, _, hmiddleUpper⟩
  rcases mem_actualPositiveCarlsonStrip.mp hmoving with
    ⟨_, _, _, hmovingLower, _⟩
  exact (not_lt_of_ge hmiddleUpper) hmovingLower

theorem
    actualSelectedHeightCriticalHalf_highLayerNorm_le_movingMasses
    {H : ℝ → ℝ} {delta : ℕ → ℝ} {m : ℕ}
    (hcap : ActualSelectedHeightMovingPositiveRightEdgeCap H delta m) :
    dynamicPositiveOutsideClusterPNTLayerNorm H ∅
        (actualSelectedHeightCriticalHalfCanonicalInput H) 1 (m : ℝ) ≤
      actualSelectedHeightMovingCarlsonMiddleMass H delta m +
        actualSelectedHeightMovingCarlsonStripMass H delta m := by
  unfold dynamicPositiveOutsideClusterPNTLayerNorm
  calc
    ‖∑ rho ∈
        (actualSelectedHeightCriticalHalfCanonicalInput H (m : ℝ)).layer 1,
        pntRelativeZeroContribution (m : ℝ) rho‖
        ≤ ∑ rho ∈
            (actualSelectedHeightCriticalHalfCanonicalInput
              H (m : ℝ)).layer 1,
            ‖pntRelativeZeroContribution (m : ℝ) rho‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈
          actualPositiveCarlsonStrip
              (1 / 2) (1 - 2 * delta m) (H (m : ℝ)) ∪
            actualPositiveCarlsonStrip
              (1 - 2 * delta m) (1 - delta m) (H (m : ℝ)),
          ‖pntRelativeZeroContribution (m : ℝ) rho‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (actualSelectedHeightCriticalHalf_high_subset_movingMiddle_union_strip
          hcap)
        (fun rho _ _ => norm_nonneg _)
    _ = actualSelectedHeightMovingCarlsonMiddleMass H delta m +
          actualSelectedHeightMovingCarlsonStripMass H delta m := by
      rw [Finset.sum_union
        actualSelectedHeightMovingCarlsonMiddle_disjoint_strip]
      rfl

theorem
    dynamicPositivePNTTailNorm_le_selectedCriticalHalf_add_movingMasses
    {H : ℝ → ℝ} {delta : ℕ → ℝ} {m : ℕ}
    (hcap : ActualSelectedHeightMovingPositiveRightEdgeCap H delta m) :
    dynamicPositivePNTTailNorm H (m : ℝ) ≤
      (dynamicPositiveOutsideClusterPNTLayerNorm H ∅
          (actualSelectedHeightCriticalHalfCanonicalInput H)
          0 (m : ℝ) +
        actualSelectedHeightMovingCarlsonMiddleMass H delta m) +
      actualSelectedHeightMovingCarlsonStripMass H delta m := by
  calc
    dynamicPositivePNTTailNorm H (m : ℝ) =
        dynamicPositiveOutsideClusterPNTTailNorm H ∅ (m : ℝ) := by
      simp [dynamicPositivePNTTailNorm,
        dynamicPositiveOutsideClusterPNTTailNorm,
        positiveNontrivialZerosOutsideClusterFinset]
    _ ≤ ∑ i,
        dynamicPositiveOutsideClusterPNTLayerNorm H ∅
          (actualSelectedHeightCriticalHalfCanonicalInput H)
          i (m : ℝ) :=
      dynamicPositiveOutsideClusterPNTTailNorm_le_sum_layerNorms
        (actualSelectedHeightCriticalHalfCanonicalInput H) (m : ℝ)
    _ =
        dynamicPositiveOutsideClusterPNTLayerNorm H ∅
            (actualSelectedHeightCriticalHalfCanonicalInput H)
            0 (m : ℝ) +
          dynamicPositiveOutsideClusterPNTLayerNorm H ∅
            (actualSelectedHeightCriticalHalfCanonicalInput H)
            1 (m : ℝ) := by
      rw [Fin.sum_univ_two]
    _ ≤
        dynamicPositiveOutsideClusterPNTLayerNorm H ∅
            (actualSelectedHeightCriticalHalfCanonicalInput H)
            0 (m : ℝ) +
          (actualSelectedHeightMovingCarlsonMiddleMass H delta m +
            actualSelectedHeightMovingCarlsonStripMass H delta m) :=
      add_le_add_right
        (actualSelectedHeightCriticalHalf_highLayerNorm_le_movingMasses hcap) _
    _ =
        (dynamicPositiveOutsideClusterPNTLayerNorm H ∅
            (actualSelectedHeightCriticalHalfCanonicalInput H)
            0 (m : ℝ) +
          actualSelectedHeightMovingCarlsonMiddleMass H delta m) +
        actualSelectedHeightMovingCarlsonStripMass H delta m := by
      ring

/-- Positive zero-tail decay at a selected explicit-formula height. -/
theorem
    tendsto_dynamicPositivePNTTailNorm_of_selectedHeightMovingCarlson
    {H : ℝ → ℝ} {innerAlpha outerAlpha epsilon : ℝ}
    {delta : ℕ → ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (houter : 0 < outerAlpha)
    (hepsilon : 0 < epsilon)
    (hmargin : outerAlpha + epsilon < 1 / 2)
    (hwindow : ∀ᶠ x : ℝ in atTop,
      H x ∈ Set.Icc
        (carlsonPolynomialHeight innerAlpha x)
        (carlsonPolynomialHeight innerAlpha x + 1))
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8 ∧
        128 * outerAlpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta)
    (hcap : ∀ᶠ m : ℕ in atTop,
      ActualSelectedHeightMovingPositiveRightEdgeCap H delta m)
    (hmiddle :
      Tendsto
        (actualSelectedHeightMovingCarlsonMiddleMass H delta)
        atTop (nhds 0)) :
    Tendsto
      (fun m : ℕ => dynamicPositivePNTTailNorm H (m : ℝ))
      atTop (nhds 0) := by
  have hcritical :=
    tendsto_actualSelectedHeightCriticalHalfPNTLayerNorm_zero
      hinner hstrict houter hepsilon hmargin hwindow
  have hwindowNat :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ∈ Set.Icc
          (carlsonPolynomialHeight innerAlpha (m : ℝ))
          (carlsonPolynomialHeight innerAlpha (m : ℝ) + 1) :=
    tendsto_natCast_atTop_atTop.eventually hwindow
  have hmoving :=
    tendsto_actualSelectedHeightMovingCarlsonStripMass_zero
      hinner.le hstrict houter hwindowNat hdelta hgap
  have hmajorant :
      Tendsto
        (fun m : ℕ =>
          (dynamicPositiveOutsideClusterPNTLayerNorm H ∅
              (actualSelectedHeightCriticalHalfCanonicalInput H)
              0 (m : ℝ) +
            actualSelectedHeightMovingCarlsonMiddleMass H delta m) +
          actualSelectedHeightMovingCarlsonStripMass H delta m)
        atTop (nhds 0) := by
    simpa using (hcritical.add hmiddle).add hmoving
  refine squeeze_zero' ?_ ?_ hmajorant
  · filter_upwards with m
    exact norm_nonneg _
  · filter_upwards [hcap] with m hm
    exact
      dynamicPositivePNTTailNorm_le_selectedCriticalHalf_add_movingMasses hm

end

end PrimeNumberTheorem
