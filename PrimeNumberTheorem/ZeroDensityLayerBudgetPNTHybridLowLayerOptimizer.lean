import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridDensity

/-!
# Optimizing the low-real-part part of the hybrid PNT budget

The hybrid density input bounds a low-real-part layer by the global
multiplicity estimate `O(T log T)`.  If the layer has real-part endpoint
`tau`, normalization by a target zero-power scale `x^beta` and the choice
`T = x^theta` produce the power exponent

`tau - beta + theta`.

The explicit-formula contour term has normalized exponent

`1 - beta - theta`.

This file solves the resulting minimax problem exactly.  The balanced height
is `theta = (1 - tau) / 2`, the optimized exponent is
`(1 + tau) / 2 - beta`, and simultaneous power decay is possible precisely
when `beta > (1 + tau) / 2`.  At the critical-line endpoint `tau = 1 / 2`,
this is the sharp arithmetic barrier `beta > 3 / 4`.

These are arithmetic transfer conditions.  This module does not yet connect
the hybrid count to the actual multiplicity-weighted zeta kernel.
-/

namespace PrimeNumberTheorem

noncomputable section

/-- Normalized power exponent of a low-real-part layer controlled by the
global `O(T log T)` zero multiplicity estimate. -/
def pntHybridLowLayerTargetExponent
    (beta tau theta : ℝ) : ℝ :=
  tau - beta + theta

/-- Normalized power exponent of the explicit-formula contour remainder. -/
def pntHybridContourTargetExponent
    (beta theta : ℝ) : ℝ :=
  1 - beta - theta

/-- Height exponent balancing the low-layer and contour exponents. -/
def pntHybridLowBalancedHeightExponent
    (tau : ℝ) : ℝ :=
  (1 - tau) / 2

/-- Optimized common exponent of the low-layer and contour terms. -/
def pntHybridLowOptimizedTargetExponent
    (beta tau : ℝ) : ℝ :=
  (1 + tau) / 2 - beta

theorem pntHybridLowLayer_balanced_eq_contour
    (beta tau : ℝ) :
    pntHybridLowLayerTargetExponent beta tau
        (pntHybridLowBalancedHeightExponent tau) =
      pntHybridContourTargetExponent beta
        (pntHybridLowBalancedHeightExponent tau) := by
  simp [pntHybridLowLayerTargetExponent,
    pntHybridContourTargetExponent,
    pntHybridLowBalancedHeightExponent]
  ring

theorem pntHybridLowLayer_balanced_eq_optimized
    (beta tau : ℝ) :
    pntHybridLowLayerTargetExponent beta tau
        (pntHybridLowBalancedHeightExponent tau) =
      pntHybridLowOptimizedTargetExponent beta tau := by
  simp [pntHybridLowLayerTargetExponent,
    pntHybridLowBalancedHeightExponent,
    pntHybridLowOptimizedTargetExponent]
  ring

theorem pntHybridContour_balanced_eq_optimized
    (beta tau : ℝ) :
    pntHybridContourTargetExponent beta
        (pntHybridLowBalancedHeightExponent tau) =
      pntHybridLowOptimizedTargetExponent beta tau := by
  rw [← pntHybridLowLayer_balanced_eq_contour]
  exact pntHybridLowLayer_balanced_eq_optimized beta tau

/--
No power-height exponent can improve on the balanced worst exponent.
-/
theorem pntHybridLowOptimizedTargetExponent_le_max
    (beta tau theta : ℝ) :
    pntHybridLowOptimizedTargetExponent beta tau ≤
      max
        (pntHybridLowLayerTargetExponent beta tau theta)
        (pntHybridContourTargetExponent beta theta) := by
  have hsum :
      pntHybridLowLayerTargetExponent beta tau theta +
          pntHybridContourTargetExponent beta theta =
        2 * pntHybridLowOptimizedTargetExponent beta tau := by
    simp [pntHybridLowLayerTargetExponent,
      pntHybridContourTargetExponent,
      pntHybridLowOptimizedTargetExponent]
    ring
  have hleft :
      pntHybridLowLayerTargetExponent beta tau theta ≤
        max
          (pntHybridLowLayerTargetExponent beta tau theta)
          (pntHybridContourTargetExponent beta theta) :=
    le_max_left _ _
  have hright :
      pntHybridContourTargetExponent beta theta ≤
        max
          (pntHybridLowLayerTargetExponent beta tau theta)
          (pntHybridContourTargetExponent beta theta) :=
    le_max_right _ _
  linarith

/-- The balanced height attains the minimax lower bound. -/
theorem pntHybridLow_balanced_max_eq_optimized
    (beta tau : ℝ) :
    max
        (pntHybridLowLayerTargetExponent beta tau
          (pntHybridLowBalancedHeightExponent tau))
        (pntHybridContourTargetExponent beta
          (pntHybridLowBalancedHeightExponent tau)) =
      pntHybridLowOptimizedTargetExponent beta tau := by
  rw [pntHybridLowLayer_balanced_eq_optimized,
    pntHybridContour_balanced_eq_optimized, max_self]

theorem pntHybridLowOptimizedTargetExponent_neg_iff
    (beta tau : ℝ) :
    pntHybridLowOptimizedTargetExponent beta tau < 0 ↔
      (1 + tau) / 2 < beta := by
  simp [pntHybridLowOptimizedTargetExponent]

/--
For `tau < 1`, a positive power-height exponent makes both the low-layer and
contour terms decay exactly when the target exponent lies above the hybrid
barrier `(1 + tau) / 2`.
-/
theorem exists_pos_heightExponent_lowLayer_and_contour_neg_iff
    (beta tau : ℝ)
    (htauOne : tau < 1) :
    (∃ theta : ℝ,
        0 < theta ∧
          pntHybridLowLayerTargetExponent beta tau theta < 0 ∧
          pntHybridContourTargetExponent beta theta < 0) ↔
      (1 + tau) / 2 < beta := by
  constructor
  · rintro ⟨theta, _htheta, hlow, hcontour⟩
    simp [pntHybridLowLayerTargetExponent] at hlow
    simp [pntHybridContourTargetExponent] at hcontour
    linarith
  · intro hbarrier
    refine ⟨pntHybridLowBalancedHeightExponent tau, ?_, ?_, ?_⟩
    · simp [pntHybridLowBalancedHeightExponent]
      linarith
    · rw [pntHybridLowLayer_balanced_eq_optimized]
      exact
        (pntHybridLowOptimizedTargetExponent_neg_iff beta tau).2 hbarrier
    · rw [pntHybridContour_balanced_eq_optimized]
      exact
        (pntHybridLowOptimizedTargetExponent_neg_iff beta tau).2 hbarrier

/-- At the critical-line endpoint, the balanced height exponent is `1 / 4`. -/
theorem pntHybridCriticalHalf_balancedHeightExponent :
    pntHybridLowBalancedHeightExponent (1 / 2 : ℝ) = 1 / 4 := by
  norm_num [pntHybridLowBalancedHeightExponent]

/-- At the critical-line endpoint, the optimized target exponent is
`3 / 4 - beta`. -/
theorem pntHybridCriticalHalf_optimizedTargetExponent
    (beta : ℝ) :
    pntHybridLowOptimizedTargetExponent beta (1 / 2 : ℝ) =
      3 / 4 - beta := by
  norm_num [pntHybridLowOptimizedTargetExponent]

/-- The hybrid critical-half layer and contour term can decay together at a
positive power height exactly for target zero exponents `beta > 3 / 4`. -/
theorem exists_pos_heightExponent_criticalHalf_and_contour_neg_iff
    (beta : ℝ) :
    (∃ theta : ℝ,
        0 < theta ∧
          pntHybridLowLayerTargetExponent beta (1 / 2 : ℝ) theta < 0 ∧
          pntHybridContourTargetExponent beta theta < 0) ↔
      3 / 4 < beta := by
  convert
    exists_pos_heightExponent_lowLayer_and_contour_neg_iff
      beta (1 / 2 : ℝ) (by norm_num) using 1 <;> norm_num

end

end PrimeNumberTheorem
