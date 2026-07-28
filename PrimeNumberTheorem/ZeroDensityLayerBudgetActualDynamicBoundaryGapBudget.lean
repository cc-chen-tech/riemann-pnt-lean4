import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryPackage
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonStripEndpointCriterion
import PrimeNumberTheorem.ZeroDensityLayerBudgetMovingGapBarrier

/-!
# Density budgets for dynamic boundary packages

For a complementary zero layer bounded by `beta - gap`, normalization by the
target scale `x^(beta - 1)` leaves the exponent

`densityExponent - gap`.

Thus pointwise positivity of the finite-complement gap is not enough:
Carlson decay requires the gap to exceed the density cost.  With an
admissible contour height and a positive Carlson slope, this forces an
eventual fixed positive gap.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- At an upper endpoint `beta - gap`, the normalized strip exponent is the
density cost minus the real-part gap. -/
theorem targetAmplitudeStripEndpointExponent_boundaryGap
    (beta gap densityExponent : ℝ) :
    targetAmplitudeStripEndpointExponent beta (beta - gap) densityExponent =
      densityExponent - gap := by
  simp [targetAmplitudeStripEndpointExponent]
  ring

/-- Endpoint-aware decay below `beta - gap` occurs exactly when the gap
strictly exceeds the density exponent. -/
theorem targetAmplitudeStripEndpointExponent_boundaryGap_lt_zero_iff
    (beta gap densityExponent : ℝ) :
    targetAmplitudeStripEndpointExponent beta (beta - gap) densityExponent < 0 ↔
      densityExponent < gap := by
  rw [targetAmplitudeStripEndpointExponent_boundaryGap]
  constructor <;> intro h <;> linarith

/-- For Carlson's classical polynomial-height density input, the exact gap
cost is `alpha * 4 * sigma * (1 - sigma)`. -/
theorem carlsonClassical_boundaryGap_decay_iff
    (beta gap alpha sigma : ℝ) :
    targetAmplitudeStripEndpointExponent beta (beta - gap)
        (carlsonClassicalPolynomialDensityExponent alpha sigma) < 0 ↔
      alpha * (4 * sigma * (1 - sigma)) < gap := by
  rw [targetAmplitudeStripEndpointExponent_boundaryGap_lt_zero_iff]
  simp [carlsonClassicalPolynomialDensityExponent,
    carlsonPolynomialHeightDensityExponent, mul_assoc]

/--
Once the polynomial height clears the target-amplitude contour threshold,
Carlson decay at `beta - gap` forces a fixed gap exceeding
`4 * sigma * (1 - sigma) * (1 - beta)`.
-/
theorem carlsonClassical_boundaryGap_exceeds_contourFloor
    {beta gap alpha sigma : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hcontour : 1 - beta < alpha)
    (hdecay :
      targetAmplitudeStripEndpointExponent beta (beta - gap)
        (carlsonClassicalPolynomialDensityExponent alpha sigma) < 0) :
    (4 * sigma * (1 - sigma)) * (1 - beta) < gap := by
  have hq : 0 < 4 * sigma * (1 - sigma) :=
    carlsonClassicalDensitySlope_pos hsigma hsigmaOne
  have hcost :
      alpha * (4 * sigma * (1 - sigma)) < gap :=
    (carlsonClassical_boundaryGap_decay_iff
      beta gap alpha sigma).mp hdecay
  have hscaled :
      (1 - beta) * (4 * sigma * (1 - sigma)) <
        alpha * (4 * sigma * (1 - sigma)) :=
    mul_lt_mul_of_pos_right hcontour hq
  calc
    (4 * sigma * (1 - sigma)) * (1 - beta) =
        (1 - beta) * (4 * sigma * (1 - sigma)) := by ring
    _ < alpha * (4 * sigma * (1 - sigma)) := hscaled
    _ < gap := hcost

/--
Choose the positive gap supplied by the finite outside-zero complement at
each natural scale.
-/
noncomputable def dynamicEqualRealPartOutsideGap
    (H : ℝ → ℝ) (beta : ℝ)
    (hright :
      ∀ m : ℕ, ∀ z ∈ positiveNontrivialZerosFinset (H (m : ℝ)),
        z.re ≤ beta)
    (m : ℕ) : ℝ :=
  Classical.choose
    (exists_dynamicEqualRealPartOutside_pos_gap
      (H := H) (beta := beta) (x := (m : ℝ)) (hright m))

theorem dynamicEqualRealPartOutsideGap_pos
    {H : ℝ → ℝ} {beta : ℝ}
    (hright :
      ∀ m : ℕ, ∀ z ∈ positiveNontrivialZerosFinset (H (m : ℝ)),
        z.re ≤ beta)
    (m : ℕ) :
    0 < dynamicEqualRealPartOutsideGap H beta hright m := by
  unfold dynamicEqualRealPartOutsideGap
  exact
    (Classical.choose_spec
      (exists_dynamicEqualRealPartOutside_pos_gap
        (H := H) (beta := beta) (x := (m : ℝ)) (hright m))).1

theorem dynamicEqualRealPartOutsideGap_spec
    {H : ℝ → ℝ} {beta : ℝ}
    (hright :
      ∀ m : ℕ, ∀ z ∈ positiveNontrivialZerosFinset (H (m : ℝ)),
        z.re ≤ beta)
    (m : ℕ) :
    ∀ z ∈ positiveNontrivialZerosOutsideClusterFinset (H (m : ℝ))
        (dynamicEqualRealPartZeroPackage H beta (m : ℝ)),
      z.re ≤ beta - dynamicEqualRealPartOutsideGap H beta hright m := by
  unfold dynamicEqualRealPartOutsideGap
  exact
    (Classical.choose_spec
      (exists_dynamicEqualRealPartOutside_pos_gap
        (H := H) (beta := beta) (x := (m : ℝ)) (hright m))).2

/--
If the selected actual-zero gap absorbs a positive Carlson density cost while
the same height remains target-amplitude admissible, then that selected gap
is eventually bounded below by a fixed positive constant.
-/
theorem eventually_fixed_dynamicBoundaryGap_of_carlsonDensity
    {H : ℝ → ℝ} {beta sigma : ℝ}
    (hright :
      ∀ m : ℕ, ∀ z ∈ positiveNontrivialZerosFinset (H (m : ℝ)),
        z.re ≤ beta)
    (hbeta : beta < 1)
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hcontour :
      IsTargetAmplitudeAdmissibleHeight beta
        (fun m : ℕ => Real.log (H (m : ℝ))))
    (hdensity :
      IsMovingDensityGapAdmissible
        (4 * sigma * (1 - sigma))
        (fun m : ℕ => Real.log (H (m : ℝ)))
        (dynamicEqualRealPartOutsideGap H beta hright)) :
    ∀ᶠ m in atTop,
      (4 * sigma * (1 - sigma)) * (1 - beta) <
        dynamicEqualRealPartOutsideGap H beta hright m := by
  exact eventually_fixedGap_of_contour_and_movingDensity
    hbeta (carlsonClassicalDensitySlope_pos hsigma hsigmaOne)
    hcontour hdensity

/--
Consequently, a selected dynamic boundary gap tending to zero cannot support
both target-amplitude contour control and a positive-slope Carlson aggregate.
-/
theorem not_dynamicBoundaryGap_tendsto_zero_of_carlsonDensity
    {H : ℝ → ℝ} {beta sigma : ℝ}
    (hright :
      ∀ m : ℕ, ∀ z ∈ positiveNontrivialZerosFinset (H (m : ℝ)),
        z.re ≤ beta)
    (hbeta : beta < 1)
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hcontour :
      IsTargetAmplitudeAdmissibleHeight beta
        (fun m : ℕ => Real.log (H (m : ℝ))))
    (hdensity :
      IsMovingDensityGapAdmissible
        (4 * sigma * (1 - sigma))
        (fun m : ℕ => Real.log (H (m : ℝ)))
        (dynamicEqualRealPartOutsideGap H beta hright)) :
    ¬ Tendsto
        (dynamicEqualRealPartOutsideGap H beta hright)
        atTop (𝓝 0) := by
  exact not_movingDensityGap_tendsto_zero_of_contour
    hbeta (carlsonClassicalDensitySlope_pos hsigma hsigmaOne)
    hcontour hdensity

end PrimeNumberTheorem
