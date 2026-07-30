import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonMovingCoefficientGrowth
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonMovingLogPowerAbsorption

/-!
# Dynamic layer-count cost for moving Carlson strips

A real-part cover reaching a boundary `delta(m)` away from `1` cannot in
general use a fixed number of strips.  For a geometric cover the number of
strips grows, but only its logarithm enters the exponential majorant.

This file isolates that cost.  If every one of `layers(m)` strip masses is
bounded by the same quadratic-coefficient Carlson ratio, their sum is bounded
by the ratio obtained by adding

`log (layers(m) + 1)`

to the coefficient envelope.  Thus the exact remaining condition is

`delta(m) / 2 * log m
  - 2 * log (1 / delta(m))
  - log (layers(m) + 1) -> +infinity`.

No zero-density theorem is asserted here: a later actual-zeta module must
supply the pointwise bound for each strip in the chosen geometric cover.
-/

namespace PrimeNumberTheorem

open Filter Topology
open scoped BigOperators

noncomputable section

/-- Logarithmic price of summing a height-dependent finite strip family. -/
noncomputable def carlsonDynamicLayerCountLogCost
    (layers : ℕ → ℕ) (m : ℕ) : ℝ :=
  Real.log ((layers m : ℝ) + 1)

/-- Quadratic moving-Carlson coefficient envelope with the dynamic layer
count included. -/
noncomputable def carlsonMovingLayeredQuadraticLogEnvelope
    (C : ℝ) (delta : ℕ → ℝ) (layers : ℕ → ℕ) (m : ℕ) : ℝ :=
  carlsonMovingQuadraticLogEnvelope C delta m +
    carlsonDynamicLayerCountLogCost layers m

/-- The precise logarithmic margin needed after summing a dynamic number of
quadratic-coefficient Carlson strips. -/
def IsCarlsonMovingQuadraticLayerCountGap
    (delta : ℕ → ℝ) (layers : ℕ → ℕ) : Prop :=
  Tendsto
    (fun m =>
      delta m / 2 * Real.log (m : ℝ) -
        2 * Real.log (delta m)⁻¹ -
        carlsonDynamicLayerCountLogCost layers m)
    atTop atTop

/-- The layer-count gap is exactly coefficient admissibility for the enlarged
logarithmic envelope. -/
theorem carlsonMovingLayeredQuadraticLogEnvelope_admissible
    {C : ℝ} {delta : ℕ → ℝ} {layers : ℕ → ℕ}
    (hgap : IsCarlsonMovingQuadraticLayerCountGap delta layers) :
    IsCarlsonMovingBalancedCoefficientAdmissible delta
      (carlsonMovingLayeredQuadraticLogEnvelope C delta layers) := by
  have hshift :=
    tendsto_atTop_add_const_right atTop (-Real.log C) hgap
  apply hshift.congr'
  filter_upwards with m
  unfold carlsonMovingBalancedCoefficientLogMargin
    carlsonMovingLayeredQuadraticLogEnvelope
    carlsonMovingQuadraticLogEnvelope
  ring

/-- Adding the logarithmic layer count multiplies the one-strip ratio by
`layers(m) + 1`. -/
theorem carlsonMovingLayeredQuadraticRatio_eq
    (alpha C : ℝ) (delta : ℕ → ℝ) (layers : ℕ → ℕ) (m : ℕ) :
    carlsonMovingBalancedCoefficientRatio alpha delta
        (carlsonMovingLayeredQuadraticLogEnvelope C delta layers) m =
      ((layers m : ℝ) + 1) *
        carlsonMovingBalancedCoefficientRatio alpha delta
          (carlsonMovingQuadraticLogEnvelope C delta) m := by
  have hlayersPos : 0 < (layers m : ℝ) + 1 := by positivity
  unfold carlsonMovingBalancedCoefficientRatio
    carlsonMovingLayeredQuadraticLogEnvelope
    carlsonDynamicLayerCountLogCost
  rw [show
      carlsonMovingQuadraticLogEnvelope C delta m +
            Real.log ((layers m : ℝ) + 1) +
            carlsonTwoHeightBalancedExponent
                (1 - 2 * delta m) (1 - delta m) alpha *
              Real.log (m : ℝ) =
          Real.log ((layers m : ℝ) + 1) +
            (carlsonMovingQuadraticLogEnvelope C delta m +
              carlsonTwoHeightBalancedExponent
                  (1 - 2 * delta m) (1 - delta m) alpha *
                Real.log (m : ℝ)) by ring]
  rw [Real.exp_add, Real.exp_log hlayersPos]

/-- A dynamic finite family of nonnegative layer masses.  The dependent
index permits the number of real-part strips to vary with `m`. -/
noncomputable def carlsonDynamicFiniteLayerMass
    (layers : ℕ → ℕ)
    (mass : (m : ℕ) → Fin (layers m) → ℝ)
    (m : ℕ) : ℝ :=
  ∑ i, mass m i

/-- Pointwise aggregation: a common one-strip Carlson majorant acquires only
the multiplicative factor `layers(m) + 1`. -/
theorem carlsonDynamicFiniteLayerMass_le_layeredQuadraticRatio
    {alpha C : ℝ} {delta : ℕ → ℝ} {layers : ℕ → ℕ}
    {mass : (m : ℕ) → Fin (layers m) → ℝ} {m : ℕ}
    (hmass :
      ∀ i,
        mass m i ≤
          carlsonMovingBalancedCoefficientRatio alpha delta
            (carlsonMovingQuadraticLogEnvelope C delta) m) :
    carlsonDynamicFiniteLayerMass layers mass m ≤
      carlsonMovingBalancedCoefficientRatio alpha delta
        (carlsonMovingLayeredQuadraticLogEnvelope C delta layers) m := by
  let ratio :=
    carlsonMovingBalancedCoefficientRatio alpha delta
      (carlsonMovingQuadraticLogEnvelope C delta) m
  have hratio : 0 ≤ ratio := by
    dsimp [ratio]
    exact (Real.exp_pos _).le
  calc
    carlsonDynamicFiniteLayerMass layers mass m
        ≤ ∑ _i : Fin (layers m), ratio := by
          unfold carlsonDynamicFiniteLayerMass
          exact Finset.sum_le_sum fun i _ => hmass i
    _ = (layers m : ℝ) * ratio := by simp
    _ ≤ ((layers m : ℝ) + 1) * ratio := by
      exact mul_le_mul_of_nonneg_right
        (by linarith : (layers m : ℝ) ≤ (layers m : ℝ) + 1) hratio
    _ = carlsonMovingBalancedCoefficientRatio alpha delta
          (carlsonMovingLayeredQuadraticLogEnvelope C delta layers) m := by
      rw [carlsonMovingLayeredQuadraticRatio_eq]

/-- Dynamic strip aggregation preserves decay exactly when the layer-count
logarithm fits inside the moving Carlson margin. -/
theorem tendsto_carlsonDynamicFiniteLayerMass_zero
    {alpha C : ℝ} {delta : ℕ → ℝ} {layers : ℕ → ℕ}
    {mass : (m : ℕ) → Fin (layers m) → ℝ}
    (halpha : 0 ≤ alpha)
    (hdelta :
      ∀ᶠ m : ℕ in atTop,
        0 < delta m ∧ delta m ≤ 1 / 2 ∧
          128 * alpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLayerCountGap delta layers)
    (hmassNonneg :
      ∀ᶠ m : ℕ in atTop, ∀ i, 0 ≤ mass m i)
    (hmass :
      ∀ᶠ m : ℕ in atTop, ∀ i,
        mass m i ≤
          carlsonMovingBalancedCoefficientRatio alpha delta
            (carlsonMovingQuadraticLogEnvelope C delta) m) :
    Tendsto (carlsonDynamicFiniteLayerMass layers mass)
      atTop (nhds 0) := by
  have hmajorant :
      Tendsto
        (carlsonMovingBalancedCoefficientRatio alpha delta
          (carlsonMovingLayeredQuadraticLogEnvelope C delta layers))
        atTop (nhds 0) :=
    tendsto_carlsonMovingBalancedCoefficientRatio_zero
      halpha hdelta
        (carlsonMovingLayeredQuadraticLogEnvelope_admissible hgap)
  apply squeeze_zero'
  · filter_upwards [hmassNonneg] with m hm
    unfold carlsonDynamicFiniteLayerMass
    exact Finset.sum_nonneg fun i _ => hm i
  · filter_upwards [hmass] with m hm
    exact
      carlsonDynamicFiniteLayerMass_le_layeredQuadraticRatio hm
  · exact hmajorant

/-- The honest pointwise Carlson envelope, including both the fourth
logarithmic power and the dynamic layer-count cost. -/
noncomputable def carlsonMovingLayeredQuadraticLogPowerEnvelope
    (C : ℝ) (delta : ℕ → ℝ) (layers : ℕ → ℕ) (m : ℕ) : ℝ :=
  carlsonMovingQuadraticLogPowerEnvelope C delta m +
    carlsonDynamicLayerCountLogCost layers m

/-- Complete margin for a dynamic family of pointwise Carlson strips.  The
four displayed costs are respectively the kernel decay, quadratic coefficient
growth, Carlson's fourth log power, and the number of real-part layers. -/
def IsCarlsonMovingQuadraticLogPowerLayerCountGap
    (delta : ℕ → ℝ) (layers : ℕ → ℕ) : Prop :=
  Tendsto
    (fun m =>
      delta m / 2 * Real.log (m : ℝ) -
        2 * Real.log (delta m)⁻¹ -
        4 * Real.log (Real.log (m : ℝ)) -
        carlsonDynamicLayerCountLogCost layers m)
    atTop atTop

theorem carlsonMovingLayeredQuadraticLogPowerEnvelope_admissible
    {C : ℝ} {delta : ℕ → ℝ} {layers : ℕ → ℕ}
    (hgap :
      IsCarlsonMovingQuadraticLogPowerLayerCountGap delta layers) :
    IsCarlsonMovingBalancedCoefficientAdmissible delta
      (carlsonMovingLayeredQuadraticLogPowerEnvelope
        C delta layers) := by
  have hshift :=
    tendsto_atTop_add_const_right atTop (-Real.log C) hgap
  apply hshift.congr'
  filter_upwards with m
  unfold carlsonMovingBalancedCoefficientLogMargin
    carlsonMovingLayeredQuadraticLogPowerEnvelope
    carlsonMovingQuadraticLogPowerEnvelope
  ring

theorem carlsonMovingLayeredQuadraticLogPowerRatio_eq
    (alpha C : ℝ) (delta : ℕ → ℝ) (layers : ℕ → ℕ) (m : ℕ) :
    carlsonMovingBalancedCoefficientRatio alpha delta
        (carlsonMovingLayeredQuadraticLogPowerEnvelope
          C delta layers) m =
      ((layers m : ℝ) + 1) *
        carlsonMovingBalancedCoefficientRatio alpha delta
          (carlsonMovingQuadraticLogPowerEnvelope C delta) m := by
  have hlayersPos : 0 < (layers m : ℝ) + 1 := by positivity
  unfold carlsonMovingBalancedCoefficientRatio
    carlsonMovingLayeredQuadraticLogPowerEnvelope
    carlsonDynamicLayerCountLogCost
  rw [show
      carlsonMovingQuadraticLogPowerEnvelope C delta m +
            Real.log ((layers m : ℝ) + 1) +
            carlsonTwoHeightBalancedExponent
                (1 - 2 * delta m) (1 - delta m) alpha *
              Real.log (m : ℝ) =
          Real.log ((layers m : ℝ) + 1) +
            (carlsonMovingQuadraticLogPowerEnvelope C delta m +
              carlsonTwoHeightBalancedExponent
                  (1 - 2 * delta m) (1 - delta m) alpha *
                Real.log (m : ℝ)) by ring]
  rw [Real.exp_add, Real.exp_log hlayersPos]

/-- Pointwise aggregation for the complete log-power Carlson ratio. -/
theorem carlsonDynamicFiniteLayerMass_le_layeredQuadraticLogPowerRatio
    {alpha C : ℝ} {delta : ℕ → ℝ} {layers : ℕ → ℕ}
    {mass : (m : ℕ) → Fin (layers m) → ℝ} {m : ℕ}
    (hmass :
      ∀ i,
        mass m i ≤
          carlsonMovingBalancedCoefficientRatio alpha delta
            (carlsonMovingQuadraticLogPowerEnvelope C delta) m) :
    carlsonDynamicFiniteLayerMass layers mass m ≤
      carlsonMovingBalancedCoefficientRatio alpha delta
        (carlsonMovingLayeredQuadraticLogPowerEnvelope
          C delta layers) m := by
  let ratio :=
    carlsonMovingBalancedCoefficientRatio alpha delta
      (carlsonMovingQuadraticLogPowerEnvelope C delta) m
  have hratio : 0 ≤ ratio := by
    dsimp [ratio]
    exact (Real.exp_pos _).le
  calc
    carlsonDynamicFiniteLayerMass layers mass m
        ≤ ∑ _i : Fin (layers m), ratio := by
          unfold carlsonDynamicFiniteLayerMass
          exact Finset.sum_le_sum fun i _ => hmass i
    _ = (layers m : ℝ) * ratio := by simp
    _ ≤ ((layers m : ℝ) + 1) * ratio := by
      exact mul_le_mul_of_nonneg_right
        (by linarith : (layers m : ℝ) ≤ (layers m : ℝ) + 1) hratio
    _ = carlsonMovingBalancedCoefficientRatio alpha delta
          (carlsonMovingLayeredQuadraticLogPowerEnvelope
            C delta layers) m := by
      rw [carlsonMovingLayeredQuadraticLogPowerRatio_eq]

/-- A dynamic family of actual or model strip masses decays under the complete
pointwise Carlson margin. -/
theorem tendsto_carlsonDynamicFiniteLayerMass_zero_logPower
    {alpha C : ℝ} {delta : ℕ → ℝ} {layers : ℕ → ℕ}
    {mass : (m : ℕ) → Fin (layers m) → ℝ}
    (halpha : 0 ≤ alpha)
    (hdelta :
      ∀ᶠ m : ℕ in atTop,
        0 < delta m ∧ delta m ≤ 1 / 2 ∧
          128 * alpha * delta m ≤ 1)
    (hgap :
      IsCarlsonMovingQuadraticLogPowerLayerCountGap delta layers)
    (hmassNonneg :
      ∀ᶠ m : ℕ in atTop, ∀ i, 0 ≤ mass m i)
    (hmass :
      ∀ᶠ m : ℕ in atTop, ∀ i,
        mass m i ≤
          carlsonMovingBalancedCoefficientRatio alpha delta
            (carlsonMovingQuadraticLogPowerEnvelope C delta) m) :
    Tendsto (carlsonDynamicFiniteLayerMass layers mass)
      atTop (nhds 0) := by
  have hmajorant :
      Tendsto
        (carlsonMovingBalancedCoefficientRatio alpha delta
          (carlsonMovingLayeredQuadraticLogPowerEnvelope
            C delta layers))
        atTop (nhds 0) :=
    tendsto_carlsonMovingBalancedCoefficientRatio_zero
      halpha hdelta
        (carlsonMovingLayeredQuadraticLogPowerEnvelope_admissible hgap)
  apply squeeze_zero'
  · filter_upwards [hmassNonneg] with m hm
    unfold carlsonDynamicFiniteLayerMass
    exact Finset.sum_nonneg fun i _ => hm i
  · filter_upwards [hmass] with m hm
    exact
      carlsonDynamicFiniteLayerMass_le_layeredQuadraticLogPowerRatio hm
  · exact hmajorant

end

end PrimeNumberTheorem
