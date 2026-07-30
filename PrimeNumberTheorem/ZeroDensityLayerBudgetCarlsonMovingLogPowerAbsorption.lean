import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonMovingCoefficientGrowth

namespace PrimeNumberTheorem

open Filter Topology

/-- Logarithmic coefficient envelope retaining both the quadratic
`delta⁻²` cost and Carlson's fourth power of the height logarithm. -/
noncomputable def carlsonMovingQuadraticLogPowerEnvelope
    (C : ℝ) (delta : ℕ → ℝ) (m : ℕ) : ℝ :=
  Real.log C +
    2 * Real.log (delta m)⁻¹ +
    4 * Real.log (Real.log (m : ℝ))

/-- The honest moving-gap condition after retaining the fourth logarithm from
the pointwise Carlson count theorem. -/
def IsCarlsonMovingQuadraticLogPowerGap
    (delta : ℕ → ℝ) : Prop :=
  Tendsto
    (fun m =>
      delta m / 2 * Real.log (m : ℝ) -
        (2 * Real.log (delta m)⁻¹ +
          4 * Real.log (Real.log (m : ℝ))))
    atTop atTop

/-- Any fixed multiple of `delta⁻² (log m)^4` is admissible when the complete
quadratic-log-power cost fits inside half of the balanced strip gap. -/
theorem carlsonMovingQuadraticLogPowerEnvelope_admissible
    {C : ℝ} {delta : ℕ → ℝ}
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta) :
    IsCarlsonMovingBalancedCoefficientAdmissible delta
      (carlsonMovingQuadraticLogPowerEnvelope C delta) := by
  have hshift :=
    tendsto_atTop_add_const_right atTop (-Real.log C) hgap
  apply hshift.congr'
  filter_upwards with m
  unfold carlsonMovingBalancedCoefficientLogMargin
    carlsonMovingQuadraticLogPowerEnvelope
  ring

/-- Carlson's moving balanced ratio still decays after retaining the full
quadratic coefficient and fourth-logarithm costs. -/
theorem tendsto_carlsonMovingQuadraticLogPowerCoefficientRatio_zero
    {alpha C : ℝ} {delta : ℕ → ℝ}
    (halpha : 0 ≤ alpha)
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 2 ∧
        128 * alpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta) :
    Tendsto
      (carlsonMovingBalancedCoefficientRatio alpha delta
        (carlsonMovingQuadraticLogPowerEnvelope C delta))
      atTop (nhds 0) :=
  tendsto_carlsonMovingBalancedCoefficientRatio_zero
    halpha hdelta
      (carlsonMovingQuadraticLogPowerEnvelope_admissible hgap)

end PrimeNumberTheorem
