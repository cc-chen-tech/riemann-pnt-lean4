import PrimeNumberTheorem.ZeroForcingUnifiedTransfer

namespace PrimeNumberTheorem

example
    (pntError : ℝ → ℂ) (upperCost amplitude : ℝ → ℝ) (x₀ : ℝ)
    (hupper : ∀ x, x₀ ≤ x → ‖pntError x‖ ≤ upperCost x)
    (hlower : ∀ X, ∃ x, X ≤ x ∧ amplitude x ≤ ‖pntError x‖) :
    DynamicUpperConclusion pntError upperCost x₀ ×
      OscillationLowerConclusion pntError amplitude :=
  unified_dynamic_transfer hupper hlower

example (heightThreshold : ℝ) :
    ∀ᶠ x in Filter.atTop,
      AdmissibleHeight heightThreshold x (Pintz.pintzZeroEnvelope x) :=
  eventually_admissible_pintzZeroEnvelope heightThreshold

end PrimeNumberTheorem
