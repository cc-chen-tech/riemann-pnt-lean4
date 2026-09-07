import HardyTheorem.AFEExplicitMellinAmplitudeBounds
import HardyTheorem.AFEExplicitPoissonQuotient

/-!
# Explicit majorant for the twice-integrated Poisson remainder

This module inserts the pointwise Mellin-amplitude bounds into the four exact
classes in the derivative of the second phase quotient.
-/

noncomputable section

namespace HardyTheorem
namespace AFE

theorem norm_explicitPoissonSecondQuotientDerivative_le_majorant
    {C₁ C₂ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂)
    (sigma x N t : ℝ) (k : ℤ) {u : ℝ} (hu : 0 < u)
    (hv0 : weightedPoissonVelocity t k u ≠ 0) :
    ‖explicitPoissonSecondQuotientDerivative sigma x N t k u‖ ≤
      |1 / (weightedPoissonVelocity t k u) ^ 2| *
        ((2 * C₂ + 2 * C₁ ^ 2) * u ^ (-sigma) +
          4 * C₁ * |sigma| * u ^ (-sigma - 1) +
          |sigma| * |sigma + 1| * u ^ (-sigma - 2)) +
      |3 * weightedPoissonVelocityDeriv t u /
          (weightedPoissonVelocity t k u) ^ 3| *
        (2 * C₁ * u ^ (-sigma) + |sigma| * u ^ (-sigma - 1)) +
      |weightedPoissonVelocitySecondDeriv t u /
          (weightedPoissonVelocity t k u) ^ 3| * u ^ (-sigma) +
      |3 * (weightedPoissonVelocityDeriv t u) ^ 2 /
          (weightedPoissonVelocity t k u) ^ 4| * u ^ (-sigma) := by
  refine (norm_explicitPoissonSecondQuotientDerivative_le hv0).trans ?_
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (norm_explicitComplexMellinAmplitudeSecondDeriv_le
            hC₁0 hC₂0 hC₁ hC₂ sigma x N hu)
          (abs_nonneg _)
      · exact mul_le_mul_of_nonneg_left
          (norm_explicitComplexMellinAmplitudeDeriv_le
            hC₁0 hC₁ sigma x N hu)
          (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left
        (norm_explicitComplexMellinAmplitude_le sigma x N hu)
        (abs_nonneg _)
  · exact mul_le_mul_of_nonneg_left
      (norm_explicitComplexMellinAmplitude_le sigma x N hu)
      (abs_nonneg _)

end AFE
end HardyTheorem
