import PrimeNumberTheorem.CarlsonTwoScaleDetectorGrowth

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Y0 Y1 : ℕ}, 1 ≤ Y0 → Y0 < Y1 →
      ∀ {T : ℝ}, 5 ≤ T → ∀ {z : ℂ},
        z ∈ Metric.sphere
          ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ) →
        ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 z‖ ≤
          C * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10 :=
  exists_norm_regularizedTwoScaleCarlsonZeroDetector_le_fixedJensenSphere

example :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Y0 Y1 : ℕ}, 1 ≤ Y0 → Y0 < Y1 →
      ∀ {T : ℝ}, 5 ≤ T →
        ‖twoScaleMollifiedZetaError Y0 Y1
          ((4 : ℂ) + I * (T + 1 / 2))‖ ≤ (1 / 3 : ℝ) →
        regularizedTwoScaleCarlsonFactorDiskZeroMass Y0 Y1 T ≤
          Real.log (C * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10) /
            Real.log ((31 / 8 : ℝ) / (123 / 32 : ℝ)) :=
  exists_regularizedTwoScaleCarlsonFactorDiskZeroMass_le_logPolynomial

example :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Y0 Y1 : ℕ}, 2 ≤ Y0 → Y0 < Y1 →
      ∀ {T : ℝ}, 5 ≤ T →
        regularizedTwoScaleCarlsonFactorDiskZeroMass Y0 Y1 T ≤
          Real.log (C * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10) /
            Real.log ((31 / 8 : ℝ) / (123 / 32 : ℝ)) :=
  exists_regularizedTwoScaleCarlsonFactorDiskZeroMass_le_logPolynomial_of_two_le_inner

example :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Y0 Y1 : ℕ}, 2 ≤ Y0 → Y0 < Y1 →
      ∀ {T : ℝ}, 5 ≤ T →
        regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T ≤
          Real.log (C * (Y1 : ℝ) ^ 2 * (T + 14) ^ 10) /
            Real.log ((31 / 8 : ℝ) / (123 / 32 : ℝ)) :=
  exists_regularizedTwoScaleCarlsonInnerFactorDiskZeroMass_le_logPolynomial

example {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1) {T : ℝ} :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g
        (Metric.closedBall
          ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) ∧
      (∀ u : (Metric.closedBall
          ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ) : Set ℂ),
        g u ≠ 0) ∧
      -Real.log (123 / 32 : ℝ) *
          regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T ≤
        Real.log ‖g ((4 : ℂ) + I * (T + 1 / 2))‖ :=
  exists_regularizedTwoScaleCarlsonZeroDetector_fixedJensenFactor_center_lower
    hY0 hY01

end CarlsonZeroDensity
end PrimeNumberTheorem
