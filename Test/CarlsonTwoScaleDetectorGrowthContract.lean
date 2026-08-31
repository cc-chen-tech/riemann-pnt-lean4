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

example {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {T : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall
      ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) :
    z ∈ regularizedTwoScaleCarlsonFactorDiskZeroSupport Y0 Y1 T ↔
      regularizedTwoScaleCarlsonZeroDetector Y0 Y1 z = 0 :=
  mem_regularizedTwoScaleCarlsonFactorDiskZeroSupport_iff_zero
    hY0 hY01 hz

example {Y0 Y1 : ℕ} {T L : ℝ}
    (hmass : regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T ≤ L) :
    0 < 1 / (4 * (L + 1)) ∧
      1 / (4 * (L + 1)) ≤
        regularizedTwoScaleCarlsonFactorHorizontalSeparation Y0 Y1 T :=
  regularizedTwoScaleCarlsonFactorHorizontalSeparation_lower_of_mass_le hmass

example {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1) {T : ℝ} :
    ∃ r : ℝ,
      0 < r ∧ r ∈ Set.Icc (121 / 32 : ℝ) (122 / 32 : ℝ) ∧
      (∀ z ∈ Metric.sphere
          ((4 : ℂ) + I * (T + 1 / 2)) r,
        ∀ rho ∈ regularizedTwoScaleCarlsonFactorDiskZeroSupport Y0 Y1 T,
          ((122 / 32 : ℝ) - 121 / 32) /
              (4 * ((((regularizedTwoScaleCarlsonFactorDiskZeroSupport
                Y0 Y1 T).image
                (dist ((4 : ℂ) + I * (T + 1 / 2)))).card : ℝ) + 1)) ≤
            dist z rho) ∧
      (∀ z ∈ Metric.sphere
          ((4 : ℂ) + I * (T + 1 / 2)) r,
        z ∈ Metric.closedBall
          ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) ∧
      ∀ z ∈ Metric.sphere
          ((4 : ℂ) + I * (T + 1 / 2)) r,
        regularizedTwoScaleCarlsonZeroDetector Y0 Y1 z ≠ 0 :=
  exists_regularizedTwoScaleCarlsonZeroDetector_goodFactorCircle hY0 hY01

example :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Y0 Y1 : ℕ}, 2 ≤ Y0 → Y0 < Y1 →
      ∀ {T : ℝ}, 5 ≤ T →
      ∃ r : ℝ, ∃ g : ℂ → ℂ,
        r ∈ Set.Icc (121 / 32 : ℝ) (122 / 32 : ℝ) ∧
        AnalyticOnNhd ℂ g
          (Metric.closedBall
            ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) ∧
        (∀ u : (Metric.closedBall
            ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ) : Set ℂ),
          g u ≠ 0) ∧
        regularizedTwoScaleCarlsonFactorCenterLogLower Y0 Y1 T ≤
          Real.log ‖g ((4 : ℂ) + I * (T + 1 / 2))‖ ∧
        (∀ z ∈ Metric.sphere
            ((4 : ℂ) + I * (T + 1 / 2)) r,
          Real.log ‖g z‖ ≤
            regularizedTwoScaleCarlsonFactorCircleLogUpper C Y0 Y1 T) ∧
        (∀ z ∈ Metric.ball
            ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ),
          regularizedTwoScaleCarlsonZeroDetector Y0 Y1 z ≠ 0 →
            logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) z =
              (∑ᶠ u,
                (MeromorphicOn.divisor
                  (regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
                  (Metric.closedBall
                    ((4 : ℂ) + I * (T + 1 / 2))
                    (123 / 32 : ℝ)) u : ℂ) * (z - u)⁻¹) +
                logDeriv g z) ∧
        ∀ z ∈ Metric.closedBall
            ((4 : ℂ) + I * (T + 1 / 2)) (15 / 4 : ℝ),
          ‖logDeriv g z‖ ≤
            4 * max
                (regularizedTwoScaleCarlsonFactorCircleLogUpper C Y0 Y1 T -
                  regularizedTwoScaleCarlsonFactorCenterLogLower Y0 Y1 T) 1 *
              (r + 15 / 4) / (r - 15 / 4) ^ 2 :=
  exists_regularizedTwoScaleCarlsonZeroDetector_goodFactor_logDeriv_le

example :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Y0 Y1 : ℕ}, 2 ≤ Y0 → Y0 < Y1 →
      ∀ {sigma T : ℝ}, 1 / 2 < sigma → 5 ≤ T →
        ∃ r ∈ Set.Icc (121 / 32 : ℝ) (122 / 32 : ℝ),
        ∃ t ∈ Set.Icc T (T + 1),
          (∀ x ∈ Set.Icc sigma 4,
            regularizedTwoScaleCarlsonZeroDetector Y0 Y1
              ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
          ∀ x ∈ Set.Icc sigma 4,
            ‖logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
              ((x : ℂ) + (t : ℂ) * I)‖ ≤
              4 * max
                  (regularizedTwoScaleCarlsonFactorCircleLogUpper C Y0 Y1 T -
                    regularizedTwoScaleCarlsonFactorCenterLogLower Y0 Y1 T) 1 *
                (r + 15 / 4) / (r - 15 / 4) ^ 2 +
              regularizedTwoScaleCarlsonInnerFactorDiskZeroMass Y0 Y1 T /
                regularizedTwoScaleCarlsonFactorHorizontalSeparation Y0 Y1 T :=
  exists_regularizedTwoScaleCarlson_horizontal_logDeriv_le_factorDisk

example :
    ∃ C₁ C₂ : ℝ, 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {Y0 Y1 : ℕ}, 2 ≤ Y0 → Y0 < Y1 →
      ∀ {sigma T : ℝ}, 1 / 2 < sigma → 5 ≤ T →
        ∃ r ∈ Set.Icc (121 / 32 : ℝ) (122 / 32 : ℝ),
        ∃ t ∈ Set.Icc T (T + 1),
          (∀ x ∈ Set.Icc sigma 4,
            regularizedTwoScaleCarlsonZeroDetector Y0 Y1
              ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
          ∀ x ∈ Set.Icc sigma 4,
            ‖logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
              ((x : ℂ) + (t : ℂ) * I)‖ ≤
              4 * max
                  (regularizedTwoScaleCarlsonFactorLogVariationMajorant
                    C₁ Y0 Y1 T
                    (regularizedTwoScaleCarlsonFactorZeroLogMajorant
                      C₂ Y0 Y1 T)) 1 *
                (r + 15 / 4) / (r - 15 / 4) ^ 2 +
              regularizedTwoScaleCarlsonFactorZeroLogMajorant C₂ Y0 Y1 T /
                (1 / (4 *
                  (regularizedTwoScaleCarlsonFactorZeroLogMajorant
                    C₂ Y0 Y1 T + 1))) :=
  exists_regularizedTwoScaleCarlson_horizontal_logDeriv_le_logPolynomial

end CarlsonZeroDensity
end PrimeNumberTheorem
