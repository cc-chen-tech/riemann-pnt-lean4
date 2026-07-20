import PrimeNumberTheorem.CarlsonDetectorGrowth

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {T : ℝ} (hT : 5 ≤ T) {z : ℂ}
    (hz : z ∈ Metric.sphere
      ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ)) :
    z.re ∈ Set.Icc (0 : ℝ) 8 :=
  fixedJensenSphere_re_mem_Icc hT hz

example {T : ℝ} (hT : 5 ≤ T) {z : ℂ}
    (hz : z ∈ Metric.sphere
      ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ)) :
    |z.im| ∈ Set.Icc (1 : ℝ) (T + 5) :=
  fixedJensenSphere_abs_im_mem_Icc hT hz

example {T : ℝ} (hT : 5 ≤ T) {z : ℂ}
    (hz : z ∈ Metric.sphere
      ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ)) :
    ‖z - 1‖ ≤ T + 14 :=
  norm_sub_one_le_on_fixedJensenSphere hT hz

example : ∃ C : ℝ, 2 ≤ C ∧ ∀ {T : ℝ}, 5 ≤ T → ∀ {z : ℂ},
    z ∈ Metric.sphere
      ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ) →
    ‖riemannZeta z‖ ≤ C * (T + 14) ^ 4 :=
  exists_norm_riemannZeta_le_fixedJensenSphere

example : ∃ C : ℝ, 1 ≤ C ∧ ∀ {X : ℕ}, 1 ≤ X → ∀ {T : ℝ}, 5 ≤ T →
    ∀ {z : ℂ}, z ∈ Metric.sphere
      ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ) →
    ‖regularizedCarlsonZeroDetector X z‖ ≤
      C * (X : ℝ) ^ 2 * (T + 14) ^ 10 :=
  exists_norm_regularizedCarlsonZeroDetector_le_fixedJensenSphere

example : ∃ C : ℝ, 1 ≤ C ∧ ∀ {X : ℕ}, 1 ≤ X → ∀ {sigma T : ℝ},
    1 / 2 < sigma → 5 ≤ T →
    (regularizedCarlsonDetectorRectangleZeroCount
        X sigma 4 T (T + 1) : ℝ) ≤
      Real.log (C * (X : ℝ) ^ 2 * (T + 14) ^ 10) /
        Real.log ((31 / 8 : ℝ) / (15 / 4 : ℝ)) :=
  exists_regularizedCarlsonDetectorRectangleZeroCount_le_logPolynomial

noncomputable example (C : ℝ) (X : ℕ) (T : ℝ) : ℝ :=
  regularizedCarlsonLocalZeroLogMajorant C X T

example : ∃ C : ℝ, 1 ≤ C ∧ ∀ {X : ℕ}, 1 ≤ X → ∀ {sigma T : ℝ},
    1 / 2 < sigma → 5 ≤ T →
    ∃ t ∈ Set.Icc T (T + 1),
      (∀ x ∈ Set.Icc sigma 4,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
      ∀ x ∈ Set.Icc sigma 4,
        ‖regularizedCarlsonDetectorRectanglePrincipalPart
          X sigma 4 T (T + 1) ((x : ℂ) + (t : ℂ) * I)‖ ≤
          regularizedCarlsonLocalZeroLogMajorant C X T /
            (1 / ((4 : ℝ) *
              (regularizedCarlsonLocalZeroLogMajorant C X T + 1))) :=
  exists_regularizedCarlson_horizontal_principalPart_le_logPolynomial

example : ∃ C : ℝ, 1 ≤ C ∧ ∀ {X : ℕ}, 1 ≤ X → ∀ {sigma T M : ℝ},
    1 / 2 < sigma → 5 ≤ T →
    (∀ t ∈ Set.Icc T (T + 1), ∀ x ∈ Set.Icc sigma 4,
      ‖regularizedCarlsonDetectorRectangleRegularPart
        X sigma 4 T (T + 1) ((x : ℂ) + (t : ℂ) * I)‖ ≤ M) →
    ∃ t ∈ Set.Icc T (T + 1),
      (∀ x ∈ Set.Icc sigma 4,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
      ∀ x ∈ Set.Icc sigma 4,
        ‖logDeriv (regularizedCarlsonZeroDetector X)
          ((x : ℂ) + (t : ℂ) * I)‖ ≤
          M + regularizedCarlsonLocalZeroLogMajorant C X T /
            (1 / ((4 : ℝ) *
              (regularizedCarlsonLocalZeroLogMajorant C X T + 1))) :=
  exists_regularizedCarlson_horizontal_logDeriv_le_regular_add_logPolynomial

example {X : ℕ} (hX : 1 ≤ X) {T : ℝ} :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g
        (Metric.closedBall ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) ∧
      (∀ u : (Metric.closedBall
          ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ) : Set ℂ),
        g u ≠ 0) ∧
      -Real.log (123 / 32 : ℝ) *
          (∑ᶠ u,
            (MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
              (Metric.closedBall
                ((4 : ℂ) + I * (T + 1 / 2)) (123 / 32 : ℝ)) u : ℝ)) ≤
        Real.log ‖g ((4 : ℂ) + I * (T + 1 / 2))‖ :=
  exists_regularizedCarlsonZeroDetector_fixedJensenFactor_center_lower hX

#print axioms fixedJensenSphere_re_mem_Icc
#print axioms fixedJensenSphere_abs_im_mem_Icc
#print axioms norm_sub_one_le_on_fixedJensenSphere
#print axioms exists_norm_riemannZeta_le_fixedJensenSphere
#print axioms exists_norm_regularizedCarlsonZeroDetector_le_fixedJensenSphere
#print axioms exists_regularizedCarlsonDetectorRectangleZeroCount_le_logPolynomial
#print axioms exists_regularizedCarlson_horizontal_principalPart_le_logPolynomial
#print axioms exists_regularizedCarlson_horizontal_logDeriv_le_regular_add_logPolynomial
#print axioms exists_regularizedCarlsonZeroDetector_fixedJensenFactor_center_lower

end CarlsonZeroDensity
end PrimeNumberTheorem
