import HardyTheorem.AFEExplicitPoissonRemainderBound
import HardyTheorem.AFEWeightedPoissonReciprocalBounds

/-!
# The explicit Poisson remainder under a uniform phase gap
-/

noncomputable section

namespace HardyTheorem
namespace AFE

theorem norm_explicitPoissonSecondQuotientDerivative_le_gapMajorant
    {C₁ C₂ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂)
    (sigma x N t g : ℝ) (k : ℤ) {u : ℝ}
    (ht : 0 ≤ t) (hu : 0 < u) (hg : 0 < g)
    (hgap : g ≤ |weightedPoissonVelocity t k u|) :
    ‖explicitPoissonSecondQuotientDerivative sigma x N t k u‖ ≤
      (1 / g ^ 2) *
        ((2 * C₂ + 2 * C₁ ^ 2) * u ^ (-sigma) +
          4 * C₁ * |sigma| * u ^ (-sigma - 1) +
          |sigma| * |sigma + 1| * u ^ (-sigma - 2)) +
      (3 * (t / u ^ 2) / g ^ 3) *
        (2 * C₁ * u ^ (-sigma) + |sigma| * u ^ (-sigma - 1)) +
      ((2 * t / u ^ 3) / g ^ 3) * u ^ (-sigma) +
      (3 * (t / u ^ 2) ^ 2 / g ^ 4) * u ^ (-sigma) := by
  have hv0 : weightedPoissonVelocity t k u ≠ 0 := by
    apply abs_pos.mp
    exact hg.trans_le hgap
  have hbase := norm_explicitPoissonSecondQuotientDerivative_le_majorant
    hC₁0 hC₂0 hC₁ hC₂ sigma x N t k hu hv0
  have hcoef₁ :
      |1 / (weightedPoissonVelocity t k u) ^ 2| ≤ 1 / g ^ 2 := by
    simpa only [abs_one] using
      (abs_div_pow_le_div_gap_pow 1 (weightedPoissonVelocity t k u) g 2 hg hgap)
  have hcoef₂ :
      |3 * weightedPoissonVelocityDeriv t u /
          (weightedPoissonVelocity t k u) ^ 3| ≤
        3 * (t / u ^ 2) / g ^ 3 := by
    have h := abs_div_pow_le_div_gap_pow
      (3 * weightedPoissonVelocityDeriv t u)
      (weightedPoissonVelocity t k u) g 3 hg hgap
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
      abs_weightedPoissonVelocityDeriv ht hu] at h
    exact h
  have hcoef₃ :
      |weightedPoissonVelocitySecondDeriv t u /
          (weightedPoissonVelocity t k u) ^ 3| ≤
        (2 * t / u ^ 3) / g ^ 3 := by
    have h := abs_div_pow_le_div_gap_pow
      (weightedPoissonVelocitySecondDeriv t u)
      (weightedPoissonVelocity t k u) g 3 hg hgap
    rw [abs_weightedPoissonVelocitySecondDeriv ht hu] at h
    exact h
  have hcoef₄ :
      |3 * (weightedPoissonVelocityDeriv t u) ^ 2 /
          (weightedPoissonVelocity t k u) ^ 4| ≤
        3 * (t / u ^ 2) ^ 2 / g ^ 4 := by
    have h := abs_div_pow_le_div_gap_pow
      (3 * (weightedPoissonVelocityDeriv t u) ^ 2)
      (weightedPoissonVelocity t k u) g 4 hg hgap
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_pow,
      abs_weightedPoissonVelocityDeriv ht hu] at h
    exact h
  refine hbase.trans ?_
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · exact mul_le_mul_of_nonneg_right hcoef₁ (by positivity)
      · exact mul_le_mul_of_nonneg_right hcoef₂ (by positivity)
    · exact mul_le_mul_of_nonneg_right hcoef₃
        (Real.rpow_nonneg hu.le _)
  · exact mul_le_mul_of_nonneg_right hcoef₄
      (Real.rpow_nonneg hu.le _)

end AFE
end HardyTheorem
