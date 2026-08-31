import HardyTheorem.AFEWeightedPoissonVelocityBounds

/-!
# Reciprocal-power bounds from a Poisson velocity gap
-/

noncomputable section

namespace HardyTheorem
namespace AFE

theorem abs_div_pow_le_div_gap_pow
    (c v g : ℝ) (n : ℕ) (hg : 0 < g) (hgv : g ≤ |v|) :
    |c / v ^ n| ≤ |c| / g ^ n := by
  rw [abs_div, abs_pow]
  exact div_le_div_of_nonneg_left (abs_nonneg c) (pow_pos hg n)
    (pow_le_pow_left₀ hg.le hgv n)

theorem abs_weightedPoissonVelocityDeriv
    {t u : ℝ} (ht : 0 ≤ t) (_hu : 0 < u) :
    |weightedPoissonVelocityDeriv t u| = t / u ^ 2 := by
  rw [weightedPoissonVelocityDeriv,
    abs_of_nonneg (div_nonneg ht (sq_nonneg u))]

theorem abs_weightedPoissonVelocitySecondDeriv
    {t u : ℝ} (ht : 0 ≤ t) (hu : 0 < u) :
    |weightedPoissonVelocitySecondDeriv t u| = 2 * t / u ^ 3 := by
  have hden : 0 < u ^ 3 := pow_pos hu 3
  have hnonpos : -2 * t / u ^ 3 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by nlinarith [ht]) hden.le
  rw [weightedPoissonVelocitySecondDeriv, abs_of_nonpos hnonpos]
  ring

end AFE
end HardyTheorem
