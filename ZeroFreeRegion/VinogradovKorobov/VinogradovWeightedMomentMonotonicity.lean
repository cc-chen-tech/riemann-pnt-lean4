import ZeroFreeRegion.VinogradovKorobov.VinogradovWeightedLargeValues

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Increasing the weighted moment from `2s` to `2(s+r)` costs at most the
trivial factor `X^(2r)`. -/
theorem sum_norm_vinogradovWeightedWeylSum_pow_add_le
    (p a k s r X : ℕ) [Fact p.Prime] :
    (∑ c : VinogradovWeightedCoefficient p a k,
        ‖vinogradovWeightedWeylSum p a k X c‖ ^ (2 * (s + r))) ≤
      (X : ℝ) ^ (2 * r) *
        ∑ c : VinogradovWeightedCoefficient p a k,
          ‖vinogradovWeightedWeylSum p a k X c‖ ^ (2 * s) := by
  calc
    (∑ c : VinogradovWeightedCoefficient p a k,
        ‖vinogradovWeightedWeylSum p a k X c‖ ^ (2 * (s + r))) =
      ∑ c : VinogradovWeightedCoefficient p a k,
        ‖vinogradovWeightedWeylSum p a k X c‖ ^ (2 * s) *
          ‖vinogradovWeightedWeylSum p a k X c‖ ^ (2 * r) := by
      apply Fintype.sum_congr
      intro c
      rw [show 2 * (s + r) = 2 * s + 2 * r by omega, pow_add]
    _ ≤ ∑ c : VinogradovWeightedCoefficient p a k,
        ‖vinogradovWeightedWeylSum p a k X c‖ ^ (2 * s) *
          (X : ℝ) ^ (2 * r) := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _)
          (norm_vinogradovWeightedWeylSum_le p a k X c) (2 * r))
        (pow_nonneg (norm_nonneg _) _)
    _ = (X : ℝ) ^ (2 * r) *
        ∑ c : VinogradovWeightedCoefficient p a k,
          ‖vinogradovWeightedWeylSum p a k X c‖ ^ (2 * s) := by
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro c
      ring

/-- Weighted modular Vinogradov solution counts inherit the same moment-order
monotonicity. -/
theorem vinogradovWeightedSolutionCountMod_add_le
    (p a k s r X : ℕ) [Fact p.Prime] :
    vinogradovWeightedSolutionCountMod p a k (s + r) X ≤
      X ^ (2 * r) * vinogradovWeightedSolutionCountMod p a k s X := by
  have hmom :=
    sum_norm_vinogradovWeightedWeylSum_pow_add_le p a k s r X
  rw [sum_norm_vinogradovWeightedWeylSum_pow_two_mul_eq
      p a k (s + r) X,
    sum_norm_vinogradovWeightedWeylSum_pow_two_mul_eq
      p a k s X] at hmom
  have hP : 0 < (p : ℝ) ^ (a * (k * (k + 1) / 2)) := by
    exact pow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) _
  have hreal :
      (vinogradovWeightedSolutionCountMod p a k (s + r) X : ℝ) ≤
        (X : ℝ) ^ (2 * r) *
          vinogradovWeightedSolutionCountMod p a k s X := by
    apply le_of_mul_le_mul_left _ hP
    calc
      (p : ℝ) ^ (a * (k * (k + 1) / 2)) *
          vinogradovWeightedSolutionCountMod p a k (s + r) X ≤
        (X : ℝ) ^ (2 * r) *
          ((p : ℝ) ^ (a * (k * (k + 1) / 2)) *
            vinogradovWeightedSolutionCountMod p a k s X) := hmom
      _ = (p : ℝ) ^ (a * (k * (k + 1) / 2)) *
          ((X : ℝ) ^ (2 * r) *
            vinogradovWeightedSolutionCountMod p a k s X) := by ring
  exact_mod_cast hreal

end

end ZeroFreeRegion.VinogradovKorobov
