import ZeroFreeRegion.VinogradovKorobov.VinogradovLargeValues

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- A complete polynomial Weyl sum over `{1, ..., X}` has norm at most `X`. -/
theorem norm_vinogradovWeylSumMod_le
    (Q k X : ℕ) [NeZero Q] (a : Fin k → ZMod Q) :
    ‖vinogradovWeylSumMod Q k X a‖ ≤ X := by
  unfold vinogradovWeylSumMod
  calc
    ‖∑ n : Fin X, ZMod.stdAddChar (vinogradovPhaseMod Q a n)‖ ≤
        ∑ n : Fin X, ‖ZMod.stdAddChar (vinogradovPhaseMod Q a n)‖ :=
      norm_sum_le _ _
    _ = X := by simp

/-- Increasing the moment from `2s` to `2(s+r)` costs at most the trivial
factor `X^(2r)`. -/
theorem sum_norm_vinogradovWeylSumMod_pow_add_le
    (Q k s r X : ℕ) [NeZero Q] :
    (∑ a : Fin k → ZMod Q,
        ‖vinogradovWeylSumMod Q k X a‖ ^ (2 * (s + r))) ≤
      (X : ℝ) ^ (2 * r) *
        ∑ a : Fin k → ZMod Q,
          ‖vinogradovWeylSumMod Q k X a‖ ^ (2 * s) := by
  calc
    (∑ a : Fin k → ZMod Q,
        ‖vinogradovWeylSumMod Q k X a‖ ^ (2 * (s + r))) =
        ∑ a : Fin k → ZMod Q,
          ‖vinogradovWeylSumMod Q k X a‖ ^ (2 * s) *
            ‖vinogradovWeylSumMod Q k X a‖ ^ (2 * r) := by
      apply Fintype.sum_congr
      intro a
      rw [show 2 * (s + r) = 2 * s + 2 * r by omega, pow_add]
    _ ≤ ∑ a : Fin k → ZMod Q,
          ‖vinogradovWeylSumMod Q k X a‖ ^ (2 * s) *
            (X : ℝ) ^ (2 * r) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _)
          (norm_vinogradovWeylSumMod_le Q k X a) (2 * r))
        (pow_nonneg (norm_nonneg _) _)
    _ = (X : ℝ) ^ (2 * r) *
          ∑ a : Fin k → ZMod Q,
            ‖vinogradovWeylSumMod Q k X a‖ ^ (2 * s) := by
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro a
      ring

/-- The modular Vinogradov solution counts inherit the same moment
monotonicity. -/
theorem vinogradovSolutionCountMod_add_le
    (Q k s r X : ℕ) [NeZero Q] :
    vinogradovSolutionCountMod Q k (s + r) X ≤
      X ^ (2 * r) * vinogradovSolutionCountMod Q k s X := by
  have hmom := sum_norm_vinogradovWeylSumMod_pow_add_le Q k s r X
  rw [sum_norm_vinogradovWeylSumMod_pow_two_mul_eq Q k (s + r) X,
    sum_norm_vinogradovWeylSumMod_pow_two_mul_eq Q k s X] at hmom
  have hQpos : 0 < (Q : ℝ) ^ k := by
    exact pow_pos (Nat.cast_pos.mpr (NeZero.pos Q)) k
  have hreal :
      (vinogradovSolutionCountMod Q k (s + r) X : ℝ) ≤
        (X : ℝ) ^ (2 * r) *
          vinogradovSolutionCountMod Q k s X := by
    apply le_of_mul_le_mul_left _ hQpos
    calc
      (Q : ℝ) ^ k * vinogradovSolutionCountMod Q k (s + r) X ≤
          (X : ℝ) ^ (2 * r) *
            ((Q : ℝ) ^ k * vinogradovSolutionCountMod Q k s X) := hmom
      _ = (Q : ℝ) ^ k *
          ((X : ℝ) ^ (2 * r) *
            vinogradovSolutionCountMod Q k s X) := by ring
  exact_mod_cast hreal

/-- For positive `X`, ordinary integer Vinogradov mean values satisfy
`J_(s+r) ≤ X^(2r) J_s`.  A sufficiently large finite modulus transfers the
modular moment inequality without wraparound. -/
theorem vinogradovSolutionCountNat_add_le
    (k s r X : ℕ) (hX : 1 ≤ X) :
    vinogradovSolutionCountNat k (s + r) X ≤
      X ^ (2 * r) * vinogradovSolutionCountNat k s X := by
  let Q := (s + r) * X ^ k + 1
  letI : NeZero Q := ⟨by simp [Q]⟩
  have htop : (s + r) * X ^ k < Q := by
    simp [Q]
  have hbase : s * X ^ k < Q := by
    have hsr : s * X ^ k ≤ (s + r) * X ^ k := by
      exact Nat.mul_le_mul_right (X ^ k) (Nat.le_add_right s r)
    omega
  have h := vinogradovSolutionCountMod_add_le Q k s r X
  rw [vinogradovSolutionCountMod_eq_nat_of_topScale Q k (s + r) X hX htop,
    vinogradovSolutionCountMod_eq_nat_of_topScale Q k s X hX hbase] at h
  exact h

end

end ZeroFreeRegion.VinogradovKorobov
