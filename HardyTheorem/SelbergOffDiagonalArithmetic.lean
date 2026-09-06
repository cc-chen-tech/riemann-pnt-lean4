import HardyTheorem.SelbergSArithmeticHarmonic

open scoped BigOperators

namespace HardyTheorem

/-!
# The arithmetic core of Selberg's off-diagonal estimate

The difference of two rational squares retains an integer gap.  Once a
possible first residue is separated, the positive gaps in a fixed residue
class have step `d`; their reciprocal tail is at most `d⁻¹ H_M`.
-/

/-- The exact rational-square gap used in Titchmarsh 10.16. -/
theorem selberg_difference_of_squares_gap_le
    {A B L V : ℝ} (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL : 0 < L) (hV : 0 < V) (hgap : B * L ≤ A * V) :
    A * (A * V - B * L) / (L ^ 2 * V) ≤
      A ^ 2 / L ^ 2 - B ^ 2 / V ^ 2 := by
  have hdiff : 0 ≤ A * V - B * L := sub_nonneg.mpr hgap
  have hterm : 0 ≤
      B * L * (A * V - B * L) / (L ^ 2 * V ^ 2) := by
    positivity
  have hid :
      (A ^ 2 / L ^ 2 - B ^ 2 / V ^ 2) -
          A * (A * V - B * L) / (L ^ 2 * V) =
        B * L * (A * V - B * L) / (L ^ 2 * V ^ 2) := by
    field_simp [hL.ne', hV.ne']
    ring
  linarith

/-- After the first positive member of a residue class, reciprocal gaps of
step `d` are bounded by `d⁻¹` times the ordinary harmonic sum. -/
theorem selberg_arithmetic_progression_reciprocal_tail_le
    {r d : ℕ} (_hr : 1 ≤ r) (hd : 1 ≤ d) (M : ℕ) :
    (∑ j ∈ Finset.Icc 1 M, ((r + j * d : ℕ) : ℝ)⁻¹) ≤
      (d : ℝ)⁻¹ * (1 + Real.log (M : ℝ)) := by
  calc
    (∑ j ∈ Finset.Icc 1 M, ((r + j * d : ℕ) : ℝ)⁻¹) ≤
        ∑ j ∈ Finset.Icc 1 M, ((j * d : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjd0 : 0 < ((j * d : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos hj1 hd
      have hden : (((j * d : ℕ) : ℝ)) ≤
          (((r + j * d : ℕ) : ℝ)) := by
        exact_mod_cast Nat.le_add_left (j * d) r
      simpa only [one_div] using one_div_le_one_div_of_le hjd0 hden
    _ = (d : ℝ)⁻¹ *
        ∑ j ∈ Finset.Icc 1 M, (j : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      push_cast
      rw [mul_inv]
      ring
    _ ≤ (d : ℝ)⁻¹ * (1 + Real.log (M : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (selberg_sum_Icc_inv_le_one_add_log M)
        (inv_nonneg.mpr (Nat.cast_nonneg d))

end HardyTheorem
