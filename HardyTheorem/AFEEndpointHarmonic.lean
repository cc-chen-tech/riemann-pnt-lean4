import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Shifted harmonic sums at a Poisson endpoint

After the single integer nearest an endpoint frequency is isolated, the
remaining reciprocal derivative gaps are bounded by an ordinary harmonic
sum.  These elementary estimates are the discrete bookkeeping behind the
logarithm in Titchmarsh's weighted Poisson transformation.
-/

noncomputable section

open scoped BigOperators

namespace HardyTheorem
namespace AFE

/-- Frequencies below `floor beta` have reciprocal gaps bounded by an
ordinary harmonic sum once the nearest frequency is removed. -/
theorem sum_reciprocal_below_floor_le_harmonic
    (beta : ℝ) (hbeta : 0 ≤ beta) (M : ℕ) :
    (∑ j ∈ Finset.Icc 1 M,
      (beta - ((Nat.floor beta : ℝ) - (j : ℝ)))⁻¹) ≤
        (harmonic M : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_le_sum
  intro j hj
  have hj_one : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hj_pos : 0 < (j : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hj_one)
  have hfloor : (Nat.floor beta : ℝ) ≤ beta := Nat.floor_le hbeta
  have hden : (j : ℝ) ≤
      beta - ((Nat.floor beta : ℝ) - (j : ℝ)) := by
    linarith
  have hden_pos : 0 < beta - ((Nat.floor beta : ℝ) - (j : ℝ)) :=
    hj_pos.trans_le hden
  exact (inv_le_inv₀ hden_pos hj_pos).2 hden

/-- Frequencies above `floor beta + 1` have reciprocal gaps bounded by an
ordinary harmonic sum once the nearest frequency is removed. -/
theorem sum_reciprocal_above_floor_le_harmonic
    (beta : ℝ) (_hbeta : 0 ≤ beta) (M : ℕ) :
    (∑ j ∈ Finset.Icc 1 M,
      (((Nat.floor beta : ℝ) + 1 + (j : ℝ)) - beta)⁻¹) ≤
        (harmonic M : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_le_sum
  intro j hj
  have hj_one : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hj_pos : 0 < (j : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hj_one)
  have hfloor_succ : beta < (Nat.floor beta : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one beta
  have hden : (j : ℝ) ≤
      ((Nat.floor beta : ℝ) + 1 + (j : ℝ)) - beta := by
    linarith
  have hden_pos : 0 <
      ((Nat.floor beta : ℝ) + 1 + (j : ℝ)) - beta :=
    hj_pos.trans_le hden
  exact (inv_le_inv₀ hden_pos hj_pos).2 hden

theorem sum_reciprocal_below_floor_le_one_add_log
    (beta : ℝ) (hbeta : 0 ≤ beta) (M : ℕ) :
    (∑ j ∈ Finset.Icc 1 M,
      (beta - ((Nat.floor beta : ℝ) - (j : ℝ)))⁻¹) ≤
        1 + Real.log M :=
  (sum_reciprocal_below_floor_le_harmonic beta hbeta M).trans
    (harmonic_le_one_add_log M)

theorem sum_reciprocal_above_floor_le_one_add_log
    (beta : ℝ) (hbeta : 0 ≤ beta) (M : ℕ) :
    (∑ j ∈ Finset.Icc 1 M,
      (((Nat.floor beta : ℝ) + 1 + (j : ℝ)) - beta)⁻¹) ≤
        1 + Real.log M :=
  (sum_reciprocal_above_floor_le_harmonic beta hbeta M).trans
    (harmonic_le_one_add_log M)

end AFE
end HardyTheorem
