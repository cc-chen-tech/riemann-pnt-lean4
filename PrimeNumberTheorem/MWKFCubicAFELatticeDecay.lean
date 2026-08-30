import PrimeNumberTheorem.MWKFCubicAFEPhysicalDecay

open Set

namespace PrimeNumberTheorem.MWKFCubic

/-!
# A translation-uniform half-line lattice bound

The integer shift is reindexed exactly at floor(s/2-b). The bound is
independent of the real translation b; it does retain its explicit modulus
dependence. This is a convergence bound, not a cubic cancellation estimate.
-/

theorem cubicAFELatticePower_nonneg (X s b : ℝ) (δ : ℤ) :
    0 ≤ cubicAFEDyadicLowerWeight (((δ : ℝ) + b) / s) *
      (((δ : ℝ) + b) / s) ^ (-X - 1 / 2) := by
  by_cases h : ((δ : ℝ) + b) / s ≤ 1 / 2
  · rw [cubicAFEDyadicLowerWeight_zero h, zero_mul]
  · exact mul_nonneg (cubicAFEDyadicLowerWeight_nonneg _)
      (Real.rpow_nonneg (by linarith [lt_of_not_ge h]) _)

private theorem latticePower_le_shifted
    {X s : ℝ} (hX : 1 / 2 < X) (hs : 1 ≤ s) (b : ℝ) (δ : ℤ) :
    cubicAFEDyadicLowerWeight (((δ : ℝ) + b) / s) *
        (((δ : ℝ) + b) / s) ^ (-X - 1 / 2) ≤
      (1 / (2 * s)) ^ (-X - 1 / 2) *
        |((δ - ⌊s / 2 - b⌋ : ℤ) : ℝ)| ^ (-X - 1 / 2) := by
  have hspos : 0 < s := by linarith
  have hbase : 0 < 1 / (2 * s) := by positivity
  by_cases hδ : δ ≤ ⌊s / 2 - b⌋
  · have hy : ((δ : ℝ) + b) / s ≤ 1 / 2 := by
      apply (div_le_iff₀ hspos).mpr
      have hd : (δ : ℝ) ≤ (⌊s / 2 - b⌋ : ℤ) := by exact_mod_cast hδ
      linarith [Int.floor_le (s / 2 - b)]
    rw [cubicAFEDyadicLowerWeight_zero hy, zero_mul]
    exact mul_nonneg (Real.rpow_nonneg hbase.le _) (Real.rpow_nonneg (abs_nonneg _) _)
  · have hn : (1 : ℝ) ≤ ((δ - ⌊s / 2 - b⌋ : ℤ) : ℝ) := by
      exact_mod_cast (show (1 : ℤ) ≤ δ - ⌊s / 2 - b⌋ by omega)
    have hlower : (1 / (2 * s)) * ((δ - ⌊s / 2 - b⌋ : ℤ) : ℝ) ≤
        ((δ : ℝ) + b) / s := by
      rw [one_div, inv_mul_eq_div, div_le_div_iff₀ (by positivity : 0 < 2 * s) hspos]
      have hh := Int.lt_floor_add_one (s / 2 - b)
      push_cast at hn ⊢
      nlinarith
    have hypos : 0 < ((δ : ℝ) + b) / s :=
      lt_of_lt_of_le (mul_pos hbase (by linarith)) hlower
    calc
      _ ≤ (((δ : ℝ) + b) / s) ^ (-X - 1 / 2) :=
        mul_le_of_le_one_left (Real.rpow_nonneg hypos.le _)
          (cubicAFEDyadicLowerWeight_le_one _)
      _ ≤ ((1 / (2 * s)) * ((δ - ⌊s / 2 - b⌋ : ℤ) : ℝ)) ^ (-X - 1 / 2) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hbase (by linarith)) hlower (by linarith)
      _ = _ := by
        rw [Real.mul_rpow hbase.le (by linarith), abs_of_nonneg (by linarith)]

private theorem summable_shifted_majorant
    {X s : ℝ} (hX : 1 / 2 < X) (b : ℝ) :
    Summable (fun δ : ℤ ↦ (1 / (2 * s)) ^ (-X - 1 / 2) *
      |((δ - ⌊s / 2 - b⌋ : ℤ) : ℝ)| ^ (-X - 1 / 2)) := by
  have hbase : Summable (fun n : ℤ ↦ |(n : ℝ)| ^ (-X - 1 / 2)) := by
    simpa only [neg_add, sub_eq_add_neg] using
      Real.summable_abs_int_rpow (by linarith : 1 < X + 1 / 2)
  have hinj : Function.Injective (fun δ : ℤ ↦ δ - ⌊s / 2 - b⌋) := by
    intro i j h
    dsimp only at h
    omega
  exact (hbase.mul_left _).comp_injective hinj

theorem summable_cubicAFELatticePower
    {X s : ℝ} (hX : 1 / 2 < X) (hs : 1 ≤ s) (b : ℝ) :
    Summable (fun δ : ℤ ↦ cubicAFEDyadicLowerWeight (((δ : ℝ) + b) / s) *
      (((δ : ℝ) + b) / s) ^ (-X - 1 / 2)) :=
  Summable.of_nonneg_of_le (cubicAFELatticePower_nonneg X s b)
    (latticePower_le_shifted hX hs b) (summable_shifted_majorant hX b)

theorem tsum_cubicAFELatticePower_le
    {X s : ℝ} (hX : 1 / 2 < X) (hs : 1 ≤ s) (b : ℝ) :
    (∑' δ : ℤ, cubicAFEDyadicLowerWeight (((δ : ℝ) + b) / s) *
        (((δ : ℝ) + b) / s) ^ (-X - 1 / 2)) ≤
      (1 / (2 * s)) ^ (-X - 1 / 2) * ∑' n : ℤ, |(n : ℝ)| ^ (-X - 1 / 2) := by
  let e : ℤ ≃ ℤ :=
    { toFun := fun δ ↦ δ - ⌊s / 2 - b⌋
      invFun := fun n ↦ n + ⌊s / 2 - b⌋
      left_inv := fun δ ↦ sub_add_cancel _ _
      right_inv := fun n ↦ add_sub_cancel_right _ _ }
  calc
    _ ≤ ∑' δ : ℤ, (1 / (2 * s)) ^ (-X - 1 / 2) *
        |((δ - ⌊s / 2 - b⌋ : ℤ) : ℝ)| ^ (-X - 1 / 2) :=
      Summable.tsum_le_tsum (latticePower_le_shifted hX hs b)
        (summable_cubicAFELatticePower hX hs b) (summable_shifted_majorant hX b)
    _ = ∑' n : ℤ, (1 / (2 * s)) ^ (-X - 1 / 2) * |(n : ℝ)| ^ (-X - 1 / 2) :=
      e.tsum_eq (fun n : ℤ ↦ (1 / (2 * s)) ^ (-X - 1 / 2) * |(n : ℝ)| ^ (-X - 1 / 2))
    _ = _ := tsum_mul_left

end PrimeNumberTheorem.MWKFCubic
