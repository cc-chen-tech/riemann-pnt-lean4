import ZeroFreeRegion.VinogradovKorobov.VinogradovDiagonal

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

open scoped BigOperators

/-- The integer power sum used by the translation-dilation invariant form of
the Vinogradov system. -/
def vinogradovPowerSumInt {k s : ℕ} (x : Fin s → ℤ) (j : Fin k) : ℤ :=
  ∑ i, x i ^ (j.val + 1)

/-- The unrestricted integer Vinogradov system. -/
def IsVinogradovSolutionInt (k s : ℕ) (x y : Fin s → ℤ) : Prop :=
  ∀ j : Fin k, vinogradovPowerSumInt x j = vinogradovPowerSumInt y j

private theorem IsVinogradovSolutionInt.powerSum_eq {k s : ℕ}
    {x y : Fin s → ℤ} (h : IsVinogradovSolutionInt k s x y)
    {m : ℕ} (hm : m ≤ k) :
    (∑ i, x i ^ m) = ∑ i, y i ^ m := by
  by_cases hm0 : m = 0
  · subst m
    simp
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hlt : m - 1 < k := by omega
    have hp := h (⟨m - 1, hlt⟩ : Fin k)
    change (∑ i, x i ^ (m - 1 + 1)) =
      ∑ i, y i ^ (m - 1 + 1) at hp
    simpa only [Nat.sub_add_cancel hmpos] using hp

/-- Translation of every coordinate preserves the integer Vinogradov
system. -/
theorem IsVinogradovSolutionInt.translate {k s : ℕ} {x y : Fin s → ℤ}
    (h : IsVinogradovSolutionInt k s x y) (c : ℤ) :
    IsVinogradovSolutionInt k s (fun i => x i + c) (fun i => y i + c) := by
  intro j
  unfold vinogradovPowerSumInt
  simp_rw [add_pow]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_range] at hm
  have hmk : m ≤ k := by omega
  calc
    (∑ i, x i ^ m * c ^ (j.val + 1 - m) * (j.val + 1).choose m) =
        (∑ i, x i ^ m) *
          (c ^ (j.val + 1 - m) * (j.val + 1).choose m) := by
      rw [Finset.sum_mul]
      simp only [mul_assoc]
    _ = (∑ i, y i ^ m) *
          (c ^ (j.val + 1 - m) * (j.val + 1).choose m) := by
      rw [h.powerSum_eq hmk]
    _ = ∑ i, y i ^ m * c ^ (j.val + 1 - m) *
          (j.val + 1).choose m := by
      rw [Finset.sum_mul]
      simp only [mul_assoc]

/-- Multiplication of every coordinate by a fixed integer preserves the
integer Vinogradov system. -/
theorem IsVinogradovSolutionInt.scale {k s : ℕ} {x y : Fin s → ℤ}
    (h : IsVinogradovSolutionInt k s x y) (d : ℤ) :
    IsVinogradovSolutionInt k s (fun i => d * x i) (fun i => d * y i) := by
  intro j
  unfold vinogradovPowerSumInt
  simp_rw [mul_pow, ← Finset.mul_sum]
  rw [h.powerSum_eq (Nat.succ_le_of_lt j.isLt)]

/-- Translation is an equivalence on the integer Vinogradov system. -/
theorem isVinogradovSolutionInt_translate_iff {k s : ℕ}
    (x y : Fin s → ℤ) (c : ℤ) :
    IsVinogradovSolutionInt k s (fun i => x i + c) (fun i => y i + c) ↔
      IsVinogradovSolutionInt k s x y := by
  constructor
  · intro h
    have hback := h.translate (-c)
    simpa only [add_neg_cancel_right] using hback
  · intro h
    exact h.translate c

/-- A nonzero integer dilation is an equivalence on the integer Vinogradov
system. -/
theorem isVinogradovSolutionInt_scale_iff {k s : ℕ}
    (x y : Fin s → ℤ) {d : ℤ} (hd : d ≠ 0) :
    IsVinogradovSolutionInt k s (fun i => d * x i) (fun i => d * y i) ↔
      IsVinogradovSolutionInt k s x y := by
  constructor
  · intro h j
    have hp := h j
    unfold vinogradovPowerSumInt at hp ⊢
    simp_rw [mul_pow, ← Finset.mul_sum] at hp
    exact mul_left_cancel₀ (pow_ne_zero (j.val + 1) hd) hp
  · intro h
    exact h.scale d

/-- The bounded natural-number Vinogradov system embeds into the unrestricted
integer system by sending a coordinate `z : Fin X` to `z + 1`. -/
theorem IsVinogradovSolutionNat.toInt {k s X : ℕ} {x y : Fin s → Fin X}
    (h : IsVinogradovSolutionNat k s X x y) :
    IsVinogradovSolutionInt k s
      (fun i => ((x i).val + 1 : ℕ))
      (fun i => ((y i).val + 1 : ℕ)) := by
  intro j
  have hp := h j
  simpa only [vinogradovPowerSumInt, vinogradovPowerSumNat,
    Nat.cast_sum, Nat.cast_pow] using congrArg (fun z : ℕ => (z : ℤ)) hp

end

end ZeroFreeRegion.VinogradovKorobov
