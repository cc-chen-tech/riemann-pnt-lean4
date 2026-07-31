import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- Explicit integral majorant for the finite negative real-power sum over
`1, ..., L - 1`. -/
noncomputable def finiteRpowSumEnvelope (L : ℕ) (α : ℝ) : ℝ :=
  1 + ((((L - 1 : ℕ) : ℝ) ^ (1 - α) - 1) / (1 - α))

/-- A finite negative real-power sum is controlled by its elementary
integral majorant for exponents in `[0, 1)`. -/
theorem sum_Icc_rpow_neg_le_envelope
    (L : ℕ) (α : ℝ) (hL : 2 ≤ L) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (∑ ell ∈ Finset.Icc 1 (L - 1), (ell : ℝ) ^ (-α)) ≤
      finiteRpowSumEnvelope L α := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-α)
  have hanti : AntitoneOn f
      (Set.Icc (((1 : ℕ) : ℝ)) ((L - 1 : ℕ) : ℝ)) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (show -α ≤ 0 by linarith)).mono
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := by
      simpa only [Nat.cast_one] using hx.1
    exact (by norm_num : (0 : ℝ) < 1).trans_le hx1
  have hint :
      (∑ i ∈ Finset.Ico 1 (L - 1), f (i + 1 : ℕ)) ≤
        ∫ x : ℝ in 1..((L - 1 : ℕ) : ℝ), f x := by
    simpa only [Nat.cast_one] using
      (@AntitoneOn.sum_le_integral_Ico 1 (L - 1) f (by omega) hanti)
  have htail :
      (∑ ell ∈ Finset.Ico 2 L, (ell : ℝ) ^ (-α)) ≤
        ∫ x : ℝ in 1..((L - 1 : ℕ) : ℝ), x ^ (-α) := by
    have hshift := Finset.sum_Ico_add'
      (fun ell : ℕ ↦ (ell : ℝ) ^ (-α)) 1 (L - 1) 1
    rw [show L - 1 + 1 = L by omega] at hshift
    rw [← hshift]
    simpa only [Nat.cast_add, Nat.cast_one] using hint
  have hsplit := Finset.sum_Ico_consecutive
    (fun ell : ℕ ↦ (ell : ℝ) ^ (-α)) (show 1 ≤ 2 by omega) hL
  have hsets : Finset.Icc 1 (L - 1) = Finset.Ico 1 L := by
    ext ell
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hsets, ← hsplit]
  simp only [Finset.sum_Ico_eq_sub _ (show 1 ≤ 2 by omega),
    Finset.sum_range_succ, Nat.cast_zero, Nat.cast_one, Real.one_rpow,
    add_sub_cancel_left]
  calc
    1 + ∑ ell ∈ Finset.Ico 2 L, (ell : ℝ) ^ (-α) ≤
        1 + ∫ x : ℝ in 1..((L - 1 : ℕ) : ℝ), x ^ (-α) :=
      add_le_add le_rfl htail
    _ = finiteRpowSumEnvelope L α := by
      rw [integral_rpow (Or.inl (by linarith))]
      rw [Real.one_rpow]
      unfold finiteRpowSumEnvelope
      congr 2 <;> ring

/-- Weighted form of the finite negative real-power estimate used by the
A-process recurrence. -/
theorem weighted_rpow_neg_sum_le_envelope
    (L : ℕ) (α : ℝ) (hL : 2 ≤ L) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * (ell : ℝ) ^ (-α)) ≤
      (L : ℝ) * finiteRpowSumEnvelope L α := by
  calc
    (∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * (ell : ℝ) ^ (-α)) ≤
        ∑ ell ∈ Finset.Icc 1 (L - 1),
          (L : ℝ) * (ell : ℝ) ^ (-α) := by
      apply Finset.sum_le_sum
      intro ell hell
      exact mul_le_mul_of_nonneg_right
        (sub_le_self (L : ℝ) (Nat.cast_nonneg ell))
        (Real.rpow_nonneg (Nat.cast_nonneg ell) _)
    _ = (L : ℝ) *
        (∑ ell ∈ Finset.Icc 1 (L - 1), (ell : ℝ) ^ (-α)) := by
      rw [Finset.mul_sum]
    _ ≤ (L : ℝ) * finiteRpowSumEnvelope L α :=
      mul_le_mul_of_nonneg_left
        (sum_Icc_rpow_neg_le_envelope L α hL hα0 hα1)
        (Nat.cast_nonneg L)

/-- The explicit finite-power-sum envelope is nonnegative on its intended
parameter range. -/
theorem finiteRpowSumEnvelope_nonneg
    (L : ℕ) (α : ℝ) (hL : 2 ≤ L) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 ≤ finiteRpowSumEnvelope L α := by
  have hsum : 0 ≤
      ∑ ell ∈ Finset.Icc 1 (L - 1), (ell : ℝ) ^ (-α) := by
    exact Finset.sum_nonneg (fun ell _ ↦
      Real.rpow_nonneg (Nat.cast_nonneg ell) _)
  exact hsum.trans (sum_Icc_rpow_neg_le_envelope L α hL hα0 hα1)

/-- After division by the differencing length, the finite power-sum
majorant retains the expected negative power of that length. -/
theorem finiteRpowSumEnvelope_div_le_rpow
    (L : ℕ) (α : ℝ) (hL : 2 ≤ L) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    finiteRpowSumEnvelope L α / (L : ℝ) ≤
      2 / (1 - α) * (L : ℝ) ^ (-α) := by
  have hLpos : 0 < (L : ℝ) := Nat.cast_pos.mpr (by omega)
  have hLone : (1 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast (show 1 ≤ L by omega)
  have hden : 0 < 1 - α := by linarith
  have hpowOne : 1 ≤ (L : ℝ) ^ (1 - α) :=
    Real.one_le_rpow hLone (by linarith)
  have hpowNonneg : 0 ≤ (L : ℝ) ^ (1 - α) :=
    hpowOne.trans' zero_le_one
  have hsub : (((L - 1 : ℕ) : ℝ)) ≤ (L : ℝ) := by
    exact_mod_cast (Nat.sub_le L 1)
  have hsub0 : 0 ≤ (((L - 1 : ℕ) : ℝ)) := Nat.cast_nonneg _
  have hpowSub : (((L - 1 : ℕ) : ℝ)) ^ (1 - α) ≤
      (L : ℝ) ^ (1 - α) :=
    Real.rpow_le_rpow hsub0 hsub (by linarith)
  have henv : finiteRpowSumEnvelope L α ≤
      2 * (L : ℝ) ^ (1 - α) / (1 - α) := by
    unfold finiteRpowSumEnvelope
    calc
      1 + ((((L - 1 : ℕ) : ℝ) ^ (1 - α) - 1) / (1 - α)) ≤
          1 + ((L : ℝ) ^ (1 - α) / (1 - α)) := by
        gcongr
        linarith
      _ ≤ (L : ℝ) ^ (1 - α) +
          (L : ℝ) ^ (1 - α) / (1 - α) := by linarith
      _ ≤ (L : ℝ) ^ (1 - α) / (1 - α) +
          (L : ℝ) ^ (1 - α) / (1 - α) := by
        gcongr
        exact (le_div_iff₀ hden).2 (by
          nlinarith [mul_nonneg hpowNonneg hα0])
      _ = 2 * (L : ℝ) ^ (1 - α) / (1 - α) := by ring
  calc
    finiteRpowSumEnvelope L α / (L : ℝ) ≤
        (2 * (L : ℝ) ^ (1 - α) / (1 - α)) / (L : ℝ) :=
      div_le_div_of_nonneg_right henv hLpos.le
    _ = 2 / (1 - α) * (L : ℝ) ^ (-α) := by
      rw [show (1 - α : ℝ) = -α + 1 by ring,
        Real.rpow_add hLpos (-α) 1, Real.rpow_one]
      field_simp

end ZeroFreeRegion.VinogradovKorobov
