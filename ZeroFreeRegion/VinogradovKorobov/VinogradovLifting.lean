import ZeroFreeRegion.VinogradovKorobov.VinogradovMoment

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The ordinary natural-number power sum of a tuple in `{1, ..., X}`. -/
def vinogradovPowerSumNat {k s X : ℕ}
    (x : Fin s → Fin X) (j : Fin k) : ℕ :=
  ∑ i, ((x i).val + 1) ^ (j.val + 1)

/-- A pair of tuples solves the degree-`k` Vinogradov system over the integers. -/
def IsVinogradovSolutionNat (k s X : ℕ)
    (x y : Fin s → Fin X) : Prop :=
  ∀ j : Fin k, vinogradovPowerSumNat x j = vinogradovPowerSumNat y j

/-- The number of ordered integer solutions of the degree-`k` Vinogradov system. -/
noncomputable def vinogradovSolutionCountNat (k s X : ℕ) : ℕ := by
  classical
  exact ∑ x : Fin s → Fin X,
    (Finset.univ.filter fun y : Fin s → Fin X ↦
      IsVinogradovSolutionNat k s X x y).card

/-- Reduction modulo `Q` commutes with the tuple power sum. -/
theorem natCast_vinogradovPowerSumNat (Q : ℕ) {k s X : ℕ}
    (x : Fin s → Fin X) (j : Fin k) :
    (vinogradovPowerSumNat x j : ZMod Q) =
      vinogradovPowerSumMod Q x j := by
  classical
  simp [vinogradovPowerSumNat, vinogradovPowerSumMod,
    Nat.cast_add, Nat.cast_pow]

/-- Every integer solution remains a solution after reduction modulo `Q`. -/
theorem IsVinogradovSolutionNat.toMod (Q k s X : ℕ)
    {x y : Fin s → Fin X}
    (h : IsVinogradovSolutionNat k s X x y) :
    IsVinogradovSolutionMod Q k s X x y := by
  intro j
  rw [← natCast_vinogradovPowerSumNat,
    ← natCast_vinogradovPowerSumNat, h j]

/-- Equality modulo `Q` lifts to equality of natural numbers when both
representatives lie below `Q`. -/
theorem nat_eq_of_cast_zmod_eq_of_lt (Q a b : ℕ)
    (ha : a < Q) (hb : b < Q) (h : (a : ZMod Q) = (b : ZMod Q)) :
    a = b := by
  have hv := congrArg ZMod.val h
  simpa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using hv

/-- A modular Vinogradov solution lifts to an integer solution as soon as all
power sums on both sides are smaller than the modulus. -/
theorem IsVinogradovSolutionMod.toNat_of_lt (Q k s X : ℕ)
    {x y : Fin s → Fin X}
    (h : IsVinogradovSolutionMod Q k s X x y)
    (hx : ∀ j : Fin k, vinogradovPowerSumNat x j < Q)
    (hy : ∀ j : Fin k, vinogradovPowerSumNat y j < Q) :
    IsVinogradovSolutionNat k s X x y := by
  intro j
  apply nat_eq_of_cast_zmod_eq_of_lt Q _ _ (hx j) (hy j)
  simpa only [natCast_vinogradovPowerSumNat] using h j

/-- Each tuple power sum is bounded by `s * X^(j+1)`. -/
theorem vinogradovPowerSumNat_le {k s X : ℕ}
    (x : Fin s → Fin X) (j : Fin k) :
    vinogradovPowerSumNat x j ≤ s * X ^ (j.val + 1) := by
  classical
  unfold vinogradovPowerSumNat
  calc
    ∑ i : Fin s, ((x i).val + 1) ^ (j.val + 1) ≤
        ∑ _i : Fin s, X ^ (j.val + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.pow_le_pow_left (Nat.succ_le_iff.mpr (x i).isLt) _
    _ = s * X ^ (j.val + 1) := by simp

/-- A scale condition depending only on `s`, `X`, and the degree guarantees
that modular and integer Vinogradov solutions are equivalent. -/
theorem isVinogradovSolutionMod_iff_nat_of_scale (Q k s X : ℕ)
    (hQ : ∀ j : Fin k, s * X ^ (j.val + 1) < Q)
    (x y : Fin s → Fin X) :
    IsVinogradovSolutionMod Q k s X x y ↔
      IsVinogradovSolutionNat k s X x y := by
  constructor
  · intro h
    apply h.toNat_of_lt Q k s X
    · intro j
      exact (vinogradovPowerSumNat_le x j).trans_lt (hQ j)
    · intro j
      exact (vinogradovPowerSumNat_le y j).trans_lt (hQ j)
  · exact fun h ↦ h.toMod Q k s X

/-- Under the no-wrap scale condition, the modular solution count is exactly
the ordinary integer Vinogradov solution count. -/
theorem vinogradovSolutionCountMod_eq_nat_of_scale (Q k s X : ℕ)
    (hQ : ∀ j : Fin k, s * X ^ (j.val + 1) < Q) :
    vinogradovSolutionCountMod Q k s X =
      vinogradovSolutionCountNat k s X := by
  classical
  unfold vinogradovSolutionCountMod vinogradovSolutionCountNat
  apply Finset.sum_congr rfl
  intro x hx
  apply congrArg Finset.card
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact isVinogradovSolutionMod_iff_nat_of_scale Q k s X hQ x y

/-- It suffices to place the modulus above the largest degree-`k` power-sum
bound when `X` is positive. -/
theorem vinogradovSolutionCountMod_eq_nat_of_topScale (Q k s X : ℕ)
    (hX : 1 ≤ X) (hQ : s * X ^ k < Q) :
    vinogradovSolutionCountMod Q k s X =
      vinogradovSolutionCountNat k s X := by
  apply vinogradovSolutionCountMod_eq_nat_of_scale
  intro j
  exact (Nat.mul_le_mul_left s
    (pow_le_pow_right' hX (Nat.succ_le_iff.mpr j.isLt))).trans_lt hQ

/-- Under the no-wrap scale condition, the finite Fourier moment computes the
ordinary integer Vinogradov mean value. -/
theorem normalizedVinogradovMomentMod_eq_natCount_of_topScale
    (Q k s X : ℕ) [NeZero Q]
    (hX : 1 ≤ X) (hQ : s * X ^ k < Q) :
    normalizedVinogradovMomentMod Q k s X =
      (vinogradovSolutionCountNat k s X : ℂ) := by
  rw [normalizedVinogradovMomentMod_eq_solutionCount,
    vinogradovSolutionCountMod_eq_nat_of_topScale Q k s X hX hQ]

end

end ZeroFreeRegion.VinogradovKorobov
