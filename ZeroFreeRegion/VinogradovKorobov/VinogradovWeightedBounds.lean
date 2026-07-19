import ZeroFreeRegion.VinogradovKorobov.VinogradovWeighted

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Weighted modular equality is equivalently degree-wise natural-number
congruence of the ordinary power sums. -/
theorem isVinogradovWeightedSolutionMod_iff_powerSumNat_modEq
    (p a k s X : ℕ) (x y : Fin s → Fin X) :
    IsVinogradovWeightedSolutionMod p a k s X x y ↔
      ∀ j : Fin k,
        vinogradovPowerSumNat x j ≡ vinogradovPowerSumNat y j
          [MOD vinogradovWeightedModulus p a j] := by
  constructor
  · intro h j
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa only [natCast_vinogradovPowerSumNat_weighted] using h j
  · intro h j
    rw [← natCast_vinogradovPowerSumNat_weighted,
      ← natCast_vinogradovPowerSumNat_weighted,
      ZMod.natCast_eq_natCast_iff]
    exact h j

/-- Increasing the weighted scale strengthens the congruences, so every
solution at scale `b` is also a solution at each smaller scale `a`. -/
theorem IsVinogradovWeightedSolutionMod.mono_scale
    {p a b k s X : ℕ} (hab : a ≤ b) {x y : Fin s → Fin X}
    (h : IsVinogradovWeightedSolutionMod p b k s X x y) :
    IsVinogradovWeightedSolutionMod p a k s X x y := by
  rw [isVinogradovWeightedSolutionMod_iff_powerSumNat_modEq] at h ⊢
  intro j
  exact (h j).of_dvd (pow_dvd_pow p
    (Nat.mul_le_mul_left (j.val + 1) hab))

/-- Weighted solution counts are antitone in the scale parameter. -/
theorem vinogradovWeightedSolutionCountMod_antitone_scale
    (p k s X : ℕ) {a b : ℕ} (hab : a ≤ b) :
    vinogradovWeightedSolutionCountMod p b k s X ≤
      vinogradovWeightedSolutionCountMod p a k s X := by
  classical
  unfold vinogradovWeightedSolutionCountMod
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  exact hy.mono_scale hab

/-- Every tuple is paired with itself in the weighted modular system. -/
theorem isVinogradovWeightedSolutionMod_refl
    (p a k s X : ℕ) (x : Fin s → Fin X) :
    IsVinogradovWeightedSolutionMod p a k s X x x := by
  intro j
  rfl

/-- The weighted solution count is bounded by the number of all ordered tuple
pairs. -/
theorem vinogradovWeightedSolutionCountMod_le_total
    (p a k s X : ℕ) :
    vinogradovWeightedSolutionCountMod p a k s X ≤ X ^ (2 * s) := by
  classical
  unfold vinogradovWeightedSolutionCountMod
  calc
    ∑ x : Fin s → Fin X,
        ((Finset.univ.filter fun y : Fin s → Fin X ↦
          IsVinogradovWeightedSolutionMod p a k s X x y).card) ≤
        ∑ _x : Fin s → Fin X,
          Fintype.card (Fin s → Fin X) := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = X ^ (2 * s) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fun, Fintype.card_fin]
      change X ^ s * X ^ s = X ^ (2 * s)
      rw [← pow_add]
      congr 2
      omega

/-- Diagonal tuple pairs contribute at least `X^s` weighted solutions. -/
theorem pow_le_vinogradovWeightedSolutionCountMod
    (p a k s X : ℕ) :
    X ^ s ≤ vinogradovWeightedSolutionCountMod p a k s X := by
  classical
  unfold vinogradovWeightedSolutionCountMod
  calc
    X ^ s = ∑ _x : Fin s → Fin X, 1 := by simp
    _ ≤ ∑ x : Fin s → Fin X,
        ((Finset.univ.filter fun y : Fin s → Fin X ↦
          IsVinogradovWeightedSolutionMod p a k s X x y).card) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.one_le_card.mpr
      exact ⟨x, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact isVinogradovWeightedSolutionMod_refl p a k s X x⟩

/-- At scale zero every degree modulus is one, so every tuple pair satisfies
the weighted system. -/
theorem isVinogradovWeightedSolutionMod_zero
    (p k s X : ℕ) (x y : Fin s → Fin X) :
    IsVinogradovWeightedSolutionMod p 0 k s X x y := by
  rw [isVinogradovWeightedSolutionMod_iff_powerSumNat_modEq]
  intro j
  have hm : vinogradovWeightedModulus p 0 j = 1 := by
    simp [vinogradovWeightedModulus]
  rw [hm]
  exact Nat.modEq_one

/-- Consequently the scale-zero weighted solution count is exactly the total
number of ordered tuple pairs. -/
theorem vinogradovWeightedSolutionCountMod_zero
    (p k s X : ℕ) :
    vinogradovWeightedSolutionCountMod p 0 k s X = X ^ (2 * s) := by
  classical
  unfold vinogradovWeightedSolutionCountMod
  simp_rw [show ∀ (x y : Fin s → Fin X),
      IsVinogradovWeightedSolutionMod p 0 k s X x y from
    fun x y ↦ isVinogradovWeightedSolutionMod_zero p k s X x y]
  simp only [Finset.filter_true, Finset.card_univ, Finset.sum_const,
    nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin]
  change X ^ s * X ^ s = X ^ (2 * s)
  rw [← pow_add]
  congr 2
  omega

end

end ZeroFreeRegion.VinogradovKorobov
