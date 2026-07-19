import ZeroFreeRegion.VinogradovKorobov.VinogradovBounds

open scoped BigOperators Matrix

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Swap the two entries of a tuple indexed by `Fin 2`. -/
def swapFinTwo {α : Type*} (x : Fin 2 → α) : Fin 2 → α :=
  ![x 1, x 0]

@[simp] theorem swapFinTwo_zero {α : Type*} (x : Fin 2 → α) :
    swapFinTwo x 0 = x 1 := by
  simp [swapFinTwo]

@[simp] theorem swapFinTwo_one {α : Type*} (x : Fin 2 → α) :
    swapFinTwo x 1 = x 0 := by
  simp [swapFinTwo]

/-- Two natural-number pairs with the same first and second power sums agree
up to permutation. -/
theorem pair_eq_or_swap_of_sum_sq
    {a b c d : ℕ} (hsum : a + b = c + d)
    (hsq : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hsumZ : (a : ℤ) + (b : ℤ) = (c : ℤ) + (d : ℤ) := by
    exact_mod_cast hsum
  have hsqZ : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 =
      (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by
    exact_mod_cast hsq
  have hfactor : ((a : ℤ) - c) * ((a : ℤ) - d) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hac | had
  · left
    have hacNat : a = c := by
      exact_mod_cast (sub_eq_zero.mp hac)
    exact ⟨hacNat, by omega⟩
  · right
    have hadNat : a = d := by
      exact_mod_cast (sub_eq_zero.mp had)
    exact ⟨hadNat, by omega⟩

/-- A two-variable solution of the degree-two Vinogradov system is either the
same ordered pair or its transposition. -/
theorem isVinogradovSolutionNat_two_eq_or_swap {X : ℕ}
    {x y : Fin 2 → Fin X}
    (h : IsVinogradovSolutionNat 2 2 X x y) :
    y = x ∨ y = swapFinTwo x := by
  have hsum : ((x 0).val + 1) + ((x 1).val + 1) =
      ((y 0).val + 1) + ((y 1).val + 1) := by
    simpa [vinogradovPowerSumNat, Fin.sum_univ_two] using h (0 : Fin 2)
  have hsq : ((x 0).val + 1) ^ 2 + ((x 1).val + 1) ^ 2 =
      ((y 0).val + 1) ^ 2 + ((y 1).val + 1) ^ 2 := by
    simpa [vinogradovPowerSumNat, Fin.sum_univ_two] using h (1 : Fin 2)
  obtain ⟨h0, h1⟩ | ⟨h0, h1⟩ := pair_eq_or_swap_of_sum_sq hsum hsq
  · left
    apply (finTwoArrowEquiv (Fin X)).injective
    change (y 0, y 1) = (x 0, x 1)
    congr
    · apply Fin.ext
      omega
    · apply Fin.ext
      omega
  · right
    apply (finTwoArrowEquiv (Fin X)).injective
    change (y 0, y 1) = (swapFinTwo x 0, swapFinTwo x 1)
    simp only [swapFinTwo_zero, swapFinTwo_one]
    congr
    · apply Fin.ext
      omega
    · apply Fin.ext
      omega

/-- For a fixed left pair, the degree-two Vinogradov system has at most two
right pairs. -/
theorem fixed_left_quadratic_solution_count_le_two (X : ℕ)
    (x : Fin 2 → Fin X) :
    (Finset.univ.filter fun y : Fin 2 → Fin X ↦
      IsVinogradovSolutionNat 2 2 X x y).card ≤ 2 := by
  classical
  have hsubset :
      Finset.univ.filter (fun y : Fin 2 → Fin X ↦
        IsVinogradovSolutionNat 2 2 X x y) ⊆ {x, swapFinTwo x} := by
    intro y hy
    have hsol : IsVinogradovSolutionNat 2 2 X x y :=
      (Finset.mem_filter.mp hy).2
    rcases isVinogradovSolutionNat_two_eq_or_swap hsol with h | h
    · simp [h]
    · simp [h]
  exact (Finset.card_le_card hsubset).trans Finset.card_le_two

/-- The two-variable quadratic Vinogradov mean value is at most `2 * X^2`. -/
theorem vinogradovSolutionCountNat_two_two_le (X : ℕ) :
    vinogradovSolutionCountNat 2 2 X ≤ 2 * X ^ 2 := by
  classical
  unfold vinogradovSolutionCountNat
  calc
    ∑ x : Fin 2 → Fin X,
        ((Finset.univ.filter fun y : Fin 2 → Fin X ↦
          IsVinogradovSolutionNat 2 2 X x y).card) ≤
        ∑ _x : Fin 2 → Fin X, 2 := by
      apply Finset.sum_le_sum
      intro x hx
      exact fixed_left_quadratic_solution_count_le_two X x
    _ = 2 * X ^ 2 := by simp [mul_comm]

/-- The quadratic rigidity bound transfers to the finite fourth Weyl moment. -/
theorem norm_normalizedVinogradovMomentMod_two_two_le
    (Q X : ℕ) [NeZero Q] (hX : 1 ≤ X) (hQ : 2 * X ^ 2 < Q) :
    ‖normalizedVinogradovMomentMod Q 2 2 X‖ ≤ 2 * (X : ℝ) ^ 2 := by
  rw [normalizedVinogradovMomentMod_eq_natCount_of_topScale Q 2 2 X hX hQ]
  exact_mod_cast vinogradovSolutionCountNat_two_two_le X

end

end ZeroFreeRegion.VinogradovKorobov
