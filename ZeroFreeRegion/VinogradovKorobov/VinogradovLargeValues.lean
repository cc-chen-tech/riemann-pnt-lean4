import ZeroFreeRegion.VinogradovKorobov.VinogradovMainEstimate

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The unnormalized real `2s`-th moment of the complete polynomial Weyl sums
is the modulus-volume times the number of modular Vinogradov solutions. -/
theorem sum_norm_vinogradovWeylSumMod_pow_two_mul_eq
    (Q k s X : ℕ) [NeZero Q] :
    ∑ a : Fin k → ZMod Q, ‖vinogradovWeylSumMod Q k X a‖ ^ (2 * s) =
      (Q : ℝ) ^ k * vinogradovSolutionCountMod Q k s X := by
  have hsummand (a : Fin k → ZMod Q) :
      vinogradovWeylSumMod Q k X a ^ s *
          (starRingEnd ℂ) (vinogradovWeylSumMod Q k X a) ^ s =
        ((‖vinogradovWeylSumMod Q k X a‖ ^ (2 * s) : ℝ) : ℂ) := by
    rw [← mul_pow, Complex.mul_conj']
    simp only [Complex.ofReal_pow, pow_mul]
  have h := normalizedVinogradovMomentMod_eq_solutionCount Q k s X
  unfold normalizedVinogradovMomentMod at h
  simp_rw [hsummand] at h
  rw [← Complex.ofReal_sum] at h
  have hQ : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Q)
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast]
  calc
    (∑ a : Fin k → ZMod Q,
        (‖vinogradovWeylSumMod Q k X a‖ : ℂ) ^ (2 * s)) =
        ∑ a : Fin k → ZMod Q,
          ((‖vinogradovWeylSumMod Q k X a‖ ^ (2 * s) : ℝ) : ℂ) := by
      simp only [Complex.ofReal_pow]
    _ =
        (Q : ℂ) ^ k *
          ((Q : ℂ)⁻¹ ^ k *
            ∑ a : Fin k → ZMod Q,
              ((‖vinogradovWeylSumMod Q k X a‖ ^ (2 * s) : ℝ) : ℂ)) := by
      rw [← mul_assoc, ← mul_pow]
      simp [hQ]
    _ = (Q : ℂ) ^ k * (vinogradovSolutionCountMod Q k s X : ℂ) := by
      simpa only [Complex.ofReal_sum] using
        congrArg (fun z : ℂ ↦ (Q : ℂ) ^ k * z) h

/-- Coefficient vectors for which the complete polynomial Weyl sum is at
least `V` in norm. -/
noncomputable def largeVinogradovCoefficientSet
    (Q k X : ℕ) [NeZero Q] (V : ℝ) : Finset (Fin k → ZMod Q) :=
  Finset.univ.filter fun a ↦ V ≤ ‖vinogradovWeylSumMod Q k X a‖

/-- Finite Markov inequality for complete polynomial Weyl sums. -/
theorem card_largeVinogradovCoefficientSet_mul_pow_le
    (Q k s X : ℕ) [NeZero Q] {V : ℝ} (hV : 0 ≤ V) :
    ((largeVinogradovCoefficientSet Q k X V).card : ℝ) * V ^ (2 * s) ≤
      (Q : ℝ) ^ k * vinogradovSolutionCountMod Q k s X := by
  rw [← sum_norm_vinogradovWeylSumMod_pow_two_mul_eq Q k s X]
  let S := largeVinogradovCoefficientSet Q k X V
  calc
    (S.card : ℝ) * V ^ (2 * s) = ∑ _a ∈ S, V ^ (2 * s) := by
      simp
    _ ≤ ∑ a ∈ S, ‖vinogradovWeylSumMod Q k X a‖ ^ (2 * s) := by
      apply Finset.sum_le_sum
      intro a ha
      apply pow_le_pow_left₀ hV
      exact (Finset.mem_filter.mp ha).2
    _ ≤ ∑ a : Fin k → ZMod Q,
        ‖vinogradovWeylSumMod Q k X a‖ ^ (2 * s) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset (fun a : Fin k → ZMod Q ↦
          V ≤ ‖vinogradovWeylSumMod Q k X a‖) Finset.univ)
      intro a _ _
      positivity

/-- Any ordinary Vinogradov mean-value estimate gives a quantitative bound
for the number of coefficient vectors with a large Weyl sum. -/
theorem card_largeVinogradovCoefficientSet_mul_pow_le_of_meanValueEstimate
    (Q k s X : ℕ) [NeZero Q] {V ε C : ℝ}
    (hest : VinogradovMeanValueEstimate k s ε C)
    (hV : 0 ≤ V) (hX : 1 ≤ X) (hQ : s * X ^ k < Q) :
    ((largeVinogradovCoefficientSet Q k X V).card : ℝ) * V ^ (2 * s) ≤
      (Q : ℝ) ^ k *
        (C * Real.rpow (X : ℝ) ε *
          ((X : ℝ) ^ s +
            (X : ℝ) ^ (2 * s - vinogradovCriticalWeight k))) := by
  have hcount :
      (vinogradovSolutionCountMod Q k s X : ℝ) ≤
        C * Real.rpow (X : ℝ) ε *
          ((X : ℝ) ^ s +
            (X : ℝ) ^ (2 * s - vinogradovCriticalWeight k)) := by
    rw [vinogradovSolutionCountMod_eq_nat_of_topScale Q k s X hX hQ]
    exact hest.2.2 X hX
  exact (card_largeVinogradovCoefficientSet_mul_pow_le Q k s X hV).trans
    (mul_le_mul_of_nonneg_left hcount (by positivity))

end

end ZeroFreeRegion.VinogradovKorobov
