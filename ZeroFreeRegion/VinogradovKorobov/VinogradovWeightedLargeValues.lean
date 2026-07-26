import ZeroFreeRegion.VinogradovKorobov.VinogradovWeightedMainEstimate

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The unnormalized real `2s`-th moment of the weighted Weyl sums is the
critical-weight coefficient volume times the weighted modular solution count. -/
theorem sum_norm_vinogradovWeightedWeylSum_pow_two_mul_eq
    (p a k s X : ℕ) [Fact p.Prime] :
    ∑ c : VinogradovWeightedCoefficient p a k,
        ‖vinogradovWeightedWeylSum p a k X c‖ ^ (2 * s) =
      (p : ℝ) ^ (a * (k * (k + 1) / 2)) *
        vinogradovWeightedSolutionCountMod p a k s X := by
  have hsummand (c : VinogradovWeightedCoefficient p a k) :
      vinogradovWeightedWeylSum p a k X c ^ s *
          (starRingEnd ℂ) (vinogradovWeightedWeylSum p a k X c) ^ s =
        ((‖vinogradovWeightedWeylSum p a k X c‖ ^ (2 * s) : ℝ) : ℂ) := by
    rw [← mul_pow, Complex.mul_conj']
    simp only [Complex.ofReal_pow, pow_mul]
  have h := normalizedVinogradovWeightedMomentMod_eq_solutionCount
    p a k s X
  unfold normalizedVinogradovWeightedMomentMod at h
  rw [prod_vinogradovWeightedModulus_inv_natCast] at h
  simp_rw [hsummand] at h
  rw [← Complex.ofReal_sum] at h
  have hP : (p ^ (a * (k * (k + 1) / 2)) : ℂ) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast]
  calc
    (∑ c : VinogradovWeightedCoefficient p a k,
        (‖vinogradovWeightedWeylSum p a k X c‖ : ℂ) ^ (2 * s)) =
        ∑ c : VinogradovWeightedCoefficient p a k,
          ((‖vinogradovWeightedWeylSum p a k X c‖ ^ (2 * s) : ℝ) : ℂ) := by
      simp only [Complex.ofReal_pow]
    _ = (p ^ (a * (k * (k + 1) / 2)) : ℂ) *
          ((p ^ (a * (k * (k + 1) / 2)) : ℂ)⁻¹ *
            ∑ c : VinogradovWeightedCoefficient p a k,
              ((‖vinogradovWeightedWeylSum p a k X c‖ ^
                (2 * s) : ℝ) : ℂ)) := by
      rw [← mul_assoc]
      simp [hP]
    _ = (p ^ (a * (k * (k + 1) / 2)) : ℂ) *
          (vinogradovWeightedSolutionCountMod p a k s X : ℂ) := by
      simpa only [Complex.ofReal_sum] using
        congrArg
          (fun z : ℂ ↦ (p ^ (a * (k * (k + 1) / 2)) : ℂ) * z) h

/-- Coefficient vectors on which the weighted complete Weyl sum has norm at
least `V`. -/
noncomputable def largeVinogradovWeightedCoefficientSet
    (p a k X : ℕ) [Fact p.Prime] (V : ℝ) :
    Finset (VinogradovWeightedCoefficient p a k) :=
  Finset.univ.filter fun c ↦ V ≤ ‖vinogradovWeightedWeylSum p a k X c‖

/-- Finite Markov inequality for weighted complete Weyl sums. -/
theorem card_largeVinogradovWeightedCoefficientSet_mul_pow_le
    (p a k s X : ℕ) [Fact p.Prime] {V : ℝ} (hV : 0 ≤ V) :
    ((largeVinogradovWeightedCoefficientSet p a k X V).card : ℝ) *
        V ^ (2 * s) ≤
      (p : ℝ) ^ (a * (k * (k + 1) / 2)) *
        vinogradovWeightedSolutionCountMod p a k s X := by
  rw [← sum_norm_vinogradovWeightedWeylSum_pow_two_mul_eq]
  let S := largeVinogradovWeightedCoefficientSet p a k X V
  calc
    (S.card : ℝ) * V ^ (2 * s) = ∑ _c ∈ S, V ^ (2 * s) := by simp
    _ ≤ ∑ c ∈ S,
        ‖vinogradovWeightedWeylSum p a k X c‖ ^ (2 * s) := by
      apply Finset.sum_le_sum
      intro c hc
      apply pow_le_pow_left₀ hV
      exact (Finset.mem_filter.mp hc).2
    _ ≤ ∑ c : VinogradovWeightedCoefficient p a k,
        ‖vinogradovWeightedWeylSum p a k X c‖ ^ (2 * s) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset
          (fun c : VinogradovWeightedCoefficient p a k ↦
            V ≤ ‖vinogradovWeightedWeylSum p a k X c‖) Finset.univ)
      intro c _ _
      positivity

/-- A verified ordinary Vinogradov mean-value estimate controls the large
weighted coefficient set in the no-wrap range. -/
theorem card_largeVinogradovWeightedCoefficientSet_mul_pow_le_of_meanValueEstimate
    (p a k s X : ℕ) [Fact p.Prime] {V ε C : ℝ}
    (hest : VinogradovMeanValueEstimate k s ε C)
    (hV : 0 ≤ V) (hX : 1 ≤ X)
    (hscale : ∀ j : Fin k,
      s * X ^ (j.val + 1) < vinogradovWeightedModulus p a j) :
    ((largeVinogradovWeightedCoefficientSet p a k X V).card : ℝ) *
        V ^ (2 * s) ≤
      (p : ℝ) ^ (a * (k * (k + 1) / 2)) *
        (C * Real.rpow (X : ℝ) ε *
          ((X : ℝ) ^ s +
            (X : ℝ) ^ (2 * s - vinogradovCriticalWeight k))) := by
  have hcount :
      (vinogradovWeightedSolutionCountMod p a k s X : ℝ) ≤
        C * Real.rpow (X : ℝ) ε *
          ((X : ℝ) ^ s +
            (X : ℝ) ^ (2 * s - vinogradovCriticalWeight k)) := by
    rw [vinogradovWeightedSolutionCountMod_eq_nat_of_scale
      p a k s X hscale]
    exact hest.2.2 X hX
  exact
    (card_largeVinogradovWeightedCoefficientSet_mul_pow_le
      p a k s X hV).trans
      (mul_le_mul_of_nonneg_left hcount (by positivity))

end

end ZeroFreeRegion.VinogradovKorobov
