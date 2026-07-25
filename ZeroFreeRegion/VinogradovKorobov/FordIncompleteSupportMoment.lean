import ZeroFreeRegion.VinogradovKorobov.VinogradovIncompleteSupportMoment

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The unnormalized real `2s`-moment of an incomplete Weyl sum on an
arbitrary finite support is the coefficient-space volume times its exact
incomplete Vinogradov solution count.  This is the finite modular analogue
of the incomplete moment appearing on the right of Ford's second Holder
step. -/
theorem sum_norm_incompleteVinogradovSupportWeylSumMod_pow_two_mul_eq
    (Q h d s X : ℕ) [NeZero Q] (B : Finset (Fin X)) :
    ∑ a : Fin d → ZMod Q,
      ‖incompleteVinogradovSupportWeylSumMod Q h d X B a‖ ^ (2 * s) =
        (Q : ℝ) ^ d *
          incompleteVinogradovSupportSolutionCountMod Q h d s X B := by
  have hsummand (a : Fin d → ZMod Q) :
      incompleteVinogradovSupportWeylSumMod Q h d X B a ^ s *
          (starRingEnd ℂ)
            (incompleteVinogradovSupportWeylSumMod Q h d X B a) ^ s =
        ((‖incompleteVinogradovSupportWeylSumMod Q h d X B a‖ ^
          (2 * s) : ℝ) : ℂ) := by
    rw [← mul_pow, Complex.mul_conj']
    simp only [Complex.ofReal_pow, pow_mul]
  have hmoment :=
    normalizedIncompleteVinogradovSupportMomentMod_eq_solutionCount
      Q h d s X B
  unfold normalizedIncompleteVinogradovSupportMomentMod
    normalizedIncompleteMomentOnMod at hmoment
  simp_rw [hsummand] at hmoment
  rw [← Complex.ofReal_sum] at hmoment
  have hQ : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Q)
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast]
  calc
    (∑ a : Fin d → ZMod Q,
        (‖incompleteVinogradovSupportWeylSumMod Q h d X B a‖ : ℂ) ^
          (2 * s)) =
        ∑ a : Fin d → ZMod Q,
          ((‖incompleteVinogradovSupportWeylSumMod Q h d X B a‖ ^
            (2 * s) : ℝ) : ℂ) := by
      simp only [Complex.ofReal_pow]
    _ = (Q : ℂ) ^ d *
        ((Q : ℂ)⁻¹ ^ d *
          ∑ a : Fin d → ZMod Q,
            ((‖incompleteVinogradovSupportWeylSumMod Q h d X B a‖ ^
              (2 * s) : ℝ) : ℂ)) := by
      rw [← mul_assoc, ← mul_pow]
      simp [hQ]
    _ = (Q : ℂ) ^ d *
        (incompleteVinogradovSupportSolutionCountMod Q h d s X B : ℂ) := by
      simpa only [Complex.ofReal_sum] using
        congrArg (fun z : ℂ ↦ (Q : ℂ) ^ d * z) hmoment

end

end ZeroFreeRegion.VinogradovKorobov
