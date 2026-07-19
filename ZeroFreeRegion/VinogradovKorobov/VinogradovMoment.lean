import ZeroFreeRegion.VinogradovKorobov.VinogradovMeanValue

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The tuple phase is the coefficient pairing with the vector of power sums. -/
theorem vinogradovTuplePhaseMod_eq_sum_powerSum (Q : ℕ) {k s X : ℕ}
    (a : Fin k → ZMod Q) (x : Fin s → Fin X) :
    vinogradovTuplePhaseMod Q a x =
      ∑ j : Fin k, a j * vinogradovPowerSumMod Q x j := by
  classical
  unfold vinogradovTuplePhaseMod vinogradovPhaseMod vinogradovPowerSumMod
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro i
  simp only [Nat.cast_add, Nat.cast_one]

/-- Pairing a tuple with a conjugate tuple produces the difference of their
power-sum vectors. -/
theorem vinogradovTuplePhaseMod_sub_eq (Q : ℕ) {k s X : ℕ}
    (a : Fin k → ZMod Q) (x y : Fin s → Fin X) :
    vinogradovTuplePhaseMod Q a x - vinogradovTuplePhaseMod Q a y =
      ∑ j : Fin k, a j *
        (vinogradovPowerSumMod Q x j - vinogradovPowerSumMod Q y j) := by
  rw [vinogradovTuplePhaseMod_eq_sum_powerSum,
    vinogradovTuplePhaseMod_eq_sum_powerSum, ← Finset.sum_sub_distrib]
  apply Fintype.sum_congr
  intro j
  ring

/-- The product of a tuple character and a conjugate tuple character is the
character of the coefficient pairing with the power-sum difference. -/
theorem stdAddChar_tuple_mul_neg_tuple (Q : ℕ) [NeZero Q] {k s X : ℕ}
    (a : Fin k → ZMod Q) (x y : Fin s → Fin X) :
    ZMod.stdAddChar (vinogradovTuplePhaseMod Q a x) *
        ZMod.stdAddChar (-vinogradovTuplePhaseMod Q a y) =
      ZMod.stdAddChar
        (∑ j : Fin k, a j *
          (vinogradovPowerSumMod Q x j - vinogradovPowerSumMod Q y j)) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simpa [sub_eq_add_neg] using vinogradovTuplePhaseMod_sub_eq Q a x y

/-- A complete average over all coefficient vectors factors into one
orthogonality sum for each degree. -/
theorem sum_stdAddChar_coefficient_pairing (Q : ℕ) [NeZero Q] {k : ℕ}
    (d : Fin k → ZMod Q) :
    ∑ a : Fin k → ZMod Q,
        ZMod.stdAddChar (∑ j : Fin k, a j * d j) =
      ∏ j : Fin k, ∑ r : ZMod Q, ZMod.stdAddChar (r * d j) := by
  classical
  rw [Fintype.prod_sum]
  apply Fintype.sum_congr
  intro a
  simpa using
    (prod_stdAddChar_eq_sum Q (Finset.univ : Finset (Fin k))
      (fun j ↦ a j * d j)).symm

/-- The normalized coefficient average of one tuple pair is exactly the
finite Fourier solution selector. -/
theorem normalized_sum_tuplePair_eq_selector (Q k s X : ℕ) [NeZero Q]
    (x y : Fin s → Fin X) :
    (Q : ℂ)⁻¹ ^ k *
        ∑ a : Fin k → ZMod Q,
          (ZMod.stdAddChar (vinogradovTuplePhaseMod Q a x) *
            ZMod.stdAddChar (-vinogradovTuplePhaseMod Q a y)) =
      vinogradovSolutionSelector Q k s X x y := by
  simp_rw [stdAddChar_tuple_mul_neg_tuple]
  rw [sum_stdAddChar_coefficient_pairing]
  simp [vinogradovSolutionSelector, Finset.prod_mul_distrib]

/-- The normalized complete `2s`-th moment of the finite Weyl sums. -/
noncomputable def normalizedVinogradovMomentMod (Q k s X : ℕ) [NeZero Q] : ℂ :=
  (Q : ℂ)⁻¹ ^ k * ∑ a : Fin k → ZMod Q,
    vinogradovWeylSumMod Q k X a ^ s *
      (starRingEnd ℂ) (vinogradovWeylSumMod Q k X a) ^ s

private theorem normalizedMoment_reindex (Q k s X : ℕ) [NeZero Q] :
    normalizedVinogradovMomentMod Q k s X =
      ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
        ((Q : ℂ)⁻¹ ^ k *
          ∑ a : Fin k → ZMod Q,
            (ZMod.stdAddChar (vinogradovTuplePhaseMod Q a x) *
              ZMod.stdAddChar (-vinogradovTuplePhaseMod Q a y))) := by
  classical
  unfold normalizedVinogradovMomentMod
  simp_rw [vinogradovWeylSumMod_pow, conj_vinogradovWeylSumMod_pow]
  calc
    (Q : ℂ)⁻¹ ^ k *
          ∑ a : Fin k → ZMod Q,
            ((∑ x : Fin s → Fin X,
                ZMod.stdAddChar (vinogradovTuplePhaseMod Q a x)) *
              ∑ y : Fin s → Fin X,
                ZMod.stdAddChar (-vinogradovTuplePhaseMod Q a y)) =
        ∑ a : Fin k → ZMod Q, ∑ x : Fin s → Fin X,
          ∑ y : Fin s → Fin X,
            (Q : ℂ)⁻¹ ^ k *
              (ZMod.stdAddChar (vinogradovTuplePhaseMod Q a x) *
                ZMod.stdAddChar (-vinogradovTuplePhaseMod Q a y)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Fintype.sum_congr
      intro a
      rw [Finset.sum_comm]
    _ = ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
          ∑ a : Fin k → ZMod Q,
            (Q : ℂ)⁻¹ ^ k *
              (ZMod.stdAddChar (vinogradovTuplePhaseMod Q a x) *
                ZMod.stdAddChar (-vinogradovTuplePhaseMod Q a y)) := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro x
      rw [Finset.sum_comm]
    _ = ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
          (Q : ℂ)⁻¹ ^ k *
            ∑ a : Fin k → ZMod Q,
              (ZMod.stdAddChar (vinogradovTuplePhaseMod Q a x) *
                ZMod.stdAddChar (-vinogradovTuplePhaseMod Q a y)) := by
      simp only [Finset.mul_sum]

/-- Finite Vinogradov mean-value identity: the normalized complete `2s`-th
moment of the polynomial Weyl sums equals the number of modular solutions of
the degree-`k` Vinogradov system. -/
theorem normalizedVinogradovMomentMod_eq_solutionCount
    (Q k s X : ℕ) [NeZero Q] :
    normalizedVinogradovMomentMod Q k s X =
      (vinogradovSolutionCountMod Q k s X : ℂ) := by
  rw [normalizedMoment_reindex]
  simp_rw [normalized_sum_tuplePair_eq_selector]
  exact sum_vinogradovSolutionSelector_eq_count Q k s X

end

end ZeroFreeRegion.VinogradovKorobov
