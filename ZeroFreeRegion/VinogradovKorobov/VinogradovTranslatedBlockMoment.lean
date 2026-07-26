import ZeroFreeRegion.VinogradovKorobov.VinogradovCompleteBlockMain
import ZeroFreeRegion.VinogradovKorobov.VinogradovModularSymmetry
import ZeroFreeRegion.VinogradovKorobov.VinogradovSolutionLifting

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The `j`-th power sum on the translated interval
`{m + 1, ..., m + X}`, reduced modulo `Q`. -/
def vinogradovTranslatedPowerSumMod (Q m : ℕ) {k s X : ℕ}
    (x : Fin s → Fin X) (j : Fin k) : ZMod Q :=
  ∑ i, ((m + (x i).val + 1 : ℕ) : ZMod Q) ^ (j.val + 1)

/-- A tuple pair solves the modular Vinogradov system on the translated
interval `{m + 1, ..., m + X}`. -/
def IsVinogradovTranslatedSolutionMod (Q m k s X : ℕ)
    (x y : Fin s → Fin X) : Prop :=
  ∀ j : Fin k,
    vinogradovTranslatedPowerSumMod Q m x j =
      vinogradovTranslatedPowerSumMod Q m y j

local instance translatedSolutionDecidable
    (Q m k s X : ℕ) (x y : Fin s → Fin X) :
    Decidable (IsVinogradovTranslatedSolutionMod Q m k s X x y) :=
  Classical.propDecidable _

/-- The number of ordered modular Vinogradov solutions on a translated
interval. -/
noncomputable def vinogradovTranslatedSolutionCountMod
    (Q m k s X : ℕ) : ℕ := by
  classical
  exact ∑ x : Fin s → Fin X,
    (Finset.univ.filter fun y : Fin s → Fin X ↦
      IsVinogradovTranslatedSolutionMod Q m k s X x y).card

/-- The translated polynomial phase modulo `Q`. -/
def vinogradovTranslatedPhaseMod (Q m : ℕ) {k X : ℕ}
    (a : Fin k → ZMod Q) (n : Fin X) : ZMod Q :=
  ∑ j : Fin k,
    a j * ((m + n.val + 1 : ℕ) : ZMod Q) ^ (j.val + 1)

/-- The complete Weyl sum on `{m + 1, ..., m + X}`. -/
noncomputable def vinogradovTranslatedWeylSumMod
    (Q m k X : ℕ) [NeZero Q] (a : Fin k → ZMod Q) : ℂ :=
  ∑ n : Fin X, ZMod.stdAddChar (vinogradovTranslatedPhaseMod Q m a n)

/-- The phase accumulated along a tuple in the translated interval. -/
def vinogradovTranslatedTuplePhaseMod
    (Q m : ℕ) {k s X : ℕ}
    (a : Fin k → ZMod Q) (x : Fin s → Fin X) : ZMod Q :=
  ∑ i : Fin s, vinogradovTranslatedPhaseMod Q m a (x i)

/-- The normalized complete `2s`-th moment of translated Weyl sums. -/
noncomputable def normalizedTranslatedVinogradovMomentMod
    (Q m k s X : ℕ) [NeZero Q] : ℂ :=
  (Q : ℂ)⁻¹ ^ k * ∑ a : Fin k → ZMod Q,
    vinogradovTranslatedWeylSumMod Q m k X a ^ s *
      (starRingEnd ℂ) (vinogradovTranslatedWeylSumMod Q m k X a) ^ s

theorem vinogradovTranslatedTuplePhaseMod_eq_sum_powerSum
    (Q m : ℕ) {k s X : ℕ}
    (a : Fin k → ZMod Q) (x : Fin s → Fin X) :
    vinogradovTranslatedTuplePhaseMod Q m a x =
      ∑ j : Fin k,
        a j * vinogradovTranslatedPowerSumMod Q m x j := by
  classical
  unfold vinogradovTranslatedTuplePhaseMod vinogradovTranslatedPhaseMod
    vinogradovTranslatedPowerSumMod
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j
  rw [Finset.mul_sum]

theorem vinogradovTranslatedTuplePhaseMod_sub_eq
    (Q m : ℕ) {k s X : ℕ}
    (a : Fin k → ZMod Q) (x y : Fin s → Fin X) :
    vinogradovTranslatedTuplePhaseMod Q m a x -
        vinogradovTranslatedTuplePhaseMod Q m a y =
      ∑ j : Fin k, a j *
        (vinogradovTranslatedPowerSumMod Q m x j -
          vinogradovTranslatedPowerSumMod Q m y j) := by
  rw [vinogradovTranslatedTuplePhaseMod_eq_sum_powerSum,
    vinogradovTranslatedTuplePhaseMod_eq_sum_powerSum,
    ← Finset.sum_sub_distrib]
  apply Fintype.sum_congr
  intro j
  ring

theorem stdAddChar_translatedTuple_mul_neg_tuple
    (Q m : ℕ) [NeZero Q] {k s X : ℕ}
    (a : Fin k → ZMod Q) (x y : Fin s → Fin X) :
    ZMod.stdAddChar (vinogradovTranslatedTuplePhaseMod Q m a x) *
        ZMod.stdAddChar (-vinogradovTranslatedTuplePhaseMod Q m a y) =
      ZMod.stdAddChar
        (∑ j : Fin k, a j *
          (vinogradovTranslatedPowerSumMod Q m x j -
            vinogradovTranslatedPowerSumMod Q m y j)) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simpa [sub_eq_add_neg] using
    vinogradovTranslatedTuplePhaseMod_sub_eq Q m a x y

/-- The Fourier selector for the translated system. -/
noncomputable def vinogradovTranslatedSolutionSelector
    (Q m k s X : ℕ) [NeZero Q]
    (x y : Fin s → Fin X) : ℂ :=
  ∏ j : Fin k,
    ((Q : ℂ)⁻¹ * ∑ a : ZMod Q,
      ZMod.stdAddChar
        (a * (vinogradovTranslatedPowerSumMod Q m x j -
          vinogradovTranslatedPowerSumMod Q m y j)))

theorem vinogradovTranslatedSolutionSelector_eq_indicator
    (Q m k s X : ℕ) [NeZero Q]
    (x y : Fin s → Fin X) :
    vinogradovTranslatedSolutionSelector Q m k s X x y =
      if IsVinogradovTranslatedSolutionMod Q m k s X x y then 1 else 0 := by
  classical
  simp only [vinogradovTranslatedSolutionSelector,
    normalized_sum_stdAddChar_mul]
  by_cases h : IsVinogradovTranslatedSolutionMod Q m k s X x y
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro j hj
    rw [if_pos]
    exact sub_eq_zero.mpr (h j)
  · rw [if_neg h]
    simp only [IsVinogradovTranslatedSolutionMod, not_forall] at h
    obtain ⟨j, hj⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [if_neg]
    exact sub_ne_zero.mpr hj

theorem normalized_sum_translatedTuplePair_eq_selector
    (Q m k s X : ℕ) [NeZero Q]
    (x y : Fin s → Fin X) :
    (Q : ℂ)⁻¹ ^ k *
        ∑ a : Fin k → ZMod Q,
          (ZMod.stdAddChar (vinogradovTranslatedTuplePhaseMod Q m a x) *
            ZMod.stdAddChar
              (-vinogradovTranslatedTuplePhaseMod Q m a y)) =
      vinogradovTranslatedSolutionSelector Q m k s X x y := by
  simp_rw [stdAddChar_translatedTuple_mul_neg_tuple]
  rw [sum_stdAddChar_coefficient_pairing]
  simp [vinogradovTranslatedSolutionSelector, Finset.prod_mul_distrib]

theorem sum_vinogradovTranslatedSolutionSelector_eq_count
    (Q m k s X : ℕ) [NeZero Q] :
    ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
      vinogradovTranslatedSolutionSelector Q m k s X x y =
        (vinogradovTranslatedSolutionCountMod Q m k s X : ℂ) := by
  classical
  simp_rw [vinogradovTranslatedSolutionSelector_eq_indicator]
  simp [vinogradovTranslatedSolutionCountMod, Finset.sum_boole]

theorem vinogradovTranslatedWeylSumMod_pow
    (Q m k s X : ℕ) [NeZero Q]
    (a : Fin k → ZMod Q) :
    vinogradovTranslatedWeylSumMod Q m k X a ^ s =
      ∑ x : Fin s → Fin X,
        ZMod.stdAddChar (vinogradovTranslatedTuplePhaseMod Q m a x) := by
  classical
  rw [vinogradovTranslatedWeylSumMod, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro x
  simpa [vinogradovTranslatedTuplePhaseMod] using
    (prod_stdAddChar_eq_sum Q (Finset.univ : Finset (Fin s))
      (fun i ↦ vinogradovTranslatedPhaseMod Q m a (x i)))

theorem conj_vinogradovTranslatedWeylSumMod_pow
    (Q m k s X : ℕ) [NeZero Q]
    (a : Fin k → ZMod Q) :
    (starRingEnd ℂ) (vinogradovTranslatedWeylSumMod Q m k X a) ^ s =
      ∑ y : Fin s → Fin X,
        ZMod.stdAddChar (-vinogradovTranslatedTuplePhaseMod Q m a y) := by
  rw [← map_pow, vinogradovTranslatedWeylSumMod_pow, map_sum]
  apply Fintype.sum_congr
  intro y
  exact conj_stdAddChar Q _

private theorem normalizedTranslatedMoment_reindex
    (Q m k s X : ℕ) [NeZero Q] :
    normalizedTranslatedVinogradovMomentMod Q m k s X =
      ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
        ((Q : ℂ)⁻¹ ^ k *
          ∑ a : Fin k → ZMod Q,
            (ZMod.stdAddChar
                (vinogradovTranslatedTuplePhaseMod Q m a x) *
              ZMod.stdAddChar
                (-vinogradovTranslatedTuplePhaseMod Q m a y))) := by
  classical
  unfold normalizedTranslatedVinogradovMomentMod
  simp_rw [vinogradovTranslatedWeylSumMod_pow,
    conj_vinogradovTranslatedWeylSumMod_pow]
  calc
    (Q : ℂ)⁻¹ ^ k *
          ∑ a : Fin k → ZMod Q,
            ((∑ x : Fin s → Fin X,
                ZMod.stdAddChar
                  (vinogradovTranslatedTuplePhaseMod Q m a x)) *
              ∑ y : Fin s → Fin X,
                ZMod.stdAddChar
                  (-vinogradovTranslatedTuplePhaseMod Q m a y)) =
        ∑ a : Fin k → ZMod Q, ∑ x : Fin s → Fin X,
          ∑ y : Fin s → Fin X,
            (Q : ℂ)⁻¹ ^ k *
              (ZMod.stdAddChar
                  (vinogradovTranslatedTuplePhaseMod Q m a x) *
                ZMod.stdAddChar
                  (-vinogradovTranslatedTuplePhaseMod Q m a y)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Fintype.sum_congr
      intro a
      rw [Finset.sum_comm]
    _ = ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
          ∑ a : Fin k → ZMod Q,
            (Q : ℂ)⁻¹ ^ k *
              (ZMod.stdAddChar
                  (vinogradovTranslatedTuplePhaseMod Q m a x) *
                ZMod.stdAddChar
                  (-vinogradovTranslatedTuplePhaseMod Q m a y)) := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro x
      rw [Finset.sum_comm]
    _ = ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
          (Q : ℂ)⁻¹ ^ k *
            ∑ a : Fin k → ZMod Q,
              (ZMod.stdAddChar
                  (vinogradovTranslatedTuplePhaseMod Q m a x) *
                ZMod.stdAddChar
                  (-vinogradovTranslatedTuplePhaseMod Q m a y)) := by
      simp only [Finset.mul_sum]

/-- The normalized translated Weyl moment counts translated modular
Vinogradov solutions exactly. -/
theorem normalizedTranslatedVinogradovMomentMod_eq_solutionCount
    (Q m k s X : ℕ) [NeZero Q] :
    normalizedTranslatedVinogradovMomentMod Q m k s X =
      (vinogradovTranslatedSolutionCountMod Q m k s X : ℂ) := by
  rw [normalizedTranslatedMoment_reindex]
  simp_rw [normalized_sum_translatedTuplePair_eq_selector]
  exact sum_vinogradovTranslatedSolutionSelector_eq_count Q m k s X

private theorem isVinogradovTranslatedSolutionMod_iff_intMod
    (Q m k s X : ℕ) (x y : Fin s → Fin X) :
    IsVinogradovTranslatedSolutionMod Q m k s X x y ↔
      IsVinogradovSolutionIntMod Q k s
        (fun i ↦ (((m + (x i).val + 1 : ℕ) : ℕ) : ℤ))
        (fun i ↦ (((m + (y i).val + 1 : ℕ) : ℕ) : ℤ)) := by
  constructor
  · intro h j
    apply (ZMod.intCast_eq_intCast_iff _ _ Q).mp
    simpa [vinogradovPowerSumInt, vinogradovTranslatedPowerSumMod] using h j
  · intro h j
    have hj := (ZMod.intCast_eq_intCast_iff _ _ Q).mpr (h j)
    simpa [vinogradovPowerSumInt, vinogradovTranslatedPowerSumMod] using hj

/-- Translating the underlying complete interval preserves the modular
Vinogradov solution predicate. -/
theorem isVinogradovTranslatedSolutionMod_iff_unshifted
    (Q m k s X : ℕ) (x y : Fin s → Fin X) :
    IsVinogradovTranslatedSolutionMod Q m k s X x y ↔
      IsVinogradovSolutionMod Q k s X x y := by
  rw [isVinogradovTranslatedSolutionMod_iff_intMod]
  have htranslate :=
    isVinogradovSolutionIntMod_translate_iff Q k s
      (fun i ↦ (((x i).val + 1 : ℕ) : ℤ))
      (fun i ↦ (((y i).val + 1 : ℕ) : ℤ)) (m : ℤ)
  have hbase :
      IsVinogradovSolutionIntMod Q k s
          (fun i ↦ (((x i).val + 1 : ℕ) : ℤ))
          (fun i ↦ (((y i).val + 1 : ℕ) : ℤ)) ↔
        IsVinogradovSolutionMod Q k s X x y := by
    simpa [IsVinogradovSolutionIntMod] using
      (isVinogradovSolutionMod_iff_powerSumInt_modEq
        Q k s X x y).symm
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm,
    add_left_comm] using htranslate.trans hbase

/-- The translated and unshifted complete intervals have exactly the same
number of modular Vinogradov solutions. -/
theorem vinogradovTranslatedSolutionCountMod_eq_unshifted
    (Q m k s X : ℕ) :
    vinogradovTranslatedSolutionCountMod Q m k s X =
      vinogradovSolutionCountMod Q k s X := by
  classical
  unfold vinogradovTranslatedSolutionCountMod vinogradovSolutionCountMod
  apply Finset.sum_congr rfl
  intro x hx
  apply congrArg Finset.card
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact isVinogradovTranslatedSolutionMod_iff_unshifted
    Q m k s X x y

/-- Every translated complete Weyl moment equals the corresponding
unshifted moment. -/
theorem normalizedTranslatedVinogradovMomentMod_eq_unshifted
    (Q m k s X : ℕ) [NeZero Q] :
    normalizedTranslatedVinogradovMomentMod Q m k s X =
      normalizedVinogradovMomentMod Q k s X := by
  rw [normalizedTranslatedVinogradovMomentMod_eq_solutionCount,
    vinogradovTranslatedSolutionCountMod_eq_unshifted,
    normalizedVinogradovMomentMod_eq_solutionCount]

/-- The fixed-scale complete-block saving is uniform in the starting point
of the interval. -/
theorem
    norm_normalizedTranslatedVinogradovMomentMod_sq_le_primeCubic_completeBlockSaving
    (p m k r q : ℕ) [Fact p.Prime]
    (hr : 0 < r) (hq : 0 < q) (hqk : q ≤ k) (hqp : q < p)
    (hbudget : 3 * q + 1 ≤ 2 * (k - r + 1)) :
    ‖normalizedTranslatedVinogradovMomentMod
        (p ^ ((k - r + 1) * 2)) m k (r + q) (p ^ 2 * p)‖ ^ 2 ≤
      (q.factorial : ℝ) * (p : ℝ) ^ (12 * r + 11 * q) := by
  rw [normalizedTranslatedVinogradovMomentMod_eq_unshifted]
  exact
    norm_normalizedVinogradovMomentMod_sq_le_primeCubic_completeBlockSaving
      p k r q hr hq hqk hqp hbudget

end

end ZeroFreeRegion.VinogradovKorobov
