import ZeroFreeRegion.VinogradovKorobov.VinogradovIncompleteMoment

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance incompleteSupportPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Retained power sum for an arbitrary finite alphabet carrying values in
`ZMod Q`.  This is the support-independent core needed for sparse sets of
integers. -/
def incompletePowerSumOnMod
    (Q h : ℕ) {ι : Type*} [Fintype ι]
    (value : ι → ZMod Q) {d s : ℕ}
    (x : Fin s → ι) (j : Fin d) : ZMod Q :=
  ∑ i, value (x i) ^ (h + j.val)

/-- Incomplete Vinogradov equations on an arbitrary finite valued alphabet. -/
def IsIncompleteSolutionOnMod
    (Q h d s : ℕ) {ι : Type*} [Fintype ι]
    (value : ι → ZMod Q) (x y : Fin s → ι) : Prop :=
  ∀ j : Fin d,
    incompletePowerSumOnMod Q h value x j =
      incompletePowerSumOnMod Q h value y j

/-- Number of ordered solutions on an arbitrary finite valued alphabet. -/
noncomputable def incompleteSolutionCountOnMod
    (Q h d s : ℕ) {ι : Type*} [Fintype ι]
    (value : ι → ZMod Q) : ℕ :=
  ∑ x : Fin s → ι,
    (Finset.univ.filter fun y : Fin s → ι ↦
      IsIncompleteSolutionOnMod Q h d s value x y).card

/-- Fourier selector for incomplete equations on a finite valued alphabet. -/
noncomputable def incompleteSolutionSelectorOnMod
    (Q h d s : ℕ) {ι : Type*} [Fintype ι] [NeZero Q]
    (value : ι → ZMod Q) (x y : Fin s → ι) : ℂ :=
  ∏ j : Fin d,
    ((Q : ℂ)⁻¹ * ∑ a : ZMod Q,
      ZMod.stdAddChar
        (a * (incompletePowerSumOnMod Q h value x j -
          incompletePowerSumOnMod Q h value y j)))

/-- The arbitrary-support selector is exactly the solution indicator. -/
theorem incompleteSolutionSelectorOnMod_eq_indicator
    (Q h d s : ℕ) {ι : Type*} [Fintype ι] [NeZero Q]
    (value : ι → ZMod Q) (x y : Fin s → ι) :
    incompleteSolutionSelectorOnMod Q h d s value x y =
      if IsIncompleteSolutionOnMod Q h d s value x y then 1 else 0 := by
  classical
  simp only [incompleteSolutionSelectorOnMod,
    normalized_sum_stdAddChar_mul]
  by_cases hxy : IsIncompleteSolutionOnMod Q h d s value x y
  · rw [if_pos hxy]
    apply Finset.prod_eq_one
    intro j hj
    rw [if_pos]
    exact sub_eq_zero.mpr (hxy j)
  · rw [if_neg hxy]
    simp only [IsIncompleteSolutionOnMod, not_forall] at hxy
    obtain ⟨j, hj⟩ := hxy
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [if_neg]
    exact sub_ne_zero.mpr hj

/-- Summing the arbitrary-support selector counts its solutions. -/
theorem sum_incompleteSolutionSelectorOnMod_eq_count
    (Q h d s : ℕ) {ι : Type*} [Fintype ι] [NeZero Q]
    (value : ι → ZMod Q) :
    ∑ x : Fin s → ι, ∑ y : Fin s → ι,
      incompleteSolutionSelectorOnMod Q h d s value x y =
        (incompleteSolutionCountOnMod Q h d s value : ℂ) := by
  classical
  simp_rw [incompleteSolutionSelectorOnMod_eq_indicator]
  simp [incompleteSolutionCountOnMod, Finset.sum_boole]

/-- Polynomial phase on one element of an arbitrary finite alphabet. -/
def incompletePhaseOnMod
    (Q h : ℕ) {ι : Type*} [Fintype ι]
    (value : ι → ZMod Q) {d : ℕ}
    (a : Fin d → ZMod Q) (n : ι) : ZMod Q :=
  ∑ j : Fin d, a j * value n ^ (h + j.val)

/-- Incomplete Weyl sum over an arbitrary finite alphabet. -/
noncomputable def incompleteWeylSumOnMod
    (Q h d : ℕ) {ι : Type*} [Fintype ι] [NeZero Q]
    (value : ι → ZMod Q) (a : Fin d → ZMod Q) : ℂ :=
  ∑ n : ι, ZMod.stdAddChar (incompletePhaseOnMod Q h value a n)

/-- Trivial cardinality bound for an incomplete Weyl sum on any finite
alphabet. -/
theorem norm_incompleteWeylSumOnMod_le_card
    (Q h d : ℕ) {ι : Type*} [Fintype ι] [NeZero Q]
    (value : ι → ZMod Q) (a : Fin d → ZMod Q) :
    ‖incompleteWeylSumOnMod Q h d value a‖ ≤ Fintype.card ι := by
  unfold incompleteWeylSumOnMod
  calc
    ‖∑ n : ι, ZMod.stdAddChar (incompletePhaseOnMod Q h value a n)‖ ≤
        ∑ n : ι,
          ‖ZMod.stdAddChar (incompletePhaseOnMod Q h value a n)‖ :=
      norm_sum_le _ _
    _ = Fintype.card ι := by simp

/-- Tuple phase over an arbitrary finite alphabet. -/
def incompleteTuplePhaseOnMod
    (Q h : ℕ) {ι : Type*} [Fintype ι]
    (value : ι → ZMod Q) {d s : ℕ}
    (a : Fin d → ZMod Q) (x : Fin s → ι) : ZMod Q :=
  ∑ i : Fin s, incompletePhaseOnMod Q h value a (x i)

/-- The arbitrary-support tuple phase is the coefficient pairing with its
retained power sums. -/
theorem incompleteTuplePhaseOnMod_eq_sum_powerSum
    (Q h : ℕ) {ι : Type*} [Fintype ι]
    (value : ι → ZMod Q) {d s : ℕ}
    (a : Fin d → ZMod Q) (x : Fin s → ι) :
    incompleteTuplePhaseOnMod Q h value a x =
      ∑ j : Fin d, a j * incompletePowerSumOnMod Q h value x j := by
  classical
  unfold incompleteTuplePhaseOnMod incompletePhaseOnMod
    incompletePowerSumOnMod
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j
  rw [Finset.mul_sum]

/-- Difference form of the arbitrary-support tuple pairing. -/
theorem incompleteTuplePhaseOnMod_sub_eq
    (Q h : ℕ) {ι : Type*} [Fintype ι]
    (value : ι → ZMod Q) {d s : ℕ}
    (a : Fin d → ZMod Q) (x y : Fin s → ι) :
    incompleteTuplePhaseOnMod Q h value a x -
        incompleteTuplePhaseOnMod Q h value a y =
      ∑ j : Fin d, a j *
        (incompletePowerSumOnMod Q h value x j -
          incompletePowerSumOnMod Q h value y j) := by
  rw [incompleteTuplePhaseOnMod_eq_sum_powerSum,
    incompleteTuplePhaseOnMod_eq_sum_powerSum,
    ← Finset.sum_sub_distrib]
  apply Fintype.sum_congr
  intro j
  ring

/-- Tuple and conjugate tuple characters combine into the arbitrary-support
coefficient pairing. -/
theorem stdAddChar_incompleteTupleOn_mul_neg_tuple
    (Q h : ℕ) {ι : Type*} [Fintype ι] [NeZero Q]
    (value : ι → ZMod Q) {d s : ℕ}
    (a : Fin d → ZMod Q) (x y : Fin s → ι) :
    ZMod.stdAddChar (incompleteTuplePhaseOnMod Q h value a x) *
        ZMod.stdAddChar (-incompleteTuplePhaseOnMod Q h value a y) =
      ZMod.stdAddChar
        (∑ j : Fin d, a j *
          (incompletePowerSumOnMod Q h value x j -
            incompletePowerSumOnMod Q h value y j)) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simpa [sub_eq_add_neg] using
    incompleteTuplePhaseOnMod_sub_eq Q h value a x y

/-- Normalized coefficient average of one arbitrary-support tuple pair. -/
theorem normalized_sum_incompleteTuplePairOn_eq_selector
    (Q h d s : ℕ) {ι : Type*} [Fintype ι] [NeZero Q]
    (value : ι → ZMod Q) (x y : Fin s → ι) :
    (Q : ℂ)⁻¹ ^ d *
        ∑ a : Fin d → ZMod Q,
          (ZMod.stdAddChar
              (incompleteTuplePhaseOnMod Q h value a x) *
            ZMod.stdAddChar
              (-incompleteTuplePhaseOnMod Q h value a y)) =
      incompleteSolutionSelectorOnMod Q h d s value x y := by
  simp_rw [stdAddChar_incompleteTupleOn_mul_neg_tuple]
  rw [sum_stdAddChar_coefficient_pairing]
  simp [incompleteSolutionSelectorOnMod, Finset.prod_mul_distrib]

/-- Tuple expansion of an arbitrary-support incomplete Weyl sum. -/
theorem incompleteWeylSumOnMod_pow
    (Q h d s : ℕ) {ι : Type*} [Fintype ι] [NeZero Q]
    (value : ι → ZMod Q) (a : Fin d → ZMod Q) :
    incompleteWeylSumOnMod Q h d value a ^ s =
      ∑ x : Fin s → ι,
        ZMod.stdAddChar
          (incompleteTuplePhaseOnMod Q h value a x) := by
  classical
  rw [incompleteWeylSumOnMod, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro x
  simpa [incompleteTuplePhaseOnMod] using
    (prod_stdAddChar_eq_sum Q (Finset.univ : Finset (Fin s))
      (fun i ↦ incompletePhaseOnMod Q h value a (x i)))

/-- Conjugate tuple expansion on an arbitrary finite alphabet. -/
theorem conj_incompleteWeylSumOnMod_pow
    (Q h d s : ℕ) {ι : Type*} [Fintype ι] [NeZero Q]
    (value : ι → ZMod Q) (a : Fin d → ZMod Q) :
    (starRingEnd ℂ) (incompleteWeylSumOnMod Q h d value a) ^ s =
      ∑ y : Fin s → ι,
        ZMod.stdAddChar
          (-incompleteTuplePhaseOnMod Q h value a y) := by
  rw [← map_pow, incompleteWeylSumOnMod_pow, map_sum]
  apply Fintype.sum_congr
  intro y
  exact conj_stdAddChar Q _

/-- Normalized incomplete moment on an arbitrary finite valued alphabet. -/
noncomputable def normalizedIncompleteMomentOnMod
    (Q h d s : ℕ) {ι : Type*} [Fintype ι] [NeZero Q]
    (value : ι → ZMod Q) : ℂ :=
  (Q : ℂ)⁻¹ ^ d * ∑ a : Fin d → ZMod Q,
    incompleteWeylSumOnMod Q h d value a ^ s *
      (starRingEnd ℂ) (incompleteWeylSumOnMod Q h d value a) ^ s

private theorem normalizedIncompleteMomentOn_reindex
    (Q h d s : ℕ) {ι : Type*} [Fintype ι] [NeZero Q]
    (value : ι → ZMod Q) :
    normalizedIncompleteMomentOnMod Q h d s value =
      ∑ x : Fin s → ι, ∑ y : Fin s → ι,
        ((Q : ℂ)⁻¹ ^ d *
          ∑ a : Fin d → ZMod Q,
            (ZMod.stdAddChar
                (incompleteTuplePhaseOnMod Q h value a x) *
              ZMod.stdAddChar
                (-incompleteTuplePhaseOnMod Q h value a y))) := by
  classical
  unfold normalizedIncompleteMomentOnMod
  simp_rw [incompleteWeylSumOnMod_pow, conj_incompleteWeylSumOnMod_pow]
  calc
    (Q : ℂ)⁻¹ ^ d *
          ∑ a : Fin d → ZMod Q,
            ((∑ x : Fin s → ι,
                ZMod.stdAddChar
                  (incompleteTuplePhaseOnMod Q h value a x)) *
              ∑ y : Fin s → ι,
                ZMod.stdAddChar
                  (-incompleteTuplePhaseOnMod Q h value a y)) =
        ∑ a : Fin d → ZMod Q, ∑ x : Fin s → ι,
          ∑ y : Fin s → ι,
            (Q : ℂ)⁻¹ ^ d *
              (ZMod.stdAddChar
                  (incompleteTuplePhaseOnMod Q h value a x) *
                ZMod.stdAddChar
                  (-incompleteTuplePhaseOnMod Q h value a y)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Fintype.sum_congr
      intro a
      rw [Finset.sum_comm]
    _ = ∑ x : Fin s → ι, ∑ y : Fin s → ι,
          ∑ a : Fin d → ZMod Q,
            (Q : ℂ)⁻¹ ^ d *
              (ZMod.stdAddChar
                  (incompleteTuplePhaseOnMod Q h value a x) *
                ZMod.stdAddChar
                  (-incompleteTuplePhaseOnMod Q h value a y)) := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro x
      rw [Finset.sum_comm]
    _ = ∑ x : Fin s → ι, ∑ y : Fin s → ι,
          (Q : ℂ)⁻¹ ^ d *
            ∑ a : Fin d → ZMod Q,
              (ZMod.stdAddChar
                  (incompleteTuplePhaseOnMod Q h value a x) *
                ZMod.stdAddChar
                  (-incompleteTuplePhaseOnMod Q h value a y)) := by
      simp only [Finset.mul_sum]

/-- Arbitrary-support finite Fourier identity: the normalized incomplete
moment equals its exact solution count. -/
theorem normalizedIncompleteMomentOnMod_eq_solutionCount
    (Q h d s : ℕ) {ι : Type*} [Fintype ι] [NeZero Q]
    (value : ι → ZMod Q) :
    normalizedIncompleteMomentOnMod Q h d s value =
      (incompleteSolutionCountOnMod Q h d s value : ℂ) := by
  rw [normalizedIncompleteMomentOn_reindex]
  simp_rw [normalized_sum_incompleteTuplePairOn_eq_selector]
  exact sum_incompleteSolutionSelectorOnMod_eq_count Q h d s value

/-- The incomplete solution count is at most the number of all ordered tuple
pairs on the finite alphabet. -/
theorem incompleteSolutionCountOnMod_le_total
    (Q h d s : ℕ) {ι : Type*} [Fintype ι]
    (value : ι → ZMod Q) :
    incompleteSolutionCountOnMod Q h d s value ≤
      Fintype.card ι ^ (2 * s) := by
  classical
  unfold incompleteSolutionCountOnMod
  calc
    ∑ x : Fin s → ι,
        ((Finset.univ.filter fun y : Fin s → ι ↦
          IsIncompleteSolutionOnMod Q h d s value x y).card) ≤
        ∑ _x : Fin s → ι, Fintype.card (Fin s → ι) := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card ι ^ (2 * s) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fun, Fintype.card_fin]
      change Fintype.card ι ^ s * Fintype.card ι ^ s =
        Fintype.card ι ^ (2 * s)
      rw [← pow_add]
      congr 2
      omega

/-- Standard interval alphabet used by the original incomplete moment. -/
def vinogradovIntervalValueMod (Q X : ℕ) : Fin X → ZMod Q :=
  fun n ↦ ((n.val + 1 : ℕ) : ZMod Q)

/-- The arbitrary-alphabet power sum specializes to the interval model. -/
theorem incompletePowerSumOnMod_interval_eq
    (Q h : ℕ) {d s X : ℕ}
    (x : Fin s → Fin X) (j : Fin d) :
    incompletePowerSumOnMod Q h (vinogradovIntervalValueMod Q X) x j =
      incompleteVinogradovPowerSumMod Q h x j := by
  simp [incompletePowerSumOnMod, incompleteVinogradovPowerSumMod,
    vinogradovIntervalValueMod, Nat.cast_add, Nat.cast_one]

/-- The arbitrary-alphabet phase specializes to the interval phase. -/
theorem incompletePhaseOnMod_interval_eq
    (Q h : ℕ) {d X : ℕ}
    (a : Fin d → ZMod Q) (n : Fin X) :
    incompletePhaseOnMod Q h (vinogradovIntervalValueMod Q X) a n =
      incompleteVinogradovPhaseMod Q h a n := by
  simp [incompletePhaseOnMod, incompleteVinogradovPhaseMod,
    vinogradovIntervalValueMod, Nat.cast_add, Nat.cast_one]

/-- The arbitrary-alphabet Weyl sum specializes to the interval Weyl sum. -/
theorem incompleteWeylSumOnMod_interval_eq
    (Q h d X : ℕ) [NeZero Q] (a : Fin d → ZMod Q) :
    incompleteWeylSumOnMod Q h d (vinogradovIntervalValueMod Q X) a =
      incompleteVinogradovWeylSumMod Q h d X a := by
  simp [incompleteWeylSumOnMod, incompleteVinogradovWeylSumMod,
    incompletePhaseOnMod_interval_eq]

/-- The arbitrary-alphabet normalized moment specializes exactly to the
previous full-interval incomplete moment. -/
theorem normalizedIncompleteMomentOnMod_interval_eq
    (Q h d s X : ℕ) [NeZero Q] :
    normalizedIncompleteMomentOnMod Q h d s
        (vinogradovIntervalValueMod Q X) =
      normalizedIncompleteVinogradovMomentMod Q h d s X := by
  simp [normalizedIncompleteMomentOnMod,
    normalizedIncompleteVinogradovMomentMod,
    incompleteWeylSumOnMod_interval_eq]

/-- Values of an arbitrary finite support `B ⊆ {1, ..., X}` reduced modulo
`Q`.  Multiplicity is absent because `B` is a finset. -/
def vinogradovSupportValueMod
    (Q : ℕ) {X : ℕ} (B : Finset (Fin X)) : ↥B → ZMod Q :=
  fun n ↦ ((n.1.val + 1 : ℕ) : ZMod Q)

/-- Incomplete equations with every variable restricted to the support `B`. -/
abbrev IsIncompleteVinogradovSupportSolutionMod
    (Q h d s X : ℕ) (B : Finset (Fin X))
    (x y : Fin s → ↥B) : Prop :=
  IsIncompleteSolutionOnMod Q h d s
    (vinogradovSupportValueMod Q B) x y

/-- Exact solution count on an arbitrary finite support. -/
noncomputable abbrev incompleteVinogradovSupportSolutionCountMod
    (Q h d s X : ℕ) (B : Finset (Fin X)) : ℕ :=
  incompleteSolutionCountOnMod Q h d s
    (vinogradovSupportValueMod Q B)

/-- Incomplete Weyl sum with its variables restricted to `B`. -/
noncomputable abbrev incompleteVinogradovSupportWeylSumMod
    (Q h d X : ℕ) [NeZero Q] (B : Finset (Fin X))
    (a : Fin d → ZMod Q) : ℂ :=
  incompleteWeylSumOnMod Q h d (vinogradovSupportValueMod Q B) a

/-- A support-restricted incomplete Weyl sum is bounded by the support
cardinality. -/
theorem norm_incompleteVinogradovSupportWeylSumMod_le_card
    (Q h d X : ℕ) [NeZero Q] (B : Finset (Fin X))
    (a : Fin d → ZMod Q) :
    ‖incompleteVinogradovSupportWeylSumMod Q h d X B a‖ ≤ B.card := by
  simpa using norm_incompleteWeylSumOnMod_le_card
    Q h d (vinogradovSupportValueMod Q B) a

/-- Normalized incomplete moment on an arbitrary finite support `B`. -/
noncomputable abbrev normalizedIncompleteVinogradovSupportMomentMod
    (Q h d s X : ℕ) [NeZero Q] (B : Finset (Fin X)) : ℂ :=
  normalizedIncompleteMomentOnMod Q h d s
    (vinogradovSupportValueMod Q B)

/-- Exact orthogonality identity on an arbitrary finite support. -/
theorem normalizedIncompleteVinogradovSupportMomentMod_eq_solutionCount
    (Q h d s X : ℕ) [NeZero Q] (B : Finset (Fin X)) :
    normalizedIncompleteVinogradovSupportMomentMod Q h d s X B =
      (incompleteVinogradovSupportSolutionCountMod Q h d s X B : ℂ) :=
  normalizedIncompleteMomentOnMod_eq_solutionCount Q h d s
    (vinogradovSupportValueMod Q B)

/-- The number of incomplete solutions supported on `B` is at most
`|B|^(2s)`. -/
theorem incompleteVinogradovSupportSolutionCountMod_le_total
    (Q h d s X : ℕ) (B : Finset (Fin X)) :
    incompleteVinogradovSupportSolutionCountMod Q h d s X B ≤
      B.card ^ (2 * s) := by
  simpa using incompleteSolutionCountOnMod_le_total Q h d s
    (vinogradovSupportValueMod Q B)

end

end ZeroFreeRegion.VinogradovKorobov
