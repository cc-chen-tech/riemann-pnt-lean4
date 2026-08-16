import ZeroFreeRegion.VinogradovKorobov.VinogradovMoment

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance incompleteMomentPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The power sum at the actual exponent `h + j`, where `j` ranges through a
window of `d` consecutive degrees. -/
def incompleteVinogradovPowerSumMod (Q h : ℕ) {d s X : ℕ}
    (x : Fin s → Fin X) (j : Fin d) : ZMod Q :=
  ∑ i, ((x i).val + 1 : ZMod Q) ^ (h + j.val)

/-- A pair of tuples solves the incomplete Vinogradov system consisting only
of the consecutive equations of degrees `h, ..., h + d - 1`. -/
def IsIncompleteVinogradovSolutionMod (Q h d s X : ℕ)
    (x y : Fin s → Fin X) : Prop :=
  ∀ j : Fin d,
    incompleteVinogradovPowerSumMod Q h x j =
      incompleteVinogradovPowerSumMod Q h y j

/-- Number of ordered modular solutions of a consecutive incomplete
Vinogradov system. -/
noncomputable def incompleteVinogradovSolutionCountMod
    (Q h d s X : ℕ) : ℕ :=
  ∑ x : Fin s → Fin X,
    (Finset.univ.filter fun y : Fin s → Fin X ↦
      IsIncompleteVinogradovSolutionMod Q h d s X x y).card

/-- Fourier selector for an incomplete Vinogradov system. -/
noncomputable def incompleteVinogradovSolutionSelector
    (Q h d s X : ℕ) [NeZero Q]
    (x y : Fin s → Fin X) : ℂ :=
  ∏ j : Fin d,
    ((Q : ℂ)⁻¹ * ∑ a : ZMod Q,
      ZMod.stdAddChar
        (a * (incompleteVinogradovPowerSumMod Q h x j -
          incompleteVinogradovPowerSumMod Q h y j)))

/-- The incomplete Fourier selector is the indicator of the retained
high-degree equations. -/
theorem incompleteVinogradovSolutionSelector_eq_indicator
    (Q h d s X : ℕ) [NeZero Q]
    (x y : Fin s → Fin X) :
    incompleteVinogradovSolutionSelector Q h d s X x y =
      if IsIncompleteVinogradovSolutionMod Q h d s X x y then 1 else 0 := by
  classical
  simp only [incompleteVinogradovSolutionSelector,
    normalized_sum_stdAddChar_mul]
  by_cases hxy : IsIncompleteVinogradovSolutionMod Q h d s X x y
  · rw [if_pos hxy]
    apply Finset.prod_eq_one
    intro j hj
    rw [if_pos]
    exact sub_eq_zero.mpr (hxy j)
  · rw [if_neg hxy]
    simp only [IsIncompleteVinogradovSolutionMod, not_forall] at hxy
    obtain ⟨j, hj⟩ := hxy
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [if_neg]
    exact sub_ne_zero.mpr hj

/-- Summing the incomplete selector over both tuples gives its modular
solution count. -/
private theorem sum_incompleteVinogradovSolutionSelector_eq_count
    (Q h d s X : ℕ) [NeZero Q] :
    ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
      incompleteVinogradovSolutionSelector Q h d s X x y =
        (incompleteVinogradovSolutionCountMod Q h d s X : ℂ) := by
  classical
  simp_rw [incompleteVinogradovSolutionSelector_eq_indicator]
  simp [incompleteVinogradovSolutionCountMod, Finset.sum_boole]

/-- Polynomial phase whose coefficient vector occupies only the consecutive
degrees `h, ..., h + d - 1`. -/
def incompleteVinogradovPhaseMod (Q h : ℕ) {d X : ℕ}
    (a : Fin d → ZMod Q) (n : Fin X) : ZMod Q :=
  ∑ j : Fin d,
    a j * ((n.val + 1 : ℕ) : ZMod Q) ^ (h + j.val)

/-- Finite Weyl sum for a consecutive incomplete polynomial phase. -/
noncomputable def incompleteVinogradovWeylSumMod
    (Q h d X : ℕ) [NeZero Q]
    (a : Fin d → ZMod Q) : ℂ :=
  ∑ n : Fin X, ZMod.stdAddChar (incompleteVinogradovPhaseMod Q h a n)

/-- Incomplete phase accumulated along an ordered tuple. -/
def incompleteVinogradovTuplePhaseMod (Q h : ℕ) {d s X : ℕ}
    (a : Fin d → ZMod Q) (x : Fin s → Fin X) : ZMod Q :=
  ∑ i : Fin s, incompleteVinogradovPhaseMod Q h a (x i)

/-- The incomplete tuple phase is the coefficient pairing with the retained
power-sum window. -/
private theorem incompleteVinogradovTuplePhaseMod_eq_sum_powerSum
    (Q h : ℕ) {d s X : ℕ}
    (a : Fin d → ZMod Q) (x : Fin s → Fin X) :
    incompleteVinogradovTuplePhaseMod Q h a x =
      ∑ j : Fin d,
        a j * incompleteVinogradovPowerSumMod Q h x j := by
  classical
  unfold incompleteVinogradovTuplePhaseMod incompleteVinogradovPhaseMod
    incompleteVinogradovPowerSumMod
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro i
  simp only [Nat.cast_add, Nat.cast_one]

/-- Pairing an incomplete tuple phase with its conjugate gives the retained
power-sum differences. -/
private theorem incompleteVinogradovTuplePhaseMod_sub_eq
    (Q h : ℕ) {d s X : ℕ}
    (a : Fin d → ZMod Q) (x y : Fin s → Fin X) :
    incompleteVinogradovTuplePhaseMod Q h a x -
        incompleteVinogradovTuplePhaseMod Q h a y =
      ∑ j : Fin d, a j *
        (incompleteVinogradovPowerSumMod Q h x j -
          incompleteVinogradovPowerSumMod Q h y j) := by
  rw [incompleteVinogradovTuplePhaseMod_eq_sum_powerSum,
    incompleteVinogradovTuplePhaseMod_eq_sum_powerSum,
    ← Finset.sum_sub_distrib]
  apply Fintype.sum_congr
  intro j
  ring

/-- Tuple and conjugate-tuple characters combine into the incomplete
coefficient pairing. -/
private theorem stdAddChar_incompleteTuple_mul_neg_tuple
    (Q h : ℕ) [NeZero Q] {d s X : ℕ}
    (a : Fin d → ZMod Q) (x y : Fin s → Fin X) :
    ZMod.stdAddChar (incompleteVinogradovTuplePhaseMod Q h a x) *
        ZMod.stdAddChar (-incompleteVinogradovTuplePhaseMod Q h a y) =
      ZMod.stdAddChar
        (∑ j : Fin d, a j *
          (incompleteVinogradovPowerSumMod Q h x j -
            incompleteVinogradovPowerSumMod Q h y j)) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simpa [sub_eq_add_neg] using
    incompleteVinogradovTuplePhaseMod_sub_eq Q h a x y

/-- The normalized coefficient average of one tuple pair is the incomplete
solution selector. -/
private theorem normalized_sum_incompleteTuplePair_eq_selector
    (Q h d s X : ℕ) [NeZero Q]
    (x y : Fin s → Fin X) :
    (Q : ℂ)⁻¹ ^ d *
        ∑ a : Fin d → ZMod Q,
          (ZMod.stdAddChar (incompleteVinogradovTuplePhaseMod Q h a x) *
            ZMod.stdAddChar
              (-incompleteVinogradovTuplePhaseMod Q h a y)) =
      incompleteVinogradovSolutionSelector Q h d s X x y := by
  simp_rw [stdAddChar_incompleteTuple_mul_neg_tuple]
  rw [sum_stdAddChar_coefficient_pairing]
  simp [incompleteVinogradovSolutionSelector, Finset.prod_mul_distrib]

/-- Expanding an incomplete Weyl sum power produces one term for every
ordered tuple. -/
private theorem incompleteVinogradovWeylSumMod_pow
    (Q h d s X : ℕ) [NeZero Q]
    (a : Fin d → ZMod Q) :
    incompleteVinogradovWeylSumMod Q h d X a ^ s =
      ∑ x : Fin s → Fin X,
        ZMod.stdAddChar (incompleteVinogradovTuplePhaseMod Q h a x) := by
  classical
  rw [incompleteVinogradovWeylSumMod, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro x
  simpa [incompleteVinogradovTuplePhaseMod] using
    (prod_stdAddChar_eq_sum Q (Finset.univ : Finset (Fin s))
      (fun i ↦ incompleteVinogradovPhaseMod Q h a (x i)))

/-- Conjugate power expansion for an incomplete Weyl sum. -/
private theorem conj_incompleteVinogradovWeylSumMod_pow
    (Q h d s X : ℕ) [NeZero Q]
    (a : Fin d → ZMod Q) :
    (starRingEnd ℂ) (incompleteVinogradovWeylSumMod Q h d X a) ^ s =
      ∑ y : Fin s → Fin X,
        ZMod.stdAddChar
          (-incompleteVinogradovTuplePhaseMod Q h a y) := by
  rw [← map_pow, incompleteVinogradovWeylSumMod_pow, map_sum]
  apply Fintype.sum_congr
  intro y
  exact conj_stdAddChar Q _

/-- Normalized `2s`-th moment for the consecutive incomplete degree window. -/
noncomputable def normalizedIncompleteVinogradovMomentMod
    (Q h d s X : ℕ) [NeZero Q] : ℂ :=
  (Q : ℂ)⁻¹ ^ d * ∑ a : Fin d → ZMod Q,
    incompleteVinogradovWeylSumMod Q h d X a ^ s *
      (starRingEnd ℂ) (incompleteVinogradovWeylSumMod Q h d X a) ^ s

private theorem normalizedIncompleteMoment_reindex
    (Q h d s X : ℕ) [NeZero Q] :
    normalizedIncompleteVinogradovMomentMod Q h d s X =
      ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
        ((Q : ℂ)⁻¹ ^ d *
          ∑ a : Fin d → ZMod Q,
            (ZMod.stdAddChar
                (incompleteVinogradovTuplePhaseMod Q h a x) *
              ZMod.stdAddChar
                (-incompleteVinogradovTuplePhaseMod Q h a y))) := by
  classical
  unfold normalizedIncompleteVinogradovMomentMod
  simp_rw [incompleteVinogradovWeylSumMod_pow,
    conj_incompleteVinogradovWeylSumMod_pow]
  calc
    (Q : ℂ)⁻¹ ^ d *
          ∑ a : Fin d → ZMod Q,
            ((∑ x : Fin s → Fin X,
                ZMod.stdAddChar
                  (incompleteVinogradovTuplePhaseMod Q h a x)) *
              ∑ y : Fin s → Fin X,
                ZMod.stdAddChar
                  (-incompleteVinogradovTuplePhaseMod Q h a y)) =
        ∑ a : Fin d → ZMod Q, ∑ x : Fin s → Fin X,
          ∑ y : Fin s → Fin X,
            (Q : ℂ)⁻¹ ^ d *
              (ZMod.stdAddChar
                  (incompleteVinogradovTuplePhaseMod Q h a x) *
                ZMod.stdAddChar
                  (-incompleteVinogradovTuplePhaseMod Q h a y)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Fintype.sum_congr
      intro a
      rw [Finset.sum_comm]
    _ = ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
          ∑ a : Fin d → ZMod Q,
            (Q : ℂ)⁻¹ ^ d *
              (ZMod.stdAddChar
                  (incompleteVinogradovTuplePhaseMod Q h a x) *
                ZMod.stdAddChar
                  (-incompleteVinogradovTuplePhaseMod Q h a y)) := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro x
      rw [Finset.sum_comm]
    _ = ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
          (Q : ℂ)⁻¹ ^ d *
            ∑ a : Fin d → ZMod Q,
              (ZMod.stdAddChar
                  (incompleteVinogradovTuplePhaseMod Q h a x) *
                ZMod.stdAddChar
                  (-incompleteVinogradovTuplePhaseMod Q h a y)) := by
      simp only [Finset.mul_sum]

/-- Finite orthogonality identity for an incomplete Vinogradov system. -/
theorem normalizedIncompleteVinogradovMomentMod_eq_solutionCount
    (Q h d s X : ℕ) [NeZero Q] :
    normalizedIncompleteVinogradovMomentMod Q h d s X =
      (incompleteVinogradovSolutionCountMod Q h d s X : ℂ) := by
  rw [normalizedIncompleteMoment_reindex]
  simp_rw [normalized_sum_incompleteTuplePair_eq_selector]
  exact sum_incompleteVinogradovSolutionSelector_eq_count Q h d s X

/-- The degree window beginning at one is the existing complete system. -/
private theorem incompleteVinogradovPowerSumMod_one_eq
    (Q : ℕ) {k s X : ℕ} (x : Fin s → Fin X) (j : Fin k) :
    incompleteVinogradovPowerSumMod Q 1 x j =
      vinogradovPowerSumMod Q x j := by
  simp [incompleteVinogradovPowerSumMod, vinogradovPowerSumMod,
    Nat.add_comm]

/-- Complete and incomplete solution predicates agree for the window
`1, ..., k`. -/
theorem isIncompleteVinogradovSolutionMod_one_iff
    (Q k s X : ℕ) (x y : Fin s → Fin X) :
    IsIncompleteVinogradovSolutionMod Q 1 k s X x y ↔
      IsVinogradovSolutionMod Q k s X x y := by
  simp only [IsIncompleteVinogradovSolutionMod, IsVinogradovSolutionMod,
    incompleteVinogradovPowerSumMod_one_eq]

/-- The incomplete solution count recovers the complete count at start
degree one. -/
theorem incompleteVinogradovSolutionCountMod_one_eq
    (Q k s X : ℕ) :
    incompleteVinogradovSolutionCountMod Q 1 k s X =
      vinogradovSolutionCountMod Q k s X := by
  classical
  unfold incompleteVinogradovSolutionCountMod vinogradovSolutionCountMod
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    isIncompleteVinogradovSolutionMod_one_iff]

/-- The incomplete phase beginning at degree one is the complete phase. -/
private theorem incompleteVinogradovPhaseMod_one_eq
    (Q : ℕ) {k X : ℕ} (a : Fin k → ZMod Q) (n : Fin X) :
    incompleteVinogradovPhaseMod Q 1 a n =
      vinogradovPhaseMod Q a n := by
  simp [incompleteVinogradovPhaseMod, vinogradovPhaseMod, Nat.add_comm]

/-- The incomplete Weyl sum beginning at degree one is the complete Weyl
sum. -/
private theorem incompleteVinogradovWeylSumMod_one_eq
    (Q k X : ℕ) [NeZero Q] (a : Fin k → ZMod Q) :
    incompleteVinogradovWeylSumMod Q 1 k X a =
      vinogradovWeylSumMod Q k X a := by
  simp [incompleteVinogradovWeylSumMod, vinogradovWeylSumMod,
    incompleteVinogradovPhaseMod_one_eq]

/-- The incomplete normalized moment recovers the complete normalized moment
at start degree one. -/
theorem normalizedIncompleteVinogradovMomentMod_one_eq
    (Q k s X : ℕ) [NeZero Q] :
    normalizedIncompleteVinogradovMomentMod Q 1 k s X =
      normalizedVinogradovMomentMod Q k s X := by
  simp [normalizedIncompleteVinogradovMomentMod,
    normalizedVinogradovMomentMod,
    incompleteVinogradovWeylSumMod_one_eq]

/-- Every complete degree-`k` solution solves each consecutive incomplete
window lying inside `1, ..., k`. -/
theorem IsVinogradovSolutionMod.toIncomplete
    {Q k h d s X : ℕ} {x y : Fin s → Fin X}
    (hxy : IsVinogradovSolutionMod Q k s X x y)
    (hh : 1 ≤ h) (hwindow : h + d ≤ k + 1) :
    IsIncompleteVinogradovSolutionMod Q h d s X x y := by
  intro j
  let j' : Fin k := ⟨h + j.val - 1, by omega⟩
  have hj := hxy j'
  have hexponent : j'.val + 1 = h + j.val := by
    dsimp only [j']
    omega
  simpa [incompleteVinogradovPowerSumMod, vinogradovPowerSumMod,
    hexponent] using hj

/-- Dropping equations can only increase the modular solution count. -/
theorem vinogradovSolutionCountMod_le_incomplete
    (Q k h d s X : ℕ)
    (hh : 1 ≤ h) (hwindow : h + d ≤ k + 1) :
    vinogradovSolutionCountMod Q k s X ≤
      incompleteVinogradovSolutionCountMod Q h d s X := by
  classical
  unfold vinogradovSolutionCountMod incompleteVinogradovSolutionCountMod
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  exact hy.toIncomplete hh hwindow

end

end ZeroFreeRegion.VinogradovKorobov
