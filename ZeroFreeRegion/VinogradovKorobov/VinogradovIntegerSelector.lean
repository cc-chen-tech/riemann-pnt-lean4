import ZeroFreeRegion.VinogradovKorobov.VinogradovMoment
import ZeroFreeRegion.VinogradovKorobov.VinogradovModularSymmetry
import ZeroFreeRegion.VinogradovKorobov.VinogradovSolutionLifting

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The `j+1`-st power sum of an arbitrary integer tuple, reduced modulo
`Q`. -/
def vinogradovIntPowerSumMod
    (Q : ℕ) {k s : ℕ} (x : Fin s → ℤ) (j : Fin k) : ZMod Q :=
  ∑ i, (x i : ZMod Q) ^ (j.val + 1)

/-- The common-modulus integer Vinogradov predicate is equivalent to equality
of all reduced power sums. -/
theorem isVinogradovSolutionIntMod_iff_powerSumMod
    (Q k s : ℕ) (x y : Fin s → ℤ) :
    IsVinogradovSolutionIntMod Q k s x y ↔
      ∀ j : Fin k,
        vinogradovIntPowerSumMod Q x j = vinogradovIntPowerSumMod Q y j := by
  constructor
  · intro h j
    have hj := (ZMod.intCast_eq_intCast_iff
      (vinogradovPowerSumInt x j) (vinogradovPowerSumInt y j) Q).mpr (h j)
    simpa [vinogradovIntPowerSumMod, vinogradovPowerSumInt] using hj
  · intro h j
    apply (ZMod.intCast_eq_intCast_iff
      (vinogradovPowerSumInt x j) (vinogradovPowerSumInt y j) Q).mp
    simpa [vinogradovIntPowerSumMod, vinogradovPowerSumInt] using h j

/-- The integer modular Vinogradov predicate is decidable through its finite
system of reduced power-sum equations. -/
instance instDecidableIsVinogradovSolutionIntMod
    (Q k s : ℕ) (x y : Fin s → ℤ) :
    Decidable (IsVinogradovSolutionIntMod Q k s x y) :=
  decidable_of_iff
    (∀ j : Fin k,
      vinogradovIntPowerSumMod Q x j = vinogradovIntPowerSumMod Q y j)
    (isVinogradovSolutionIntMod_iff_powerSumMod Q k s x y).symm

/-- Product of normalized character averages detecting the common-modulus
Vinogradov equations for an arbitrary integer tuple pair. -/
noncomputable def vinogradovIntSolutionSelector
    (Q k s : ℕ) [NeZero Q] (x y : Fin s → ℤ) : ℂ :=
  ∏ j : Fin k,
    ((Q : ℂ)⁻¹ * ∑ a : ZMod Q,
      ZMod.stdAddChar
        (a * (vinogradovIntPowerSumMod Q x j -
          vinogradovIntPowerSumMod Q y j)))

/-- The arbitrary-integer Fourier selector is exactly the indicator of the
common-modulus Vinogradov system. -/
theorem vinogradovIntSolutionSelector_eq_indicator
    (Q k s : ℕ) [NeZero Q] (x y : Fin s → ℤ) :
    vinogradovIntSolutionSelector Q k s x y =
      if IsVinogradovSolutionIntMod Q k s x y then 1 else 0 := by
  classical
  simp only [vinogradovIntSolutionSelector, normalized_sum_stdAddChar_mul]
  by_cases h : IsVinogradovSolutionIntMod Q k s x y
  · rw [if_pos h]
    have hmod := (isVinogradovSolutionIntMod_iff_powerSumMod Q k s x y).mp h
    apply Finset.prod_eq_one
    intro j hj
    rw [if_pos]
    exact sub_eq_zero.mpr (hmod j)
  · rw [if_neg h]
    have hmod : ¬ ∀ j : Fin k,
        vinogradovIntPowerSumMod Q x j = vinogradovIntPowerSumMod Q y j := by
      intro hall
      exact h ((isVinogradovSolutionIntMod_iff_powerSumMod Q k s x y).mpr hall)
    simp only [not_forall] at hmod
    obtain ⟨j, hj⟩ := hmod
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [if_neg]
    exact sub_ne_zero.mpr hj

/-- The polynomial phase with a finite coefficient vector, evaluated at an
arbitrary integer. -/
def vinogradovIntPhaseMod (Q : ℕ) {k : ℕ}
    (a : Fin k → ZMod Q) (n : ℤ) : ZMod Q :=
  ∑ j : Fin k, a j * (n : ZMod Q) ^ (j.val + 1)

/-- The accumulated polynomial phase along an arbitrary integer tuple. -/
def vinogradovIntTuplePhaseMod (Q : ℕ) {k s : ℕ}
    (a : Fin k → ZMod Q) (x : Fin s → ℤ) : ZMod Q :=
  ∑ i : Fin s, vinogradovIntPhaseMod Q a (x i)

/-- The integer tuple phase is the coefficient pairing with its reduced
power-sum vector. -/
theorem vinogradovIntTuplePhaseMod_eq_sum_powerSum
    (Q : ℕ) {k s : ℕ} (a : Fin k → ZMod Q) (x : Fin s → ℤ) :
    vinogradovIntTuplePhaseMod Q a x =
      ∑ j : Fin k, a j * vinogradovIntPowerSumMod Q x j := by
  classical
  unfold vinogradovIntTuplePhaseMod vinogradovIntPhaseMod
    vinogradovIntPowerSumMod
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j
  rw [Finset.mul_sum]

/-- The accumulated phase splits additively across joined tuple blocks. -/
theorem vinogradovIntTuplePhaseMod_joinTuple
    (Q : ℕ) {k r t : ℕ} (a : Fin k → ZMod Q)
    (head : Fin r → ℤ) (tail : Fin t → ℤ) :
    vinogradovIntTuplePhaseMod Q a (vinogradovJoinTuple head tail) =
      vinogradovIntTuplePhaseMod Q a head +
        vinogradovIntTuplePhaseMod Q a tail := by
  unfold vinogradovIntTuplePhaseMod
  rw [← finSumFinEquiv.sum_comp
    (fun i ↦ vinogradovIntPhaseMod Q a
      (vinogradovJoinTuple head tail i))]
  rw [Fintype.sum_sum_type]
  simp [vinogradovJoinTuple]

/-- A finite Weyl sum whose index set is mapped to arbitrary integer values. -/
noncomputable def vinogradovIntWeylSum
    (Q k X : ℕ) [NeZero Q] (value : Fin X → ℤ)
    (a : Fin k → ZMod Q) : ℂ :=
  ∑ n : Fin X, ZMod.stdAddChar (vinogradovIntPhaseMod Q a (value n))

/-- Expanding a power of an arbitrary-integer Weyl sum produces one summand
for every ordered tuple of indices. -/
theorem vinogradovIntWeylSum_pow
    (Q k s X : ℕ) [NeZero Q] (value : Fin X → ℤ)
    (a : Fin k → ZMod Q) :
    vinogradovIntWeylSum Q k X value a ^ s =
      ∑ x : Fin s → Fin X,
        ZMod.stdAddChar
          (vinogradovIntTuplePhaseMod Q a (fun i ↦ value (x i))) := by
  classical
  rw [vinogradovIntWeylSum, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro x
  simpa [vinogradovIntTuplePhaseMod] using
    (prod_stdAddChar_eq_sum Q (Finset.univ : Finset (Fin s))
      (fun i ↦ vinogradovIntPhaseMod Q a (value (x i))))

/-- The conjugate power of an arbitrary-integer Weyl sum expands with the
opposite accumulated phase. -/
theorem conj_vinogradovIntWeylSum_pow
    (Q k s X : ℕ) [NeZero Q] (value : Fin X → ℤ)
    (a : Fin k → ZMod Q) :
    (starRingEnd ℂ) (vinogradovIntWeylSum Q k X value a) ^ s =
      ∑ x : Fin s → Fin X,
        ZMod.stdAddChar
          (-vinogradovIntTuplePhaseMod Q a (fun i ↦ value (x i))) := by
  rw [← map_pow, vinogradovIntWeylSum_pow, map_sum]
  apply Fintype.sum_congr
  intro x
  exact conj_stdAddChar Q _

/-- Pairing an integer tuple with a conjugate tuple produces the coefficient
pairing with their reduced power-sum difference. -/
theorem vinogradovIntTuplePhaseMod_sub_eq
    (Q : ℕ) {k s : ℕ} (a : Fin k → ZMod Q)
    (x y : Fin s → ℤ) :
    vinogradovIntTuplePhaseMod Q a x -
        vinogradovIntTuplePhaseMod Q a y =
      ∑ j : Fin k, a j *
        (vinogradovIntPowerSumMod Q x j -
          vinogradovIntPowerSumMod Q y j) := by
  rw [vinogradovIntTuplePhaseMod_eq_sum_powerSum,
    vinogradovIntTuplePhaseMod_eq_sum_powerSum,
    ← Finset.sum_sub_distrib]
  apply Fintype.sum_congr
  intro j
  ring

/-- The product of the two integer tuple characters is the character of the
coefficient pairing with their power-sum difference. -/
theorem stdAddChar_intTuple_mul_neg_tuple
    (Q : ℕ) [NeZero Q] {k s : ℕ}
    (a : Fin k → ZMod Q) (x y : Fin s → ℤ) :
    ZMod.stdAddChar (vinogradovIntTuplePhaseMod Q a x) *
        ZMod.stdAddChar (-vinogradovIntTuplePhaseMod Q a y) =
      ZMod.stdAddChar
        (∑ j : Fin k, a j *
          (vinogradovIntPowerSumMod Q x j -
            vinogradovIntPowerSumMod Q y j)) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simpa [sub_eq_add_neg] using vinogradovIntTuplePhaseMod_sub_eq Q a x y

/-- The normalized coefficient average of an arbitrary integer tuple pair is
the common-modulus Fourier solution selector. -/
theorem normalized_sum_intTuplePair_eq_selector
    (Q k s : ℕ) [NeZero Q] (x y : Fin s → ℤ) :
    (Q : ℂ)⁻¹ ^ k *
        ∑ a : Fin k → ZMod Q,
          (ZMod.stdAddChar (vinogradovIntTuplePhaseMod Q a x) *
            ZMod.stdAddChar (-vinogradovIntTuplePhaseMod Q a y)) =
      vinogradovIntSolutionSelector Q k s x y := by
  simp_rw [stdAddChar_intTuple_mul_neg_tuple]
  rw [sum_stdAddChar_coefficient_pairing]
  simp [vinogradovIntSolutionSelector, Finset.prod_mul_distrib]

end

end ZeroFreeRegion.VinogradovKorobov
