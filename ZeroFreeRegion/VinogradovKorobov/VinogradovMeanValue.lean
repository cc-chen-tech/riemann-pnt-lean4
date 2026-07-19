import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The `j`-th power sum of a tuple with entries in `{1, ..., X}`, reduced modulo `Q`.
The coordinate `j : Fin k` represents the positive exponent `j + 1`. -/
def vinogradovPowerSumMod (Q : ℕ) {k s X : ℕ}
    (x : Fin s → Fin X) (j : Fin k) : ZMod Q :=
  ∑ i, ((x i).val + 1 : ZMod Q) ^ (j.val + 1)

/-- A pair of tuples solves the degree-`k` Vinogradov system modulo `Q`. -/
def IsVinogradovSolutionMod (Q k s X : ℕ)
    (x y : Fin s → Fin X) : Prop :=
  ∀ j : Fin k,
    vinogradovPowerSumMod Q x j = vinogradovPowerSumMod Q y j

/-- The number of ordered solutions of the degree-`k` Vinogradov system modulo `Q`. -/
noncomputable def vinogradovSolutionCountMod (Q k s X : ℕ) : ℕ :=
  by
    classical
    exact ∑ x : Fin s → Fin X,
      (Finset.univ.filter fun y : Fin s → Fin X ↦
        IsVinogradovSolutionMod Q k s X x y).card

/-- Orthogonality of the standard additive character of `ZMod Q`. -/
theorem sum_stdAddChar_mul (Q : ℕ) [NeZero Q] (a : ZMod Q) :
    ∑ r : ZMod Q, ZMod.stdAddChar (r * a) =
      if a = 0 then (Q : ℂ) else 0 := by
  simpa using
    (AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar Q))

/-- The normalized character average is the indicator of the zero residue. -/
theorem normalized_sum_stdAddChar_mul (Q : ℕ) [NeZero Q] (a : ZMod Q) :
    (Q : ℂ)⁻¹ * ∑ r : ZMod Q, ZMod.stdAddChar (r * a) =
      if a = 0 then 1 else 0 := by
  rw [sum_stdAddChar_mul]
  split_ifs
  · have hQ : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Q)
    field_simp
  · simp

/-- The product of normalized character averages which detects all equations in
the degree-`k` Vinogradov system. -/
noncomputable def vinogradovSolutionSelector (Q k s X : ℕ) [NeZero Q]
    (x y : Fin s → Fin X) : ℂ :=
  ∏ j : Fin k,
    ((Q : ℂ)⁻¹ * ∑ a : ZMod Q,
      ZMod.stdAddChar
        (a * (vinogradovPowerSumMod Q x j -
          vinogradovPowerSumMod Q y j)))

/-- The finite Fourier selector is exactly one on modular Vinogradov solutions
and zero on every other pair of tuples. -/
theorem vinogradovSolutionSelector_eq_indicator (Q k s X : ℕ) [NeZero Q]
    (x y : Fin s → Fin X) :
    vinogradovSolutionSelector Q k s X x y =
      if IsVinogradovSolutionMod Q k s X x y then 1 else 0 := by
  classical
  simp only [vinogradovSolutionSelector, normalized_sum_stdAddChar_mul]
  by_cases h : IsVinogradovSolutionMod Q k s X x y
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro j hj
    rw [if_pos]
    exact sub_eq_zero.mpr (h j)
  · rw [if_neg h]
    simp only [IsVinogradovSolutionMod, not_forall] at h
    obtain ⟨j, hj⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [if_neg]
    exact sub_ne_zero.mpr hj

/-- Summing the Fourier selector over both tuples counts precisely the modular
solutions of the Vinogradov system. -/
theorem sum_vinogradovSolutionSelector_eq_count (Q k s X : ℕ) [NeZero Q] :
    ∑ x : Fin s → Fin X, ∑ y : Fin s → Fin X,
      vinogradovSolutionSelector Q k s X x y =
        (vinogradovSolutionCountMod Q k s X : ℂ) := by
  classical
  simp_rw [vinogradovSolutionSelector_eq_indicator]
  simp [vinogradovSolutionCountMod, Finset.sum_boole]

/-- The polynomial phase with coefficient vector `a`, evaluated at an integer
in `{1, ..., X}` and reduced modulo `Q`. -/
def vinogradovPhaseMod (Q : ℕ) {k X : ℕ}
    (a : Fin k → ZMod Q) (n : Fin X) : ZMod Q :=
  ∑ j : Fin k, a j * ((n.val + 1 : ℕ) : ZMod Q) ^ (j.val + 1)

/-- A complete finite Weyl sum for the Vinogradov polynomial phase modulo `Q`. -/
noncomputable def vinogradovWeylSumMod (Q k X : ℕ) [NeZero Q]
    (a : Fin k → ZMod Q) : ℂ :=
  ∑ n : Fin X, ZMod.stdAddChar (vinogradovPhaseMod Q a n)

/-- The phase accumulated along an `s`-tuple of integers in `{1, ..., X}`. -/
def vinogradovTuplePhaseMod (Q : ℕ) {k s X : ℕ}
    (a : Fin k → ZMod Q) (x : Fin s → Fin X) : ZMod Q :=
  ∑ i : Fin s, vinogradovPhaseMod Q a (x i)

/-- An additive character sends a finite sum to the corresponding finite product. -/
theorem prod_stdAddChar_eq_sum (Q : ℕ) [NeZero Q]
    {ι : Type*} (u : Finset ι) (f : ι → ZMod Q) :
    ∏ i ∈ u, ZMod.stdAddChar (f i) =
      ZMod.stdAddChar (∑ i ∈ u, f i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | @insert a u ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      exact (AddChar.map_add_eq_mul ZMod.stdAddChar (f a) (∑ i ∈ u, f i)).symm

/-- Expanding the `s`-th power of a Weyl sum produces one summand for every
ordered `s`-tuple. -/
theorem vinogradovWeylSumMod_pow (Q k s X : ℕ) [NeZero Q]
    (a : Fin k → ZMod Q) :
    vinogradovWeylSumMod Q k X a ^ s =
      ∑ x : Fin s → Fin X,
        ZMod.stdAddChar (vinogradovTuplePhaseMod Q a x) := by
  classical
  rw [vinogradovWeylSumMod, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro x
  simpa [vinogradovTuplePhaseMod] using
    (prod_stdAddChar_eq_sum Q (Finset.univ : Finset (Fin s))
      (fun i ↦ vinogradovPhaseMod Q a (x i)))

/-- Complex conjugation reverses the standard additive character. -/
theorem conj_stdAddChar (Q : ℕ) [NeZero Q] (z : ZMod Q) :
    (starRingEnd ℂ) (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
  have hQ : 0 < ringChar (ZMod Q) := by
    rw [ZMod.ringChar_zmod_n]
    exact NeZero.pos Q
  simpa [AddChar.inv_apply'] using
    (AddChar.starComp_apply hQ (φ := ZMod.stdAddChar) z)

/-- The conjugate `s`-th power expands over a second tuple with the opposite
accumulated phase. -/
theorem conj_vinogradovWeylSumMod_pow (Q k s X : ℕ) [NeZero Q]
    (a : Fin k → ZMod Q) :
    (starRingEnd ℂ) (vinogradovWeylSumMod Q k X a) ^ s =
      ∑ y : Fin s → Fin X,
        ZMod.stdAddChar (-vinogradovTuplePhaseMod Q a y) := by
  rw [← map_pow, vinogradovWeylSumMod_pow, map_sum]
  apply Fintype.sum_congr
  intro y
  exact conj_stdAddChar Q _

end

end ZeroFreeRegion.VinogradovKorobov
