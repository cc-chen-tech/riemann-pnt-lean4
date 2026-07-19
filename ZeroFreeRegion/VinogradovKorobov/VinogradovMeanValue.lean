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

end

end ZeroFreeRegion.VinogradovKorobov
