import HardyTheorem.SelbergSqrtZetaSignedModelL2
import HardyTheorem.SelbergSqrtZetaSignedRationalGapBudget

/-!
# Arithmetic decomposition of the signed model L2 budget

The real-frequency diagonal-plus-gap budget is exactly the rational collected
coefficient energy, multiplied by the interval length, plus the reciprocal
logarithmic gap budget.  This identity is diagnostic: the global energy retains
a nonzero main term, while the gap budget takes absolute values and discards
the phase cancellation needed at the short-window scale.  The Selberg route
therefore continues through the exact Hermitian short kernel, not by forcing
these two global positive quantities to be logarithmically small.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

/-- Exact arithmetic decomposition of the signed model L2 budget. -/
theorem selbergSqrtZetaSignedModelL2Budget_eq_rational_energy_add_gap
    (T : ℝ) (X : ℕ) :
    selbergSqrtZetaSignedModelL2Budget T X =
      T *
          ∑ q ∈ selbergSqrtZetaSignedRationalSupport
              (firstZetaApproximationCutoff T) X,
            Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff
                (firstZetaApproximationCutoff T) X q) +
        selbergSqrtZetaSignedRationalGapBudget
          (firstZetaApproximationCutoff T) X 0 := by
  classical
  let N : ℕ := firstZetaApproximationCutoff T
  let Q : Finset ℚ := selbergSqrtZetaSignedRationalSupport N X
  let frequency : ℚ → ℝ := selbergSqrtZetaSignedRationalFrequency
  let coeff : ℚ → ℂ := selbergSqrtZetaSignedRationalCoeff N X
  have hinj : Set.InjOn frequency (Q : Set ℚ) := by
    simpa only [Q, frequency] using
      selbergSqrtZetaSignedRationalFrequency_injOn N X
  rw [selbergSqrtZetaSignedModelL2Budget,
    ← image_rationalFrequency_rationalSupport N X]
  change
    (∑ omega ∈ Q.image frequency,
      ∑ nu ∈ Q.image frequency,
        if omega = nu then
          T * Complex.normSq
            (selbergSqrtZetaSignedCollectedCoeff N X nu)
        else
          2 *
              ‖selbergSqrtZetaSignedCollectedCoeff N X omega‖ *
              ‖selbergSqrtZetaSignedCollectedCoeff N X nu‖ /
            |omega - nu|) =
      T * ∑ q ∈ Q, Complex.normSq (coeff q) +
        selbergSqrtZetaSignedRationalGapBudget N X 0
  rw [Finset.sum_image hinj]
  unfold selbergSqrtZetaSignedRationalGapBudget
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_image hinj]
  change
    (∑ r ∈ Q,
      if frequency q = frequency r then
        T * Complex.normSq
          (selbergSqrtZetaSignedCollectedCoeff N X (frequency r))
      else
        2 *
            ‖selbergSqrtZetaSignedCollectedCoeff N X (frequency q)‖ *
            ‖selbergSqrtZetaSignedCollectedCoeff N X (frequency r)‖ /
          |frequency q - frequency r|) =
      T * Complex.normSq (coeff q) +
        ∑ r ∈ Q,
          if q = r then 0
          else
            ‖coeff q‖ * ‖coeff r‖ *
              ((2 + 0 / 2) /
                |Real.log ((q : ℝ) / (r : ℝ))|)
  have hdiag :
      T * Complex.normSq (coeff q) =
        ∑ r ∈ Q,
          if q = r then T * Complex.normSq (coeff r) else 0 := by
    symm
    exact Finset.sum_ite_eq_of_mem Q q
      (fun r => T * Complex.normSq (coeff r)) hq
  rw [hdiag, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hfrequencyEq : frequency q = frequency r ↔ q = r := by
    constructor
    · exact fun h => hinj hq hr h
    · exact congrArg frequency
  rw [selbergSqrtZetaSignedCollectedCoeff_rationalFrequency hq,
    selbergSqrtZetaSignedCollectedCoeff_rationalFrequency hr]
  by_cases hqr : q = r
  · subst r
    simp [coeff]
  · have hfreqNe : frequency q ≠ frequency r := by
      exact fun h => hqr (hfrequencyEq.mp h)
    rw [if_neg hfreqNe, if_neg hqr]
    rw [selbergSqrtZetaSignedRationalFrequency_sub_eq_log_div hq hr]
    simp only [hqr, if_false]
    dsimp only [coeff]
    ring

end HardyTheorem
