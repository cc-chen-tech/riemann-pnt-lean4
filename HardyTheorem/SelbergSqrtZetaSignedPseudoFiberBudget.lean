import HardyTheorem.SelbergSqrtZetaSignedPseudoShiftBudget
import HardyTheorem.SelbergSqrtZetaSignedCollectedL1

/-!
# Frequency-fiber budget for the shift-averaged pseudo-correlation

The shift-averaged pseudo-correlation estimate initially contains the square
of the collected coefficient `L1` norm. This module composes that analytic
estimate with the finite Cauchy--Schwarz and frequency-fiber energy bounds.
The resulting right-hand side is a purely finite arithmetic budget.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

/-- The full shift-averaged pseudo-correlation is controlled by the number
of distinct collected frequencies and the exact raw frequency-fiber
multiplicity energy. -/
theorem
    norm_integral_integral_integral_selbergSqrtZetaSignedComplexModel_mul_shift_le_fiber_budget
    (kappa : ℝ) {T delta : ℝ} (X : ℕ)
    (hT : 1 ≤ T) (hdelta : 0 ≤ delta) (hroom : delta ≤ T) :
    ‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          selbergSqrtZetaSignedComplexModel kappa T X (t + w)‖ ≤
      delta ^ 2 *
        ((12 * Real.sqrt (4 * T)) *
          ((selbergSqrtZetaSignedCollectedFrequencySupport
            (firstZetaApproximationCutoff T) X).card : ℝ) *
          ∑ omega ∈
              selbergSqrtZetaSignedCollectedFrequencySupport
                (firstZetaApproximationCutoff T) X,
            (((selbergSqrtZetaSignedPhaseSupport
                (firstZetaApproximationCutoff T) X).filter
              (fun p =>
                selbergSqrtZetaSignedPhaseFrequency p = omega)).card : ℝ) *
            ∑ p ∈
                (selbergSqrtZetaSignedPhaseSupport
                  (firstZetaApproximationCutoff T) X).filter
                (fun p =>
                  selbergSqrtZetaSignedPhaseFrequency p = omega),
              Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p)) := by
  have hC : 0 ≤ 12 * Real.sqrt (4 * T) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  exact
    (norm_integral_integral_integral_selbergSqrtZetaSignedComplexModel_mul_shift_le
      kappa X hT hdelta hroom).trans
      (mul_le_mul_of_nonneg_left
        (sum_sum_mul_norm_selbergSqrtZetaSignedCollectedCoeff_le_fiber_budget
          (firstZetaApproximationCutoff T) X hC)
        (sq_nonneg delta))

end HardyTheorem
