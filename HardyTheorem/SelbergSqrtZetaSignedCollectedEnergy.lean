import HardyTheorem.SelbergSqrtZetaSignedCollectedGapBound
import MathlibAux.CollectedCoefficientEnergy

/-!
# Energy of the collected signed square-root-zeta coefficients

This specializes the generic frequency-fiber Cauchy--Schwarz estimate to the
actual finite signed square-root-zeta phase model.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

/-- The collected square energy is controlled by the exact multiplicities
and raw square energies of the signed frequency fibers. -/
theorem
    sum_normSq_selbergSqrtZetaSignedCollectedCoeff_le_fiber_budget
    (N X : ℕ) :
    (∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        Complex.normSq
          (selbergSqrtZetaSignedCollectedCoeff N X omega)) ≤
      ∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        (((selbergSqrtZetaSignedPhaseSupport N X).filter
          (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega)).card : ℝ) *
        ∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
          (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega),
          Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p) := by
  simpa only [selbergSqrtZetaSignedCollectedFrequencySupport,
    selbergSqrtZetaSignedCollectedCoeff] using
    (MathlibAux.sum_normSq_collectedCoefficient_le_fiber_budget
      (selbergSqrtZetaSignedPhaseSupport N X)
      (selbergSqrtZetaSignedPhaseCoeff X)
      selbergSqrtZetaSignedPhaseFrequency)

/-- The norm of the same-frequency correlation block is at most the total
square energy of the collected coefficients. -/
theorem norm_selbergSqrtZetaSignedCollectedCorrelationDiagonal_le_energy
    (T : ℝ) (X : ℕ) (v w : ℝ) :
    ‖selbergSqrtZetaSignedCollectedCorrelationDiagonal T X v w‖ ≤
      ∑ omega ∈
          selbergSqrtZetaSignedCollectedFrequencySupport
            (firstZetaApproximationCutoff T) X,
        Complex.normSq
          (selbergSqrtZetaSignedCollectedCoeff
            (firstZetaApproximationCutoff T) X omega) := by
  unfold selbergSqrtZetaSignedCollectedCorrelationDiagonal
  calc
    ‖∑ omega ∈
        selbergSqrtZetaSignedCollectedFrequencySupport
          (firstZetaApproximationCutoff T) X,
        selbergSqrtZetaSignedCollectedCoeff
            (firstZetaApproximationCutoff T) X omega *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedCollectedCoeff
              (firstZetaApproximationCutoff T) X omega) *
          Complex.exp (I * ((omega * v - omega * w : ℝ) : ℂ))‖ ≤
      ∑ omega ∈
        selbergSqrtZetaSignedCollectedFrequencySupport
          (firstZetaApproximationCutoff T) X,
        ‖selbergSqrtZetaSignedCollectedCoeff
            (firstZetaApproximationCutoff T) X omega *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedCollectedCoeff
              (firstZetaApproximationCutoff T) X omega) *
          Complex.exp (I * ((omega * v - omega * w : ℝ) : ℂ))‖ :=
      norm_sum_le _ _
    _ = ∑ omega ∈
        selbergSqrtZetaSignedCollectedFrequencySupport
          (firstZetaApproximationCutoff T) X,
        Complex.normSq
          (selbergSqrtZetaSignedCollectedCoeff
            (firstZetaApproximationCutoff T) X omega) := by
      apply Finset.sum_congr rfl
      intro omega homega
      rw [norm_mul, norm_mul, Complex.norm_conj,
        Complex.norm_exp_I_mul_ofReal, mul_one,
        Complex.normSq_eq_norm_sq]
      ring

/-- The same-frequency correlation block is therefore bounded by the exact
raw frequency-fiber multiplicity budget. -/
theorem
    norm_selbergSqrtZetaSignedCollectedCorrelationDiagonal_le_fiber_budget
    (T : ℝ) (X : ℕ) (v w : ℝ) :
    ‖selbergSqrtZetaSignedCollectedCorrelationDiagonal T X v w‖ ≤
      ∑ omega ∈
          selbergSqrtZetaSignedCollectedFrequencySupport
            (firstZetaApproximationCutoff T) X,
        (((selbergSqrtZetaSignedPhaseSupport
            (firstZetaApproximationCutoff T) X).filter
          (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega)).card : ℝ) *
        ∑ p ∈
            (selbergSqrtZetaSignedPhaseSupport
              (firstZetaApproximationCutoff T) X).filter
              (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega),
          Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p) := by
  exact
    (norm_selbergSqrtZetaSignedCollectedCorrelationDiagonal_le_energy
      T X v w).trans
      (sum_normSq_selbergSqrtZetaSignedCollectedCoeff_le_fiber_budget
        (firstZetaApproximationCutoff T) X)

end HardyTheorem
