import HardyTheorem.SelbergSqrtZetaSignedModelL2
import HardyTheorem.SelbergSqrtZetaSignedRationalFourierTransfer

/-!
# Whole-line energy of the truncated signed phase

The dyadic truncation used by the Fourier transfer vanishes off `[T, 2T]`.
This module identifies its whole-line `L²` energy with the interval energy of
the original complex phase polynomial.  The common Hardy phase has norm one,
so the energy is exactly that of the collected exponential polynomial and is
bounded by the existing diagonal-plus-gap model budget.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-- The whole-line energy of the dyadic truncation is exactly the interval
energy of the original complex phase polynomial. -/
theorem
    integral_normSq_selbergSqrtZetaSignedTruncatedPhase_eq_phasePolynomial
    (T : ℝ) (X : ℕ) (hT : 0 < T) :
    (∫ t : ℝ, Complex.normSq
      (selbergSqrtZetaSignedTruncatedPhase T X t)) =
      ∫ t in T..2 * T, Complex.normSq
        (selbergSqrtZetaSignedPhasePolynomial
          (firstZetaApproximationCutoff T) X t) := by
  let f : ℝ → ℂ :=
    selbergSqrtZetaSignedPhasePolynomial
      (firstZetaApproximationCutoff T) X
  have hTtwo : T ≤ 2 * T := by linarith
  have hindicator :
      (fun t : ℝ => Complex.normSq
          (selbergSqrtZetaSignedTruncatedPhase T X t)) =
        (Icc T (2 * T)).indicator
          (fun t : ℝ => Complex.normSq (f t)) := by
    funext t
    by_cases ht : t ∈ Icc T (2 * T)
    · simp [selbergSqrtZetaSignedTruncatedPhase, f, ht]
    · simp [selbergSqrtZetaSignedTruncatedPhase, f, ht]
  calc
    (∫ t : ℝ, Complex.normSq
        (selbergSqrtZetaSignedTruncatedPhase T X t)) =
        ∫ t : ℝ, (Icc T (2 * T)).indicator
          (fun u : ℝ => Complex.normSq (f u)) t := by
            rw [hindicator]
    _ = ∫ t in Icc T (2 * T), Complex.normSq (f t) :=
      MeasureTheory.integral_indicator measurableSet_Icc
    _ = ∫ t in Ioc T (2 * T), Complex.normSq (f t) :=
      MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ t in T..2 * T, Complex.normSq
        (selbergSqrtZetaSignedPhasePolynomial
          (firstZetaApproximationCutoff T) X t) := by
      rw [intervalIntegral.integral_of_le hTtwo]

/-- Removing the common unit-modulus Hardy phase identifies the same
whole-line energy with the collected collision-free polynomial. -/
theorem
    integral_normSq_selbergSqrtZetaSignedTruncatedPhase_eq_collectedTriplePolynomial
    (T : ℝ) (X : ℕ) (hT : 0 < T) :
    (∫ t : ℝ, Complex.normSq
      (selbergSqrtZetaSignedTruncatedPhase T X t)) =
      ∫ t in T..2 * T, Complex.normSq
        (selbergSqrtZetaSignedCollectedTriplePolynomial
          (firstZetaApproximationCutoff T) X t) := by
  rw [
    integral_normSq_selbergSqrtZetaSignedTruncatedPhase_eq_phasePolynomial
      T X hT]
  apply intervalIntegral.integral_congr
  intro t _ht
  change
    Complex.normSq
        (selbergSqrtZetaSignedPhasePolynomial
          (firstZetaApproximationCutoff T) X t) =
      Complex.normSq
        (selbergSqrtZetaSignedCollectedTriplePolynomial
          (firstZetaApproximationCutoff T) X t)
  rw [
    selbergSqrtZetaSignedPhasePolynomial_eq_exp_mul_collectedTriplePolynomial,
    Complex.normSq_mul]
  have hphase :
      Complex.normSq
          (Complex.exp (I * (thetaModel t : ℂ))) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_I_mul_ofReal]
    norm_num
  rw [hphase, one_mul]

/-- The dyadically truncated complex phase has whole-line energy bounded by
the existing collected-frequency diagonal-plus-gap budget. -/
theorem
    integral_normSq_selbergSqrtZetaSignedTruncatedPhase_le_modelL2Budget
    (T : ℝ) (X : ℕ) (hT : 0 < T) :
    (∫ t : ℝ, Complex.normSq
      (selbergSqrtZetaSignedTruncatedPhase T X t)) ≤
      selbergSqrtZetaSignedModelL2Budget T X := by
  rw [
    integral_normSq_selbergSqrtZetaSignedTruncatedPhase_eq_collectedTriplePolynomial
      T X hT]
  let N : ℕ := firstZetaApproximationCutoff T
  let K : Finset ℝ :=
    selbergSqrtZetaSignedCollectedFrequencySupport N X
  let a : ℝ → ℂ := selbergSqrtZetaSignedCollectedCoeff N X
  let Q : ℝ → ℂ :=
    selbergSqrtZetaSignedCollectedTriplePolynomial N X
  have hbase :=
    MathlibAux.integral_normSq_exponentialPolynomial_le
      K a (fun omega : ℝ => omega)
      (a := T) (b := 2 * T)
      (by
        intro omega homega nu hnu hne
        exact hne)
  simpa only [Q, K, a, N,
    selbergSqrtZetaSignedCollectedTriplePolynomial,
    MathlibAux.collectedExponentialPolynomial,
    selbergSqrtZetaSignedCollectedFrequencySupport,
    selbergSqrtZetaSignedCollectedCoeff,
    selbergSqrtZetaSignedModelL2Budget,
    show 2 * T - T = T by ring] using hbase

end HardyTheorem
