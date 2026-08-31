import HardyTheorem.AFECriticalTwoCutoffBridge
import HardyTheorem.SelbergMollifiedDualRayEnergy

/-!
# Gaussian mean square of a fixed critical-line AFE energy

The local square-root AFE has at most two cutoffs.  This file closes the
full-line Gaussian mean square for either fixed cutoff by adding the already
proved main-polynomial and dual-polynomial estimates.  The square-root AFE
itself is not assumed or used here.
-/

open Complex MeasureTheory

namespace HardyTheorem
namespace AFE

/-- The Gaussian-weighted sum of the main and dual fixed AFE polynomial
energies is integrable on the whole line. -/
theorem integrable_gaussian_mul_criticalAfeFixedPolynomialEnergy
    {Delta : ℝ} (hDelta : 0 < Delta) (w : ℝ) (N X : ℕ) :
    Integrable fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        criticalAfeFixedPolynomialEnergy N X t := by
  have hmain :=
    MathlibAux.integrable_gaussian_mul_normSq_exponentialPolynomial
      hDelta w (Finset.Icc 1 (N * X))
      (selbergMollifiedCriticalLineCoeff N X) (fun k => -Real.log k)
  have hdual :=
    MathlibAux.integrable_gaussian_mul_normSq_exponentialPolynomial
      hDelta w (selbergMollifiedDualSupport N X)
      (selbergMollifiedDualCoeff X) selbergMollifiedDualFrequency
  rw [show (fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        criticalAfeFixedPolynomialEnergy N X t) =
    (fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (MathlibAux.exponentialPolynomial (Finset.Icc 1 (N * X))
            (selbergMollifiedCriticalLineCoeff N X)
            (fun k => -Real.log k) t)) +
    (fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq (selbergMollifiedDualPolynomial N X t)) by
    funext t
    simp only [criticalAfeFixedPolynomialEnergy, Pi.add_apply, mul_add]]
  exact hmain.add (by
    simpa only [selbergMollifiedDualPolynomial] using hdual)

/-- The full-line Gaussian mean square of one fixed AFE energy is bounded by
exactly two copies of the common Schur bound, one for the main polynomial and
one for the dual polynomial. -/
theorem integral_gaussian_mul_criticalAfeFixedPolynomialEnergy_le
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X)
    {Delta : ℝ} (hDelta : 2 * ((N * X : ℕ) : ℝ) ≤ Delta)
    (w : ℝ) :
    (∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        criticalAfeFixedPolynomialEnergy N X t) ≤
      2 *
        (Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
          MathlibAux.gaussianBucketSchurConstant *
            (2 * (1 + Real.log (N * X)) ^ 4)) := by
  have hDeltaPos : 0 < Delta := by
    have hNXpos : 0 < ((N * X : ℕ) : ℝ) := by
      positivity
    linarith
  have hmainInt :=
    MathlibAux.integrable_gaussian_mul_normSq_exponentialPolynomial
      hDeltaPos w (Finset.Icc 1 (N * X))
      (selbergMollifiedCriticalLineCoeff N X) (fun k => -Real.log k)
  have hdualInt :=
    MathlibAux.integrable_gaussian_mul_normSq_exponentialPolynomial
      hDeltaPos w (selbergMollifiedDualSupport N X)
      (selbergMollifiedDualCoeff X) selbergMollifiedDualFrequency
  have hdualInt' : Integrable fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq (selbergMollifiedDualPolynomial N X t) := by
    simpa only [selbergMollifiedDualPolynomial] using hdualInt
  have hmain :=
    integral_gaussian_normSq_criticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_le
      hN hX hDelta w
  have hmain' :
      (∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          Complex.normSq
            (MathlibAux.exponentialPolynomial (Finset.Icc 1 (N * X))
              (selbergMollifiedCriticalLineCoeff N X)
              (fun k => -Real.log k) t)) ≤
        Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
          MathlibAux.gaussianBucketSchurConstant *
            (2 * (1 + Real.log (N * X)) ^ 4) := by
    rw [show (fun t : ℝ =>
        Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          Complex.normSq
            ((∑ m ∈ Finset.Icc 1 N,
                1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
              selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) =
      fun t : ℝ =>
        Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          Complex.normSq
            (MathlibAux.exponentialPolynomial (Finset.Icc 1 (N * X))
              (selbergMollifiedCriticalLineCoeff N X)
              (fun k => -Real.log k) t) by
      funext t
      rw [criticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_eq_exponentialPolynomial]] at hmain
    exact hmain
  have hdual :=
    integral_gaussian_normSq_selbergMollifiedDualPolynomial_le
      hN hX hDelta w
  rw [show (fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        criticalAfeFixedPolynomialEnergy N X t) =
    fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          Complex.normSq
            (MathlibAux.exponentialPolynomial (Finset.Icc 1 (N * X))
              (selbergMollifiedCriticalLineCoeff N X)
              (fun k => -Real.log k) t) +
        Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          Complex.normSq (selbergMollifiedDualPolynomial N X t) by
    funext t
    simp only [criticalAfeFixedPolynomialEnergy, mul_add]]
  rw [integral_add hmainInt hdualInt']
  linarith

end AFE
end HardyTheorem
