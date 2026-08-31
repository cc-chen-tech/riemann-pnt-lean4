import HardyTheorem.AFECriticalCanonical
import HardyTheorem.SelbergMollifiedGaussianPolynomial
import HardyTheorem.SelbergMollifiedDualPolynomial

/-!
# Fixed-polynomial form of the canonical critical-line AFE

At a height where the square-root cutoff equals `N`, the two canonical AFE
main terms multiplied by the standard linear Selberg mollifier are exactly
the two finite exponential polynomials whose Gaussian moments are estimated
elsewhere.  The final theorem separates those terms from the canonical AFE
remainder with the elementary sharp three-term quadratic inequality.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem
namespace AFE

/-- Reindex the range form of the first AFE sum as the positive integer
interval expected by the finite-polynomial lemmas. -/
theorem criticalAfeMainSum_eq_Icc (t : ℝ) :
    criticalAfeMainSum t =
      ∑ n ∈ Finset.Icc 1 (criticalAfeCutoff t),
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t) := by
  have hIcc : Finset.Icc 1 (criticalAfeCutoff t) =
      Finset.Ico 1 (criticalAfeCutoff t + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp [criticalAfeMainSum, add_comm]

/-- Reindex the range form of the dual AFE sum as a positive integer
interval. -/
theorem criticalAfeDualSum_eq_Icc (t : ℝ) :
    criticalAfeDualSum t =
      ∑ n ∈ Finset.Icc 1 (criticalAfeCutoff t),
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) - I * t) := by
  have hIcc : Finset.Icc 1 (criticalAfeCutoff t) =
      Finset.Ico 1 (criticalAfeCutoff t + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp [criticalAfeDualSum, add_comm]

/-- At a fixed cutoff, the first AFE term times the mollifier is exactly the
collected integer-frequency exponential polynomial. -/
theorem criticalAfeMainSum_mul_mollifier_eq_exponentialPolynomial
    {N X : ℕ} {t : ℝ} (hcutoff : criticalAfeCutoff t = N) :
    criticalAfeMainSum t *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) =
      MathlibAux.exponentialPolynomial (Finset.Icc 1 (N * X))
        (selbergMollifiedCriticalLineCoeff N X)
        (fun k => -Real.log k) t := by
  rw [criticalAfeMainSum_eq_Icc, hcutoff]
  exact
    criticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_eq_exponentialPolynomial
      N X t

/-- At a fixed cutoff, the dual AFE term times the mollifier is exactly the
rational-frequency exponential polynomial. -/
theorem criticalAfeDualSum_mul_mollifier_eq_dualPolynomial
    {N X : ℕ} {t : ℝ} (hcutoff : criticalAfeCutoff t = N) :
    criticalAfeDualSum t *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) =
      selbergMollifiedDualPolynomial N X t := by
  rw [criticalAfeDualSum_eq_Icc, hcutoff]
  exact
    dualCriticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_eq_exponentialPolynomial
      N X t

private theorem normSq_add_add_le_three (A B C : ℂ) :
    Complex.normSq (A + B + C) ≤
      3 * (Complex.normSq A + Complex.normSq B + Complex.normSq C) := by
  simp only [Complex.normSq_eq_norm_sq]
  have htri : ‖A + B + C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ :=
    (norm_add_le (A + B) C).trans
      (add_le_add (norm_add_le A B) le_rfl)
  have hsquare : ‖A + B + C‖ ^ 2 ≤
      (‖A‖ + ‖B‖ + ‖C‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
        (norm_nonneg _))).2 htri
  calc
    ‖A + B + C‖ ^ 2 ≤ (‖A‖ + ‖B‖ + ‖C‖) ^ 2 := hsquare
    _ ≤ 3 * (‖A‖ ^ 2 + ‖B‖ ^ 2 + ‖C‖ ^ 2) := by
      nlinarith [sq_nonneg (‖A‖ - ‖B‖), sq_nonneg (‖A‖ - ‖C‖),
        sq_nonneg (‖B‖ - ‖C‖)]

/-- The canonical AFE product is bounded by its first, dual, and remainder
components.  The unit norm of the corrected dual phase removes that phase
without loss. -/
theorem normSq_criticalAfeProduct_le_three_components (X : ℕ) (t : ℝ) :
    Complex.normSq
        (riemannZeta ((1 / 2 : ℂ) + I * t) *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) ≤
      3 *
        (Complex.normSq
            (criticalAfeMainSum t *
              selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) +
          Complex.normSq
            (criticalAfeDualSum t *
              selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) +
          Complex.normSq
            (criticalAfeCanonicalRemainder t *
              selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) := by
  rw [criticalAfe_product_decomposition]
  have h := normSq_add_add_le_three
    (criticalAfeMainSum t *
      selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))
    (criticalAfeDualPhase t *
      (criticalAfeDualSum t *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)))
    (criticalAfeCanonicalRemainder t *
      selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))
  simpa [Complex.normSq_eq_norm_sq, norm_criticalAfeDualPhase] using h

/-- Fixed-cutoff specialization of the three-component AFE product bound.
This is the pointwise interface consumed by the two finite Gaussian moment
theorems. -/
theorem normSq_criticalAfeProduct_le_three_fixedPolynomial_components
    {N X : ℕ} {t : ℝ} (hcutoff : criticalAfeCutoff t = N) :
    Complex.normSq
        (riemannZeta ((1 / 2 : ℂ) + I * t) *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) ≤
      3 *
        (Complex.normSq
            (MathlibAux.exponentialPolynomial (Finset.Icc 1 (N * X))
              (selbergMollifiedCriticalLineCoeff N X)
              (fun k => -Real.log k) t) +
          Complex.normSq (selbergMollifiedDualPolynomial N X t) +
          Complex.normSq
            (criticalAfeCanonicalRemainder t *
              selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) := by
  have h := normSq_criticalAfeProduct_le_three_components X t
  rw [criticalAfeMainSum_mul_mollifier_eq_exponentialPolynomial hcutoff,
    criticalAfeDualSum_mul_mollifier_eq_dualPolynomial hcutoff] at h
  exact h

end AFE
end HardyTheorem
