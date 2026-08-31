import HardyTheorem.AFECriticalPolynomialBridge
import HardyTheorem.AFECriticalCutoffStability

/-!
# A two-fixed-cutoff majorant on a local AFE window

When the square-root coordinate has width less than one, the moving AFE
cutoff is either the left-end cutoff `N` or `N+1`.  Instead of partitioning
the interval into measurable cutoff fibres, we majorize pointwise by the sum
of both fixed-polynomial energies.  This form is designed to be integrated
directly against the Carlson Gaussian.
-/

open Complex Set

namespace HardyTheorem
namespace AFE

/-- The sum of the first and dual fixed-cutoff mollified AFE polynomial
energies. -/
noncomputable def criticalAfeFixedPolynomialEnergy
    (N X : ℕ) (t : ℝ) : ℝ :=
  Complex.normSq
      (MathlibAux.exponentialPolynomial (Finset.Icc 1 (N * X))
        (selbergMollifiedCriticalLineCoeff N X)
        (fun k => -Real.log k) t) +
    Complex.normSq (selbergMollifiedDualPolynomial N X t)

/-- Fixed AFE polynomial energy is nonnegative. -/
theorem criticalAfeFixedPolynomialEnergy_nonneg
    (N X : ℕ) (t : ℝ) :
    0 ≤ criticalAfeFixedPolynomialEnergy N X t := by
  unfold criticalAfeFixedPolynomialEnergy
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/-- One exact cutoff gives the corresponding fixed-polynomial energy plus
the canonical AFE remainder. -/
theorem normSq_criticalAfeProduct_le_three_fixedEnergy_add_remainder
    {N X : ℕ} {t : ℝ} (hcutoff : criticalAfeCutoff t = N) :
    Complex.normSq
        (riemannZeta ((1 / 2 : ℂ) + I * t) *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) ≤
      3 *
        (criticalAfeFixedPolynomialEnergy N X t +
          Complex.normSq
            (criticalAfeCanonicalRemainder t *
              selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) := by
  simpa [criticalAfeFixedPolynomialEnergy, add_assoc] using
    normSq_criticalAfeProduct_le_three_fixedPolynomial_components hcutoff

/-- Uniform pointwise majorant on a short height interval.  Both possible
fixed cutoffs are retained, so no measurable partition by the floor function
is needed. -/
theorem normSq_criticalAfeProduct_le_three_twoCutoffEnergies
    {L U t : ℝ} (_hL : 0 ≤ L) (ht : t ∈ Icc L U)
    (hwidth :
      Real.sqrt (U / (2 * Real.pi)) <
        Real.sqrt (L / (2 * Real.pi)) + 1)
    (X : ℕ) :
    Complex.normSq
        (riemannZeta ((1 / 2 : ℂ) + I * t) *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) ≤
      3 *
        (criticalAfeFixedPolynomialEnergy (criticalAfeCutoff L) X t +
          criticalAfeFixedPolynomialEnergy (criticalAfeCutoff L + 1) X t +
          Complex.normSq
            (criticalAfeCanonicalRemainder t *
              selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) := by
  rcases criticalAfeCutoff_eq_left_or_succ_of_mem_interval
      _hL ht hwidth with hcut | hcut
  · have hbase :=
      normSq_criticalAfeProduct_le_three_fixedEnergy_add_remainder
        (X := X) hcut
    calc
      _ ≤ 3 *
          (criticalAfeFixedPolynomialEnergy (criticalAfeCutoff L) X t +
            Complex.normSq
              (criticalAfeCanonicalRemainder t *
                selbergMoebiusMollifier X
                  ((1 / 2 : ℂ) + I * t))) := hbase
      _ ≤ _ := by
        have hnonneg := criticalAfeFixedPolynomialEnergy_nonneg
          (criticalAfeCutoff L + 1) X t
        nlinarith
  · have hbase :=
      normSq_criticalAfeProduct_le_three_fixedEnergy_add_remainder
        (X := X) hcut
    calc
      _ ≤ 3 *
          (criticalAfeFixedPolynomialEnergy (criticalAfeCutoff L + 1) X t +
            Complex.normSq
              (criticalAfeCanonicalRemainder t *
                selbergMoebiusMollifier X
                  ((1 / 2 : ℂ) + I * t))) := hbase
      _ ≤ _ := by
        have hnonneg := criticalAfeFixedPolynomialEnergy_nonneg
          (criticalAfeCutoff L) X t
        nlinarith

end AFE
end HardyTheorem
