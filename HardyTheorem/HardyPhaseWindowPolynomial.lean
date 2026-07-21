import HardyTheorem.HardyPhaseWindowCoeffDerivative
import MathlibAux.TimeDependentLogHilbert

open Complex
open scoped BigOperators

namespace HardyTheorem

/-- After removing the common theta phase, the linearized Hardy sum is a
negative logarithmic-frequency polynomial with moving window coefficients. -/
theorem hardyPhaseLinearizedSum_eq_commonPhase_mul_negLogPolynomial
    {T delta t : ℝ} (ht : 0 < t) :
    hardyPhaseLinearizedSum T delta t =
      Complex.exp (I * thetaModel t) *
        MathlibAux.timeDependentNegLogPolynomial
          (Finset.Icc 1 (firstZetaApproximationCutoff T))
          (fun x n => hardyPhaseWindowCoeff n delta x) t := by
  change
    (∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
      hardyPhaseLinearizedCoeff n delta t) = _
  rw [MathlibAux.timeDependentNegLogPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  rw [hardyPhaseLinearizedCoeff_eq_commonPhase_mul_windowCoeff hnpos ht]
  have hexp :
      Complex.exp (-I * ((Real.log n : ℂ) * (t : ℂ))) =
        Complex.exp (-I * ((Real.log n * t : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- The common theta phase is unitary, so it disappears from the pointwise
energy of the linearized Hardy sum. -/
theorem normSq_hardyPhaseLinearizedSum_eq_negLogPolynomial
    {T delta t : ℝ} (ht : 0 < t) :
    Complex.normSq (hardyPhaseLinearizedSum T delta t) =
      Complex.normSq
        (MathlibAux.timeDependentNegLogPolynomial
          (Finset.Icc 1 (firstZetaApproximationCutoff T))
          (fun x n => hardyPhaseWindowCoeff n delta x) t) := by
  rw [hardyPhaseLinearizedSum_eq_commonPhase_mul_negLogPolynomial ht,
    Complex.normSq_mul]
  have hphase :
      Complex.normSq (Complex.exp (I * thetaModel t)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_I_mul_ofReal]
    norm_num
  rw [hphase, one_mul]

/-- Conjugation converts the negative Hardy frequencies to the positive
frequency convention used by the time-dependent Hilbert identity. -/
theorem hardyPhaseNegLogPolynomial_eq_conj_positive
    (s : Finset ℕ) (delta t : ℝ) :
    MathlibAux.timeDependentNegLogPolynomial s
        (fun x n => hardyPhaseWindowCoeff n delta x) t =
      (starRingEnd ℂ)
        (MathlibAux.timeDependentLogPolynomial s
          (fun x n => (starRingEnd ℂ) (hardyPhaseWindowCoeff n delta x)) t) :=
  MathlibAux.timeDependentNegLogPolynomial_eq_conj _ _ _

end HardyTheorem
