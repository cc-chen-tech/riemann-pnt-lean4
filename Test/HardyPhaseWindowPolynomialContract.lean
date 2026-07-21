import HardyTheorem.HardyPhaseWindowPolynomial

open Complex

#check HardyTheorem.hardyPhaseLinearizedSum_eq_commonPhase_mul_negLogPolynomial
#check HardyTheorem.normSq_hardyPhaseLinearizedSum_eq_negLogPolynomial
#check HardyTheorem.hardyPhaseNegLogPolynomial_eq_conj_positive

example {T delta t : ℝ} (ht : 0 < t) :
    HardyTheorem.hardyPhaseLinearizedSum T delta t =
      Complex.exp (I * HardyTheorem.thetaModel t) *
        MathlibAux.timeDependentNegLogPolynomial
          (Finset.Icc 1 (HardyTheorem.firstZetaApproximationCutoff T))
          (fun x n => HardyTheorem.hardyPhaseWindowCoeff n delta x) t :=
  HardyTheorem.hardyPhaseLinearizedSum_eq_commonPhase_mul_negLogPolynomial ht

example {T delta t : ℝ} (ht : 0 < t) :
    Complex.normSq (HardyTheorem.hardyPhaseLinearizedSum T delta t) =
      Complex.normSq
        (MathlibAux.timeDependentNegLogPolynomial
          (Finset.Icc 1 (HardyTheorem.firstZetaApproximationCutoff T))
          (fun x n => HardyTheorem.hardyPhaseWindowCoeff n delta x) t) :=
  HardyTheorem.normSq_hardyPhaseLinearizedSum_eq_negLogPolynomial ht

example (s : Finset ℕ) (delta t : ℝ) :
    MathlibAux.timeDependentNegLogPolynomial s
        (fun x n => HardyTheorem.hardyPhaseWindowCoeff n delta x) t =
      (starRingEnd ℂ)
        (MathlibAux.timeDependentLogPolynomial s
          (fun x n => (starRingEnd ℂ)
            (HardyTheorem.hardyPhaseWindowCoeff n delta x)) t) :=
  HardyTheorem.hardyPhaseNegLogPolynomial_eq_conj_positive s delta t

#print axioms HardyTheorem.hardyPhaseLinearizedSum_eq_commonPhase_mul_negLogPolynomial
#print axioms HardyTheorem.normSq_hardyPhaseLinearizedSum_eq_negLogPolynomial
#print axioms HardyTheorem.hardyPhaseNegLogPolynomial_eq_conj_positive
