import HardyTheorem.SelbergMollifiedHardyPhasePolynomial

open Complex
open scoped BigOperators

namespace HardyTheorem

noncomputable example (q : ℚ) (t : ℝ) : ℝ :=
  selbergMollifiedHardyPhaseFrequency q t

noncomputable example (N X : ℕ) (t : ℝ) : ℂ :=
  selbergMollifiedHardyPhasePolynomial N X t

noncomputable example (N X : ℕ) (t : ℝ) : ℂ :=
  selbergMollifiedHardyPhaseCollectedPolynomial N X t

example (N X : ℕ) (t : ℝ) :
    selbergMollifiedHardyPhasePolynomial N X t =
      Complex.exp (I * (thetaModel t : ℂ)) *
        selbergMollifiedTriplePolynomial N X t :=
  selbergMollifiedHardyPhasePolynomial_eq_exp_mul_triplePolynomial N X t

example (N X : ℕ) (t : ℝ) :
    selbergMollifiedHardyPhaseCollectedPolynomial N X t =
      Complex.exp (I * (thetaModel t : ℂ)) *
        selbergMollifiedTripleCollectedPolynomial N X t :=
  selbergMollifiedHardyPhaseCollectedPolynomial_eq_exp_mul_collectedPolynomial N X t

example (N X : ℕ) (t : ℝ) :
    selbergMollifiedHardyPhasePolynomial N X t =
      selbergMollifiedHardyPhaseCollectedPolynomial N X t :=
  selbergMollifiedHardyPhasePolynomial_eq_collectedPolynomial N X t

example (N X : ℕ) (t : ℝ) :
    Complex.exp (I * (thetaModel t : ℂ)) *
        (((∑ m ∈ Finset.Icc 1 N,
            1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) *
          (starRingEnd ℂ)
            (selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) =
      selbergMollifiedHardyPhasePolynomial N X t :=
  exp_I_thetaModel_mul_criticalLinePolynomial_mul_mollifier_mul_conj_eq_phasePolynomial N X t

example (N X : ℕ) (t : ℝ) :
    Complex.exp (I * (thetaModel t : ℂ)) *
        (((∑ m ∈ Finset.Icc 1 N,
            1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) *
          (starRingEnd ℂ)
            (selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) =
      selbergMollifiedHardyPhaseCollectedPolynomial N X t :=
  exp_I_thetaModel_mul_criticalLinePolynomial_mul_mollifier_mul_conj_eq_collectedPhasePolynomial
    N X t

end HardyTheorem
