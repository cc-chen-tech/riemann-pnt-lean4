import HardyTheorem.SelbergSqrtZetaSignedPhasePolynomial

open Complex
open scoped BigOperators

namespace HardyTheorem

noncomputable example (N X : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  selbergSqrtZetaSignedPhaseSupport N X

noncomputable example (X : ℕ) (p : ℕ × (ℕ × ℕ)) : ℂ :=
  selbergSqrtZetaSignedPhaseCoeff X p

noncomputable example (p : ℕ × (ℕ × ℕ)) : ℝ :=
  selbergSqrtZetaSignedPhaseFrequency p

noncomputable example (N X : ℕ) (t : ℝ) : ℂ :=
  selbergSqrtZetaSignedTriplePolynomial N X t

noncomputable example (N X : ℕ) (t : ℝ) : ℂ :=
  selbergSqrtZetaSignedPhasePolynomial N X t

example (X : ℕ) (t : ℝ) :
    (starRingEnd ℂ)
        (selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) =
      ∑ l ∈ Finset.Icc 1 X,
        (selbergSqrtZetaTaperedCoeff X l : ℂ) *
          (1 / (l : ℂ) ^ ((1 / 2 : ℂ) - I * t)) :=
  conj_selbergSqrtZetaMollifier_criticalLine_eq_sum X t

example (N X : ℕ) (t : ℝ) :
    ((∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
        selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) *
        (starRingEnd ℂ)
          (selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) =
      ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 X,
        ∑ l ∈ Finset.Icc 1 X,
          (selbergSqrtZetaTaperedCoeff X d : ℂ) *
            (selbergSqrtZetaTaperedCoeff X l : ℂ) *
            (1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
            (1 / (d : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
            (1 / (l : ℂ) ^ ((1 / 2 : ℂ) - I * t)) :=
  criticalLineDirichletPolynomial_mul_sqrtZetaMollifier_mul_conj_eq_signedTripleSum N X t

example (N X : ℕ) (t : ℝ) :
    ((∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
        selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) *
        (starRingEnd ℂ)
          (selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) =
      selbergSqrtZetaSignedTriplePolynomial N X t :=
  criticalLineDirichletPolynomial_mul_sqrtZetaMollifier_mul_conj_eq_signedTriplePolynomial N X t

example (N X : ℕ) (t : ℝ) :
    selbergSqrtZetaSignedPhasePolynomial N X t =
      Complex.exp (I * (thetaModel t : ℂ)) *
        selbergSqrtZetaSignedTriplePolynomial N X t :=
  selbergSqrtZetaSignedPhasePolynomial_eq_exp_mul_signedTriplePolynomial N X t

example (N X : ℕ) (t : ℝ) :
    Complex.exp (I * (thetaModel t : ℂ)) *
        (((∑ m ∈ Finset.Icc 1 N,
            1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
          selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) *
          (starRingEnd ℂ)
            (selbergSqrtZetaMollifier X
              ((1 / 2 : ℂ) + I * t))) =
      selbergSqrtZetaSignedPhasePolynomial N X t :=
  exp_I_thetaModel_mul_criticalLinePolynomial_mul_sqrtZetaMollifier_mul_conj_eq_signedPhasePolynomial N X t

end HardyTheorem
