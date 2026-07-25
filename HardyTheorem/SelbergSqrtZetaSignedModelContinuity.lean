import HardyTheorem.SelbergSqrtZetaSignedModelPolynomial

open Complex

namespace HardyTheorem

/-!
# Continuity of the signed square-root-zeta model

The finite signed phase polynomial is continuous at every positive height.
The positivity restriction is essential here: `thetaModel` contains a real
logarithm, so this module deliberately makes no continuity assertion at zero.
-/

private theorem continuousAt_selbergSqrtZetaSignedPhasePolynomial_of_pos
    {N X : ℕ} {t : ℝ} (ht : 0 < t) :
    ContinuousAt (selbergSqrtZetaSignedPhasePolynomial N X) t := by
  unfold selbergSqrtZetaSignedPhasePolynomial
  apply tendsto_finset_sum
  intro p hp
  have htheta : ContinuousAt thetaModel t := by
    change ContinuousAt (fun x : ℝ =>
      x / 2 * Real.log (x / (2 * Real.pi)) - x / 2 - Real.pi / 8) t
    fun_prop (disch := positivity)
  have hphase : ContinuousAt (fun x : ℝ =>
      thetaModel x + selbergSqrtZetaSignedPhaseFrequency p * x) t :=
    htheta.add (continuousAt_const.mul continuousAt_id)
  exact continuousAt_const.mul
    ((continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp hphase)).cexp)

/-- The finite signed square-root-zeta theta model is continuous on every
closed interval with a positive left endpoint. -/
theorem continuousOn_selbergSqrtZetaSignedThetaModel_Icc_of_pos
    (kappa T : ℝ) (X : ℕ) {A B : ℝ} (hA : 0 < A) :
    ContinuousOn (selbergSqrtZetaSignedThetaModel kappa T X) (Set.Icc A B) := by
  intro t ht
  rw [selbergSqrtZetaSignedThetaModel_eq_re_exp_I_kappa_mul_signedPhasePolynomial]
  apply ContinuousAt.continuousWithinAt
  apply Complex.continuous_re.continuousAt.comp
  exact continuousAt_const.mul
    (continuousAt_selbergSqrtZetaSignedPhasePolynomial_of_pos
      (hA.trans_le ht.1))

/-- The signed theta model is continuous on the positive dyadic control
interval used by its autocorrelation integrals. -/
theorem continuousOn_selbergSqrtZetaSignedThetaModel_Icc_T_two_mul_T
    (kappa T : ℝ) (X : ℕ) (hT : 0 < T) :
    ContinuousOn (selbergSqrtZetaSignedThetaModel kappa T X)
      (Set.Icc T (2 * T)) := by
  exact continuousOn_selbergSqrtZetaSignedThetaModel_Icc_of_pos kappa T X hT

end HardyTheorem
