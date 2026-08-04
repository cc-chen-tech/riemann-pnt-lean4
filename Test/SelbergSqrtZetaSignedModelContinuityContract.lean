import HardyTheorem.SelbergSqrtZetaSignedModelContinuity

namespace HardyTheorem

example (kappa T : ℝ) (X : ℕ) {A B : ℝ} (hA : 0 < A) :
    ContinuousOn (selbergSqrtZetaSignedThetaModel kappa T X) (Set.Icc A B) :=
  continuousOn_selbergSqrtZetaSignedThetaModel_Icc_of_pos kappa T X hA

example (kappa T : ℝ) (X : ℕ) (hT : 0 < T) :
    ContinuousOn (selbergSqrtZetaSignedThetaModel kappa T X)
      (Set.Icc T (2 * T)) :=
  continuousOn_selbergSqrtZetaSignedThetaModel_Icc_T_two_mul_T kappa T X hT

end HardyTheorem
