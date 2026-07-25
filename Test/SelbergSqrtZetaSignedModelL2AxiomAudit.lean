import HardyTheorem.SelbergSqrtZetaSignedModelL2

open HardyTheorem

#check selbergSqrtZetaSignedModelL2Budget
#check selbergSqrtZetaSignedActualL2Budget
#check integral_sq_selbergSqrtZetaSignedThetaModel_le_modelL2Budget
#check exists_integral_sq_selbergSqrtZetaMollifiedHardyZ_le_actualL2Budget

example (kappa T : ℝ) (X : ℕ) (hT : 0 < T) :
    (∫ t in T..2 * T,
      selbergSqrtZetaSignedThetaModel kappa T X t ^ 2) ≤
        selbergSqrtZetaSignedModelL2Budget T X :=
  integral_sq_selbergSqrtZetaSignedThetaModel_le_modelL2Budget
    kappa T X hT

example :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T : ℝ, T0 ≤ T →
        (∫ t in T..2 * T,
          selbergSqrtZetaMollifiedHardyZ X t ^ 2) ≤
            selbergSqrtZetaSignedActualL2Budget C T X :=
  exists_integral_sq_selbergSqrtZetaMollifiedHardyZ_le_actualL2Budget

#print axioms integral_sq_selbergSqrtZetaSignedThetaModel_le_modelL2Budget
#print axioms exists_integral_sq_selbergSqrtZetaMollifiedHardyZ_le_actualL2Budget
