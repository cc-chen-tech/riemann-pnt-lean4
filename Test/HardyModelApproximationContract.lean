import HardyTheorem.HardyModelApproximation

open Complex Set

#check HardyTheorem.exists_norm_rotated_riemannZeta_sub_thetaModel_dirichletPolynomial_le_inv_sqrt
#print axioms HardyTheorem.exists_norm_rotated_riemannZeta_sub_thetaModel_dirichletPolynomial_le_inv_sqrt

example :
    ∃ κ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T t : ℝ,
      T0 ≤ T → t ∈ Icc T (2 * T) →
        ‖Complex.exp (I * HardyTheorem.thetaPhase t) *
              riemannZeta ((1 / 2 : ℂ) + I * t) -
            Complex.exp (I * κ) *
              Complex.exp (I * HardyTheorem.thetaModel t) *
                (∑ n ∈ Finset.Icc 1
                    (HardyTheorem.firstZetaApproximationCutoff T),
                  1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))‖ ≤
          C / Real.sqrt T :=
  HardyTheorem.exists_norm_rotated_riemannZeta_sub_thetaModel_dirichletPolynomial_le_inv_sqrt
