import HardyTheorem.VerticalGammaAsymptotic

open Complex

noncomputable example (t : ℝ) : ℝ := HardyTheorem.verticalGammaPhaseVelocity t

example {t : ℝ} (ht : 0 < t) :
    deriv HardyTheorem.thetaModel t =
      (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)) :=
  HardyTheorem.deriv_thetaModel ht

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      |HardyTheorem.verticalGammaPhaseVelocity t -
          deriv HardyTheorem.thetaModel t| ≤ C / t ^ 2 :=
  HardyTheorem.exists_abs_verticalGammaPhaseVelocity_sub_deriv_thetaModel_le_inv_sq

noncomputable example (t : ℝ) : ℝ := HardyTheorem.verticalGammaUnwrappedPhase t

example {t : ℝ} (ht : 1 ≤ t) :
    Complex.exp (I * HardyTheorem.verticalGammaUnwrappedPhase t) =
      Complex.exp (I * HardyTheorem.thetaPhase t) :=
  HardyTheorem.exp_I_verticalGammaUnwrappedPhase_eq_exp_I_thetaPhase ht

example :
    ∃ κ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      |HardyTheorem.verticalGammaUnwrappedPhase t -
          HardyTheorem.thetaModel t - κ| ≤ C / t :=
  HardyTheorem.exists_verticalGammaUnwrappedPhase_sub_thetaModel_tendsto_const_inv

example :
    ∃ κ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖Complex.exp (I * HardyTheorem.thetaPhase t) -
          Complex.exp (I * κ) * Complex.exp (I * HardyTheorem.thetaModel t)‖ ≤ C / t :=
  HardyTheorem.exists_norm_exp_I_thetaPhase_sub_const_mul_exp_I_thetaModel_le_inv
