import HardyTheorem.AFE

open Complex
open scoped ComplexConjugate

open HardyTheorem
open HardyTheorem.AFE

#check criticalGamma_div_norm_eq_exp
#check criticalGamma_conj_div_gamma_eq_dualPhase
#check criticalAfeDualPhase
#check criticalAfeDualPhase_eq_exp_neg_two_thetaPhase
#check zeta_critical_afe_target

example (t : ℝ) :
    conj (Gammaℝ ((1 / 2 : ℂ) + I * t)) /
        Gammaℝ ((1 / 2 : ℂ) + I * t) =
      criticalAfeDualPhase t :=
  criticalGamma_conj_div_gamma_eq_dualPhase t
