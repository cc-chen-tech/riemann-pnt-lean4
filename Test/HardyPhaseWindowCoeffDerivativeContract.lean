import HardyTheorem.HardyPhaseWindowCoeffDerivative

open Complex MeasureTheory Set
open scoped BigOperators

#check HardyTheorem.hardyPhaseWindowCoeff
#check HardyTheorem.OscillatoryIntegral.hardyPhase_eq_thetaModel_sub_log
#check HardyTheorem.OscillatoryIntegral.deriv_hardyPhase_eq_deriv_thetaModel_sub_log
#check HardyTheorem.hardyPhaseLinearizedCoeff_eq_commonPhase_mul_windowCoeff
#check HardyTheorem.hasDerivAt_deriv_thetaModel
#check HardyTheorem.hasDerivAt_hardyPhaseWindowCoeff
#check HardyTheorem.norm_deriv_hardyPhaseWindowCoeff_le
#check HardyTheorem.sum_normSq_deriv_hardyPhaseWindowCoeff_le

example {n : ℕ} (hn : 0 < n) {delta t : ℝ} (ht : 0 < t) :
    HardyTheorem.hardyPhaseLinearizedCoeff n delta t =
      Complex.exp (I * HardyTheorem.thetaModel t) *
        Complex.exp (-I * (Real.log n * t)) *
          HardyTheorem.hardyPhaseWindowCoeff n delta t :=
  HardyTheorem.hardyPhaseLinearizedCoeff_eq_commonPhase_mul_windowCoeff hn ht

example {n : ℕ} (hn : 0 < n) {delta t : ℝ}
    (hdelta : 0 ≤ delta) (ht : 0 < t) :
    ‖deriv (HardyTheorem.hardyPhaseWindowCoeff n delta) t‖ ≤
      (Real.sqrt n)⁻¹ * delta ^ 2 / (4 * t) :=
  HardyTheorem.norm_deriv_hardyPhaseWindowCoeff_le hn hdelta ht

example {N : ℕ} {delta t : ℝ} (hdelta : 0 ≤ delta) (ht : 0 < t) :
    (∑ n ∈ Finset.Icc 1 N,
        Complex.normSq (deriv (HardyTheorem.hardyPhaseWindowCoeff n delta) t)) ≤
      delta ^ 4 / (16 * t ^ 2) * (1 + Real.log N) :=
  HardyTheorem.sum_normSq_deriv_hardyPhaseWindowCoeff_le hdelta ht

#print axioms HardyTheorem.hardyPhaseLinearizedCoeff_eq_commonPhase_mul_windowCoeff
#print axioms HardyTheorem.hasDerivAt_hardyPhaseWindowCoeff
#print axioms HardyTheorem.norm_deriv_hardyPhaseWindowCoeff_le
#print axioms HardyTheorem.sum_normSq_deriv_hardyPhaseWindowCoeff_le
