import HardyTheorem.AFECriticalUnitPhaseLogProof

open HardyTheorem AFE Complex

-- No AFE, Gamma, Poisson, or derivative-bound premise is supplied.
example : zeta_critical_unitPhase_logAfe_target := zeta_critical_unitPhase_logAfe

-- The canonical moving prefixes, unit modulus, and exact remainder scale
-- must all be obtained with one uniform constant and this fixed threshold.
example : ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, 72 * Real.pi ≤ t →
    ∃ phase remainder : ℂ, ‖phase‖ = 1 ∧
      riemannZeta ((1 / 2 : ℂ) + I * t) =
        criticalAfeMainSum t + phase * criticalAfeDualSum t + remainder ∧
      ‖remainder‖ ≤ R * t ^ (-1 / 4 : ℝ) * (1 + Real.log t) :=
  exists_zeta_critical_unitPhase_logAfe_fixed_threshold

#print axioms zeta_critical_unitPhase_logAfe
#print axioms exists_zeta_critical_unitPhase_logAfe_fixed_threshold
