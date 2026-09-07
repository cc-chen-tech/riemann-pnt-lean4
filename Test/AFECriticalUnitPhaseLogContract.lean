import HardyTheorem.AFECriticalUnitPhaseLog

open Complex

namespace HardyTheorem.AFE

#check zeta_critical_unitPhase_logAfe_target
#print axioms criticalAfeUnitPhaseDualProduct_normSq_eq_mainProduct
#print axioms normSq_criticalUnitPhaseAfeProduct_le_three_components

/-- Regression contract: the dual phase may be any unit complex number;
the critical-boundary energy must not depend on its argument. -/
example (phase : ℂ) (hphase : ‖phase‖ = 1) (X : ℕ) (t : ℝ) :
    Complex.normSq
        (phase *
          (criticalAfeDualSum t *
            selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) =
      Complex.normSq
        (criticalAfeMainSum t *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) :=
  criticalAfeUnitPhaseDualProduct_normSq_eq_mainProduct phase hphase X t

/-- Regression contract: an arbitrary unit-phase AFE decomposition is
bounded by two copies of the main energy plus the genuine remainder. -/
example {phase remainder : ℂ} (hphase : ‖phase‖ = 1)
    (X : ℕ) (t : ℝ)
    (hdecomp :
      riemannZeta ((1 / 2 : ℂ) + I * t) =
        criticalAfeMainSum t + phase * criticalAfeDualSum t + remainder) :
    Complex.normSq
        (riemannZeta ((1 / 2 : ℂ) + I * t) *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) ≤
      3 *
        (2 * Complex.normSq
          (criticalAfeMainSum t *
            selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) +
          Complex.normSq
            (remainder *
              selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))):=
  normSq_criticalUnitPhaseAfeProduct_le_three_components
    phase remainder hphase X t hdecomp

end HardyTheorem.AFE
