import HardyTheorem.AFECriticalUnitPhaseLogRemainder

open Filter

namespace HardyTheorem.AFE

#check criticalAfeLogRemainderWindowBound
#print axioms normSq_unitPhaseLogAfeRemainder_product_le_windowBound
#print axioms criticalAfeLogRemainderWindowBound_le_halfRange
#print axioms tendsto_halfRange_logRemainderFactor_atTop_nhds_zero
#print axioms eventually_halfRange_logRemainderFactor_le_one

example {R L U : ℝ} {X : ℕ} (hL : 1 ≤ L)
    (hX : (X : ℝ) ≤ L ^ (9 / 20 : ℝ)) :
    criticalAfeLogRemainderWindowBound R L U X ≤
      4 * R ^ 2 * L ^ (-1 / 20 : ℝ) *
        (1 + Real.log U) ^ 2 :=
  criticalAfeLogRemainderWindowBound_le_halfRange hL hX

example :
    Tendsto
      (fun L : ℝ =>
        L ^ (-1 / 20 : ℝ) * (1 + Real.log (4 * L)) ^ 2)
      atTop (nhds 0) :=
  tendsto_halfRange_logRemainderFactor_atTop_nhds_zero

end HardyTheorem.AFE
