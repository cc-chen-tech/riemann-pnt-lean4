import HardyTheorem.HardyGoodWindowMeasure
import HardyTheorem.HardyLittlewoodPacking
import HardyTheorem.ShortIntegralZeroDetection

open Complex MeasureTheory Set

namespace HardyTheorem

/-- Hardy and Littlewood's linear lower bound for the number of distinct
zeros of the Riemann zeta function on the critical line. -/
theorem hardy_littlewood_lower_bound_target_proved :
    hardy_littlewood_lower_bound_target := by
  obtain ⟨H, hH, T0, hT0, hbad⟩ :=
    exists_fixed_window_bad_start_measure_le
  apply hardy_littlewood_lower_bound_target_of_good_window_measure
    H T0 (fun _T => hardyGoodWindowStarts H) hH
  · intro T hT
    exact hbad T hT
  · intro T hT t ht
    exact exists_criticalLineZero_of_abs_hardyShortIntegral_lt_hardyShortAbsIntegral
      hH.le ht.1

end HardyTheorem
