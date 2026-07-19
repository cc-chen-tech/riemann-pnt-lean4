import HardyTheorem.ShortIntervalMeanValue
import MathlibAux.IntegralAbsSignChange

open Complex MeasureTheory Set

namespace HardyTheorem

/-- Strict cancellation in a signed Hardy short integral detects a zeta zero
on the corresponding critical-line segment. -/
theorem exists_criticalLineZero_of_abs_hardyShortIntegral_lt_hardyShortAbsIntegral
    {delta t : ℝ} (hdelta : 0 ≤ delta)
    (hstrict : |hardyShortIntegral delta t| <
      hardyShortAbsIntegral delta t) :
    ∃ u ∈ Set.Icc t (t + delta),
      riemannZeta ((1 / 2 : ℂ) + I * u) = 0 := by
  obtain ⟨u, hu, hzero⟩ :=
    MathlibAux.exists_zero_of_abs_intervalIntegral_lt_intervalIntegral_abs
      hardyZ_continuous (by linarith : t ≤ t + delta) hstrict
  exact ⟨u, hu, by
    convert hardyZ_zero_implies_zeta_zero u hzero using 1
    norm_num⟩

end HardyTheorem
