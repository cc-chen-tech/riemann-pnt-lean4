import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic

open Complex Set

namespace PrimeNumberTheorem.LFunction

/-- Minimal strip data needed to transfer zeros and multiplicities from a base
function to its entire completion. Contour-specific nonvanishing and finite-zero
data remain theorem inputs. -/
structure CompletedLFunctionContourData where
  base : ℂ → ℂ
  completed : ℂ → ℂ
  leftBoundary : ℝ
  rightBoundary : ℝ
  left_lt_right : leftBoundary < rightBoundary
  analytic_completed : AnalyticOnNhd ℂ completed Set.univ
  completed_eq_zero_iff_base_eq_zero :
    ∀ {s : ℂ}, leftBoundary < s.re → s.re < rightBoundary →
      (completed s = 0 ↔ base s = 0)
  analyticOrderAt_completed_eq_base :
    ∀ {s : ℂ}, leftBoundary < s.re → s.re < rightBoundary →
      (analyticOrderAt completed s = analyticOrderAt base s)

namespace CompletedLFunctionContourData

theorem analyticOrderNatAt_completed_eq_base
    (data : CompletedLFunctionContourData) {s : ℂ}
    (hleft : data.leftBoundary < s.re)
    (hright : s.re < data.rightBoundary) :
    analyticOrderNatAt data.completed s = analyticOrderNatAt data.base s :=
  congrArg ENat.toNat
    (data.analyticOrderAt_completed_eq_base hleft hright)

end CompletedLFunctionContourData
end PrimeNumberTheorem.LFunction
