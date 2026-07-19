import PrimeNumberTheorem.LFunction.CompletedContourData

open Complex

namespace PrimeNumberTheorem.LFunction

example (data : CompletedLFunctionContourData) {s : ℂ}
    (hleft : data.leftBoundary < s.re)
    (hright : s.re < data.rightBoundary) :
    data.completed s = 0 ↔ data.base s = 0 :=
  data.completed_eq_zero_iff_base_eq_zero (s := s) hleft hright

example (data : CompletedLFunctionContourData) {s : ℂ}
    (hleft : data.leftBoundary < s.re)
    (hright : s.re < data.rightBoundary) :
    analyticOrderNatAt data.completed s = analyticOrderNatAt data.base s :=
  data.analyticOrderNatAt_completed_eq_base (s := s) hleft hright

end PrimeNumberTheorem.LFunction
