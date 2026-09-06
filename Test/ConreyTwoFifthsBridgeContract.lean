import HardyTheorem.ConreyTwoFifthsBridge

open Filter Topology

namespace HardyTheorem

noncomputable example : ℝ := conreyExplicitIntegralProportion

example (h : conreyExplicitAnalyticLowerBound) :
    conreyTwoFifthsSimpleZerosTarget :=
  conreyTwoFifthsSimpleZerosTarget_of_explicit_analytic_lower_bound h

#print axioms conreyTwoFifthsSimpleZerosTarget_of_explicit_analytic_lower_bound

end HardyTheorem
