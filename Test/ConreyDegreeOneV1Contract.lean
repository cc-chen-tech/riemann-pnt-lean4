import HardyTheorem.ConreyDegreeOneV1

open Complex

namespace HardyTheorem

example {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    conreyH s ≠ 0 :=
  conreyH_ne_zero_of_re_pos_of_ne_one hs0 hs1

example {g g0 g1 L : ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (conreyDegreeOneV1 g g0 g1 L) s :=
  analyticAt_conreyDegreeOneV1_of_re_pos_of_ne_one hs0 hs1

example {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    conreyH s ≠ 0 :=
  conreyH_ne_zero_of_mem_criticalStrip hs0 hs1

example {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    RiemannHypothesis.completedZeta s = conreyH s * riemannZeta s :=
  completedZeta_eq_conreyH_mul_riemannZeta hs0 hs1

example {g g0 g1 L : ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    conreyDegreeOneEta g g0 g1 L s =
      conreyH s * conreyDegreeOneV1 g g0 g1 L s :=
  conreyDegreeOneEta_eq_conreyH_mul_conreyDegreeOneV1 hs0 hs1

example {g g0 g1 L : ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    conreyDegreeOneEta g g0 g1 L s = 0 ↔
      conreyDegreeOneV1 g g0 g1 L s = 0 :=
  conreyDegreeOneEta_eq_zero_iff_conreyDegreeOneV1_eq_zero hs0 hs1

example {g g0 g1 L : ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    analyticOrderNatAt (conreyDegreeOneEta g g0 g1 L) s =
      analyticOrderNatAt (conreyDegreeOneV1 g g0 g1 L) s :=
  analyticOrderNatAt_conreyDegreeOneEta_eq_conreyDegreeOneV1 hs0 hs1

#print axioms completedZeta_eq_conreyH_mul_riemannZeta
#print axioms conreyH_ne_zero_of_re_pos_of_ne_one
#print axioms analyticAt_conreyDegreeOneV1_of_re_pos_of_ne_one
#print axioms conreyDegreeOneEta_eq_conreyH_mul_conreyDegreeOneV1
#print axioms conreyDegreeOneEta_eq_zero_iff_conreyDegreeOneV1_eq_zero
#print axioms analyticOrderNatAt_conreyDegreeOneEta_eq_conreyDegreeOneV1

end HardyTheorem
