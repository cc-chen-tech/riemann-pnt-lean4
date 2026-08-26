import HardyTheorem.ConreyDegreeOneEta

open Complex
open scoped ComplexConjugate

namespace HardyTheorem

example (t : ℝ) : (conreyCriticalPoint t).re = 1 / 2 :=
  conreyCriticalPoint_re t

example (t : ℝ) :
    RiemannHypothesis.completedZeta (conreyCriticalPoint t) =
      conj (RiemannHypothesis.completedZeta (conreyCriticalPoint t)) :=
  completedZeta_eq_conj_on_criticalLine t

example (t : ℝ) :
    conj (deriv RiemannHypothesis.completedZeta (conreyCriticalPoint t)) =
      -deriv RiemannHypothesis.completedZeta (conreyCriticalPoint t) :=
  conj_deriv_completedZeta_eq_neg_on_criticalLine t

example (g g0 g1 L t : ℝ) :
    (conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t)).re =
      g * (RiemannHypothesis.completedZeta (conreyCriticalPoint t)).re :=
  conreyDegreeOneEta_re_on_criticalLine g g0 g1 L t

example {g g0 g1 L t : ℝ} (hg : g ≠ 0)
    (hre : (conreyDegreeOneEta g g0 g1 L
      (conreyCriticalPoint t)).re = 0)
    (hne : conreyDegreeOneEta g g0 g1 L
      (conreyCriticalPoint t) ≠ 0) :
    riemannZeta (conreyCriticalPoint t) = 0 ∧
      analyticOrderNatAt riemannZeta (conreyCriticalPoint t) = 1 :=
  conreyDegreeOneEta_simple_zero_of_re_eq_zero_of_ne_zero hg hre hne

#print axioms conreyDegreeOneEta_re_on_criticalLine
#print axioms conreyDegreeOneEta_simple_zero_of_re_eq_zero_of_ne_zero

end HardyTheorem
