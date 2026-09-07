import HardyTheorem.ConreyBalancedTraceCount

open Complex Set MeasureTheory
open scoped Interval
open HardyTheorem

-- q must be the continuous extension of the actual eta logarithmic-derivative
-- real trace. There are no caller-supplied components, logarithms or phases.
example {g g0 g1 L U T : ℝ} {q : ℝ → ℝ}
    (hg : g ≠ 0) (hU : 0 ≤ U) (hUT : U < T)
    (hq : ContinuousOn q (Icc U T))
    (htrace : ∀ t ∈ Ioo U T,
      conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) ≠ 0 →
      q t = (logDeriv (conreyDegreeOneEta g g0 g1 L) (conreyCriticalPoint t)).re) :
    ∃ S : Finset ℝ,
      (∫ t in U..T, q t) / Real.pi -
        conreyEtaCriticalZeroMultiplicityMassBetween g g0 g1 L U T - 1 ≤ S.card ∧
      ∀ t ∈ S, t ∈ Ioo U T ∧ riemannZeta (conreyCriticalPoint t) = 0 ∧
        analyticOrderNatAt riemannZeta (conreyCriticalPoint t) = 1 := by
  exact exists_conreyDegreeOneEta_simpleZero_finset_of_regularized_trace hg hU hUT hq htrace

#print axioms exists_conreyDegreeOneEta_simpleZero_finset_of_regularized_trace
