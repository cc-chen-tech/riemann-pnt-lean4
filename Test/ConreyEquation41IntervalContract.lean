import HardyTheorem.ConreyEquation41Global

open Complex Set
open HardyTheorem

-- Mutation caught: a zero in a purported consecutive `(U,T]` gap must be
-- returned to the same interval zero list and contradict the gap hypothesis.
example {g g0 g1 L U T a b t : ℝ} (hg : g ≠ 0) (hU : 0 ≤ U)
    (ha : a ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T)
    (hb : b ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T)
    (hgap : ∀ u ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T,
      ¬ (a < u ∧ u < b))
    (ht : t ∈ Set.Ioo a b) :
    conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) ≠ 0 := by
  exact conreyDegreeOneEta_ne_zero_between_consecutiveCriticalZeroOrdinatesBetween
    hg hU ha hb hgap ht

-- Mutation caught: component arguments require one logarithm continuous on
-- the entire gap, not unrelated pointwise logarithms.
example {g g0 g1 L U T a b : ℝ} (hg : g ≠ 0) (hU : 0 ≤ U)
    (hab : a < b)
    (ha : a ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T)
    (hb : b ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T)
    (hgap : ∀ u ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T,
      ¬ (a < u ∧ u < b)) :
    ∃ ell : ℝ → ℂ,
      ContinuousOn ell (Set.Ioo a b) ∧
      ∀ t ∈ Set.Ioo a b,
        Complex.exp (ell t) =
          conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) := by
  exact
    exists_conreyDegreeOneEta_continuousLog_between_consecutiveCriticalZeroOrdinatesBetween
      hg hU hab ha hb hgap

#print axioms
  exists_conreyDegreeOneEta_continuousLog_between_consecutiveCriticalZeroOrdinatesBetween
