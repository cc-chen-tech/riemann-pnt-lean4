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

-- Mutation caught: endpoint nonvanishing must produce a genuine open
-- neighborhood, so the endpoint itself lies inside a logarithm domain.
example {g g0 g1 L u : ℝ}
    (hu : conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint u) ≠ 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ t ∈ Set.Ioo (u - delta) (u + delta),
        conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) ≠ 0 := by
  exact exists_conreyDegreeOneEta_nonzero_real_neighborhood hu

-- Mutation caught: the first component logarithm must include the lower
-- endpoint U in its open domain and extend all the way to the first zero.
example {g g0 g1 L U T tau : ℝ} (hg : g ≠ 0) (hU : 0 ≤ U)
    (hUeta : conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint U) ≠ 0)
    (htau : tau ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T)
    (hfirst : ∀ u ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T,
      tau ≤ u) :
    ∃ delta : ℝ, ∃ ell : ℝ → ℂ,
      0 < delta ∧ U ∈ Set.Ioo (U - delta) tau ∧
      ContinuousOn ell (Set.Ioo (U - delta) tau) ∧
      ∀ t ∈ Set.Ioo (U - delta) tau,
        Complex.exp (ell t) =
          conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) := by
  exact exists_conreyDegreeOneEta_continuousLog_lowerEndpoint_to_firstZero
    hg hU hUeta htau hfirst

-- Mutation caught: the last component logarithm must include T and begin at
-- the last zero; the endpoint nonzero hypothesis excludes tau = T.
example {g g0 g1 L U T tau : ℝ} (hg : g ≠ 0) (hU : 0 ≤ U)
    (hTeta : conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint T) ≠ 0)
    (htau : tau ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T)
    (hlast : ∀ u ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T,
      u ≤ tau) :
    ∃ delta : ℝ, ∃ ell : ℝ → ℂ,
      0 < delta ∧ T ∈ Set.Ioo tau (T + delta) ∧
      ContinuousOn ell (Set.Ioo tau (T + delta)) ∧
      ∀ t ∈ Set.Ioo tau (T + delta),
        Complex.exp (ell t) =
          conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) := by
  exact exists_conreyDegreeOneEta_continuousLog_lastZero_to_upperEndpoint
    hg hU hTeta htau hlast

#print axioms exists_conreyDegreeOneEta_continuousLog_lowerEndpoint_to_firstZero
#print axioms exists_conreyDegreeOneEta_continuousLog_lastZero_to_upperEndpoint

-- Mutation caught: when the equation-(41) zero list is empty, the whole
-- endpoint interval is one component and must use the `.single` partition
-- case rather than inventing a zero bridge.
example {g g0 g1 L U T : ℝ} (hg : g ≠ 0) (hU : 0 ≤ U) (hUT : U ≤ T)
    (hUeta : conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint U) ≠ 0)
    (hTeta : conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint T) ≠ 0)
    (hEmpty : conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T = ∅) :
    ∃ deltaU deltaT : ℝ, ∃ ell : ℝ → ℂ,
      0 < deltaU ∧ 0 < deltaT ∧
      U ∈ Set.Ioo (U - deltaU) (T + deltaT) ∧
      T ∈ Set.Ioo (U - deltaU) (T + deltaT) ∧
      ContinuousOn ell (Set.Ioo (U - deltaU) (T + deltaT)) ∧
      ∀ t ∈ Set.Ioo (U - deltaU) (T + deltaT),
        Complex.exp (ell t) =
          conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) := by
  exact exists_conreyDegreeOneEta_continuousLog_of_zeroInterval_empty
    hg hU hUT hUeta hTeta hEmpty

#print axioms exists_conreyDegreeOneEta_continuousLog_of_zeroInterval_empty
