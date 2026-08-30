import HardyTheorem.ConreyMollifiedContourCount

/-!
The final numerator must be the canonical actual simple critical-line zero
count. The subtracted loss uses full mollified multiplicity at the same
fixed parameters, keeping exactly the lower height cutoff U. Both the
bounded version needed by Littlewood and the half-strip version are tested.
-/

open Complex Set
open scoped BigOperators Interval

example {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (hA : 1 / 2 < A) (hU : 0 ≤ U) (hUT : U < T)
    (hedge : ∀ z ∈ (Icc (1 / 2 : ℝ) A ×ℂ Icc U T),
      z.im = U ∨ z.re = A ∨ z.im = T →
        HardyTheorem.conreyDegreeOneEta g g0 g1 L z ≠ 0) :
    ((∫ x in (1 / 2 : ℝ)..A,
        (logDeriv (HardyTheorem.conreyDegreeOneEta g g0 g1 L) ((x : ℂ) + I * U)).im) +
      (∫ t in U..T,
        (logDeriv (HardyTheorem.conreyDegreeOneEta g g0 g1 L) ((A : ℂ) + I * t)).re) -
      (∫ x in (1 / 2 : ℝ)..A,
        (logDeriv (HardyTheorem.conreyDegreeOneEta g g0 g1 L) ((x : ℂ) + I * T)).im)) /
        Real.pi - 2 * ((∑ z ∈ (HardyTheorem.conreyMollifiedV1BoundedZeros
            g g0 g1 L Y sigma0 P A T).filter (fun z => U < z.im),
          analyticOrderNatAt
            (HardyTheorem.conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) z : ℕ) : ℝ) - 1 ≤
          HardyTheorem.positiveCriticalLineSimpleZeroCount T := by
  exact HardyTheorem.conrey_simpleZeroCount_lower_bound_of_three_edges_mollified_bounded
    hg hY hP1 hA hU hUT hedge

example {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (hA : 1 / 2 < A) (hU : 0 ≤ U) (hUT : U < T)
    (hedge : ∀ z ∈ (Icc (1 / 2 : ℝ) A ×ℂ Icc U T),
      z.im = U ∨ z.re = A ∨ z.im = T →
        HardyTheorem.conreyDegreeOneEta g g0 g1 L z ≠ 0) :
    ((∫ x in (1 / 2 : ℝ)..A,
        (logDeriv (HardyTheorem.conreyDegreeOneEta g g0 g1 L) ((x : ℂ) + I * U)).im) +
      (∫ t in U..T,
        (logDeriv (HardyTheorem.conreyDegreeOneEta g g0 g1 L) ((A : ℂ) + I * t)).re) -
      (∫ x in (1 / 2 : ℝ)..A,
        (logDeriv (HardyTheorem.conreyDegreeOneEta g g0 g1 L) ((x : ℂ) + I * T)).im)) /
        Real.pi - 2 * ((∑ z ∈ (HardyTheorem.conreyMollifiedV1HalfStripZeros
            g g0 g1 L Y sigma0 P T).filter (fun z => U < z.im),
          analyticOrderNatAt
            (HardyTheorem.conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) z : ℕ) : ℝ) - 1 ≤
          HardyTheorem.positiveCriticalLineSimpleZeroCount T := by
  exact HardyTheorem.conrey_simpleZeroCount_lower_bound_of_three_edges_mollified_halfStrip
    hg hY hP1 hA hU hUT hedge

#print axioms HardyTheorem.conrey_simpleZeroCount_lower_bound_of_three_edges_mollified_bounded
#print axioms HardyTheorem.conrey_simpleZeroCount_lower_bound_of_three_edges_mollified_halfStrip
