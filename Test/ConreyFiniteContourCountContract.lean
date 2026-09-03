import HardyTheorem.ConreyFiniteContourCount

/-!
The actual contour count must construct both the complete eta zero table and
genuine zeta simple zeros, without a caller-supplied trace or phase partition.
The loss is twice the full eta multiplicity, including its left-edge zeros.
-/

open Complex Set
open scoped BigOperators Interval

example {g g0 g1 L A U T : ℝ}
    (hg : g ≠ 0) (hA : 1 / 2 < A) (hU : 0 ≤ U) (hUT : U < T)
    (hedge : ∀ z ∈ (Icc (1 / 2 : ℝ) A ×ℂ Icc U T),
      z.im = U ∨ z.re = A ∨ z.im = T →
        HardyTheorem.conreyDegreeOneEta g g0 g1 L z ≠ 0) :
    ∃ (K : Finset ℂ) (S : Finset ℝ),
      (∀ z, z ∈ K ↔ 1 / 2 ≤ z.re ∧ z.re ≤ A ∧ U ≤ z.im ∧ z.im ≤ T ∧
        HardyTheorem.conreyDegreeOneEta g g0 g1 L z = 0) ∧
      (∀ t ∈ S, t ∈ Ioo U T ∧
        riemannZeta (HardyTheorem.conreyCriticalPoint t) = 0 ∧
        analyticOrderNatAt riemannZeta (HardyTheorem.conreyCriticalPoint t) = 1) ∧
      ((∫ x in (1 / 2 : ℝ)..A,
          (logDeriv (HardyTheorem.conreyDegreeOneEta g g0 g1 L) ((x : ℂ) + I * U)).im) +
        (∫ t in U..T,
          (logDeriv (HardyTheorem.conreyDegreeOneEta g g0 g1 L) ((A : ℂ) + I * t)).re) -
        (∫ x in (1 / 2 : ℝ)..A,
          (logDeriv (HardyTheorem.conreyDegreeOneEta g g0 g1 L) ((x : ℂ) + I * T)).im)) /
          Real.pi - 2 * (∑ z ∈ K,
            (analyticOrderNatAt (HardyTheorem.conreyDegreeOneEta g g0 g1 L) z : ℝ)) - 1 ≤
              S.card := by
  exact HardyTheorem.exists_conreyDegreeOneEta_simpleZero_finset_of_three_edges
    hg hA hU hUT hedge

#print axioms HardyTheorem.exists_conreyDegreeOneEta_simpleZero_finset_of_three_edges
