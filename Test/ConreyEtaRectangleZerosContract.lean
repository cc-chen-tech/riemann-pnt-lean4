import HardyTheorem.ConreyEtaRectangleZeros

/-!
Construct all zeros of actual eta in the closed rectangle, not only its
critical-line zeros. The filtered left-edge analytic mass must equal the
existing ordinate-based budget, with the lower endpoint excluded exactly.
-/

open Complex Set
open scoped BigOperators

example {g g0 g1 L A U T : ℝ}
    (hg : g ≠ 0) (hA : 1 / 2 ≤ A) (hU : 0 ≤ U)
    (hbase : HardyTheorem.conreyDegreeOneEta g g0 g1 L
      (HardyTheorem.conreyCriticalPoint U) ≠ 0) :
    ∃ K : Finset ℂ,
      (∀ z, z ∈ K ↔ 1 / 2 ≤ z.re ∧ z.re ≤ A ∧ U ≤ z.im ∧ z.im ≤ T ∧
        HardyTheorem.conreyDegreeOneEta g g0 g1 L z = 0) ∧
      (∑ z ∈ K.filter (fun z => z.re = 1 / 2),
        analyticOrderNatAt (HardyTheorem.conreyDegreeOneEta g g0 g1 L) z) =
        HardyTheorem.conreyEtaCriticalZeroMultiplicityMassBetween g g0 g1 L U T := by
  exact HardyTheorem.exists_conreyDegreeOneEta_rectangle_zero_finset hg hA hU hbase

#print axioms HardyTheorem.exists_conreyDegreeOneEta_rectangle_zero_finset
