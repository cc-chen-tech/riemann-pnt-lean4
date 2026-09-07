import HardyTheorem.ConreyMollifiedRectangleZeros

/-!
The actual product zero table must cover the full shifted rectangle, retain
left-edge roots, use actual finite orders, and identify full (not half)
multiplicity on Re >= 1/2 with the existing bounded (U,T] count.
-/

open Complex Set
open scoped BigOperators

example {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (hsigma0 : 0 < sigma0) (hsigmaHalf : sigma0 ≤ 1 / 2) (hU : 0 < U)
    (hbottom : ∀ z ∈ (Icc sigma0 A ×ℂ Icc U T), z.im = U →
      HardyTheorem.conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P z ≠ 0) :
    ∃ K : Finset ℂ,
      (∀ z, z ∈ K ↔ sigma0 ≤ z.re ∧ z.re ≤ A ∧ U ≤ z.im ∧ z.im ≤ T ∧
        HardyTheorem.conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P z = 0) ∧
      (∀ z ∈ K,
        analyticOrderAt (HardyTheorem.conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) z =
          analyticOrderNatAt
            (HardyTheorem.conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) z) ∧
      (∑ z ∈ K.filter (fun z => 1 / 2 ≤ z.re),
        analyticOrderNatAt (HardyTheorem.conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) z) =
        HardyTheorem.conreyMollifiedV1BoundedFullZeroCountBetween
          g g0 g1 L Y sigma0 P A U T := by
  exact HardyTheorem.exists_conreyMollified_rectangle_zero_finset
    hg hY hP1 hsigma0 hsigmaHalf hU hbottom

#print axioms HardyTheorem.exists_conreyMollified_rectangle_zero_finset
