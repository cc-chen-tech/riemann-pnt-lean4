import HardyTheorem.ConreyMollifiedFullCount

/-!
The budget must be full natural-number multiplicity on `(U,T]`, not half
weight on the critical line. It must permit `A > 1` and `U = 0` while only
using the eta/V1 identification at positive-height zeros.
-/

open Complex Set
open scoped BigOperators

example {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) (hU : 0 ≤ U)
    (K : Finset ℂ)
    (hK : ∀ z ∈ K, 1 / 2 ≤ z.re ∧ z.re ≤ A ∧ U < z.im ∧ z.im ≤ T ∧
      HardyTheorem.conreyDegreeOneEta g g0 g1 L z = 0) :
    (∑ z ∈ K, analyticOrderNatAt (HardyTheorem.conreyDegreeOneEta g g0 g1 L) z) ≤
      ∑ z ∈ (HardyTheorem.conreyMollifiedV1BoundedZeros
          g g0 g1 L Y sigma0 P A T).filter (fun z => U < z.im),
        analyticOrderNatAt
          (HardyTheorem.conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) z := by
  exact HardyTheorem.conreyEta_zero_mass_le_mollified_bounded_full hg hY hP1 hU K hK

example {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) :
    (∑ z ∈ (HardyTheorem.conreyMollifiedV1BoundedZeros
        g g0 g1 L Y sigma0 P A T).filter (fun z => U < z.im),
      analyticOrderNatAt
        (HardyTheorem.conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) z) ≤
    ∑ z ∈ (HardyTheorem.conreyMollifiedV1HalfStripZeros
        g g0 g1 L Y sigma0 P T).filter (fun z => U < z.im),
      analyticOrderNatAt
        (HardyTheorem.conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) z := by
  exact HardyTheorem.conreyMollifiedV1BoundedFullZeroCountBetween_le_halfStrip hg hY hP1

#print axioms HardyTheorem.conreyEta_zero_mass_le_mollified_bounded_full
#print axioms HardyTheorem.conreyMollifiedV1BoundedFullZeroCountBetween_le_halfStrip
