import HardyTheorem.ConreyMollifierRectangleCount

open Complex

namespace HardyTheorem

example (A T : ℝ) : IsCompact (conreyClosedZeroRectangle A T) :=
  isCompact_conreyClosedZeroRectangle A T

example {g g0 g1 L sigma0 : ℝ} {Y : ℕ} {P : ℝ → ℝ} {s : ℂ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) :
    analyticOrderAt
        (conreyRegularizedMollifiedDegreeOneV1
          g g0 g1 L Y sigma0 P) s ≠ ⊤ :=
  analyticOrderAt_conreyRegularizedMollifiedDegreeOneV1_ne_top
    hg hY hP1 s

example {g g0 g1 L A T : ℝ} {s : ℂ} (hg : g ≠ 0) :
    s ∈ conreyV1BoundedZeros g g0 g1 L A T ↔
      1 / 2 ≤ s.re ∧ s.re ≤ A ∧
        0 < s.im ∧ s.im ≤ T ∧
          conreyDegreeOneV1 g g0 g1 L s = 0 :=
  mem_conreyV1BoundedZeros hg

example {g g0 g1 L sigma0 A T : ℝ} {Y : ℕ} {P : ℝ → ℝ} {s : ℂ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) :
    s ∈ conreyMollifiedV1BoundedZeros
        g g0 g1 L Y sigma0 P A T ↔
      1 / 2 ≤ s.re ∧ s.re ≤ A ∧
        0 < s.im ∧ s.im ≤ T ∧
          conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P s = 0 :=
  mem_conreyMollifiedV1BoundedZeros hg hY hP1

example {g g0 g1 L sigma0 A T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) :
    conreyV1BoundedZeros g g0 g1 L A T ⊆
      conreyMollifiedV1BoundedZeros g g0 g1 L Y sigma0 P A T :=
  conreyV1BoundedZeros_subset_mollified hg hY hP1

example {g g0 g1 L sigma0 A T : ℝ} {Y : ℕ} {P : ℝ → ℝ} {s : ℂ}
    (hs : s ∈ conreyV1BoundedZeros g g0 g1 L A T) :
    s ∈ conreyV1MollifiedCriticalBoundaryZeros
        g g0 g1 L Y sigma0 P A T ↔ s.re = 1 / 2 := by
  classical
  simp [conreyV1MollifiedCriticalBoundaryZeros, hs]

example {g g0 g1 L sigma0 A T : ℝ} {Y : ℕ} {P : ℝ → ℝ} {s : ℂ}
    (hs : s ∈ conreyMollifiedV1BoundedZeros
      g g0 g1 L Y sigma0 P A T) :
    s ∈ conreyV1MollifiedCriticalBoundaryZeros
        g g0 g1 L Y sigma0 P A T ↔ s.re = 1 / 2 := by
  classical
  simp [conreyV1MollifiedCriticalBoundaryZeros, hs]

example {g g0 g1 L sigma0 A T : ℝ} {Y : ℕ} {P : ℝ → ℝ} :
    conreyV1BoundedHalfWeightedZeroCount
        g g0 g1 L Y sigma0 P A T =
      MathlibAux.halfWeightedMultiplicityMass
        (conreyV1BoundedZeros g g0 g1 L A T)
        (conreyV1MollifiedCriticalBoundaryZeros
          g g0 g1 L Y sigma0 P A T)
        (analyticOrderNatAt (conreyDegreeOneV1 g g0 g1 L)) := rfl

example {g g0 g1 L sigma0 A T : ℝ} {Y : ℕ} {P : ℝ → ℝ} :
    conreyMollifiedV1BoundedHalfWeightedZeroCount
        g g0 g1 L Y sigma0 P A T =
      MathlibAux.halfWeightedMultiplicityMass
        (conreyMollifiedV1BoundedZeros
          g g0 g1 L Y sigma0 P A T)
        (conreyV1MollifiedCriticalBoundaryZeros
          g g0 g1 L Y sigma0 P A T)
        (analyticOrderNatAt
          (conreyMollifiedDegreeOneV1
            g g0 g1 L Y sigma0 P)) := rfl

example {g g0 g1 L sigma0 A T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) :
    conreyV1BoundedHalfWeightedZeroCount g g0 g1 L Y sigma0 P A T ≤
      conreyMollifiedV1BoundedHalfWeightedZeroCount
        g g0 g1 L Y sigma0 P A T :=
  conreyV1BoundedHalfWeightedZeroCount_le_mollified hg hY hP1

#print axioms analyticOrderAt_conreyRegularizedMollifiedDegreeOneV1_ne_top
#print axioms mem_conreyV1BoundedZeros
#print axioms mem_conreyMollifiedV1BoundedZeros
#print axioms conreyV1BoundedZeros_subset_mollified
#print axioms conreyV1BoundedHalfWeightedZeroCount_le_mollified

end HardyTheorem
