import HardyTheorem.ConreyEquation35Global

open Complex

namespace HardyTheorem

example {g g0 g1 L sigma0 : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) {s : ℂ}
    (hs : conreyEquation35FarRightEdge g g0 g1 L Y sigma0 P ≤ s.re) :
    conreyDegreeOneV1 g g0 g1 L s ≠ 0 ∧
      conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P s ≠ 0 :=
  conreyEquation35FarRight_nonzero hg hY hP1 hs

example {g g0 g1 L sigma0 T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) {s : ℂ} :
    s ∈ conreyV1HalfStripZeros g g0 g1 L Y sigma0 P T ↔
      1 / 2 ≤ s.re ∧ 0 < s.im ∧ s.im ≤ T ∧
        conreyDegreeOneV1 g g0 g1 L s = 0 :=
  mem_conreyV1HalfStripZeros hg hY hP1

example {g g0 g1 L sigma0 T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) {s : ℂ} :
    s ∈ conreyMollifiedV1HalfStripZeros
        g g0 g1 L Y sigma0 P T ↔
      1 / 2 ≤ s.re ∧ 0 < s.im ∧ s.im ≤ T ∧
        conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P s = 0 :=
  mem_conreyMollifiedV1HalfStripZeros hg hY hP1

example {g g0 g1 L sigma0 T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) :
    conreyV1HalfStripHalfWeightedZeroCount
        g g0 g1 L Y sigma0 P T ≤
      conreyMollifiedV1HalfStripHalfWeightedZeroCount
        g g0 g1 L Y sigma0 P T :=
  conreyV1HalfStripHalfWeightedZeroCount_le_mollified hg hY hP1

#print axioms conreyEquation35FarRight_nonzero
#print axioms mem_conreyV1HalfStripZeros
#print axioms mem_conreyMollifiedV1HalfStripZeros
#print axioms conreyV1HalfStripHalfWeightedZeroCount_le_mollified

end HardyTheorem
