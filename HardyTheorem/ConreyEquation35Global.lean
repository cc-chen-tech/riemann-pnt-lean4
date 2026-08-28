import HardyTheorem.ConreyFarRight

/-!
# Global half-strip form of Conrey's equation (35)

The uniform far-right theorem supplies one vertical line, independent of the
height, beyond which both `V1` and `V1 * B` are nonzero.  Evaluating the
bounded divisor families at that line therefore gives finite representations
of the actual unbounded right-half-strip zero families.
-/

open Complex Set

namespace HardyTheorem

/-- A canonical common right edge for equation (35).  Outside Conrey's
normalization hypotheses it is defined to be zero; every theorem using its
zero-free property states those hypotheses explicitly. -/
noncomputable def conreyEquation35FarRightEdge
    (g g0 g1 L : ℝ) (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ) : ℝ :=
  if h : g ≠ 0 ∧ 2 ≤ Y ∧ P 1 = 1 then
    Classical.choose
      (exists_conreyMollifiedDegreeOneV1_ne_zero_of_re_ge
        (g0 := g0) (g1 := g1) (L := L) (sigma0 := sigma0)
        h.1 h.2.1 h.2.2)
  else 0

/-- On the canonical edge and everywhere to its right, both the degree-one
factor and its actual mollified product are nonzero, uniformly in height. -/
theorem conreyEquation35FarRight_nonzero
    {g g0 g1 L sigma0 : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) {s : ℂ}
    (hs : conreyEquation35FarRightEdge
      g g0 g1 L Y sigma0 P ≤ s.re) :
    conreyDegreeOneV1 g g0 g1 L s ≠ 0 ∧
      conreyMollifiedDegreeOneV1
        g g0 g1 L Y sigma0 P s ≠ 0 := by
  have hadm : g ≠ 0 ∧ 2 ≤ Y ∧ P 1 = 1 := ⟨hg, hY, hP1⟩
  have hproduct : conreyMollifiedDegreeOneV1
      g g0 g1 L Y sigma0 P s ≠ 0 := by
    have hspec := Classical.choose_spec
      (exists_conreyMollifiedDegreeOneV1_ne_zero_of_re_ge
        (g0 := g0) (g1 := g1) (L := L) (sigma0 := sigma0)
        hg hY hP1)
    apply hspec s
    simpa [conreyEquation35FarRightEdge, hadm] using hs
  have hV : conreyDegreeOneV1 g g0 g1 L s ≠ 0 := by
    intro hzero
    apply hproduct
    exact conreyMollifiedDegreeOneV1_eq_zero_of_v1_eq_zero hzero
  exact ⟨hV, hproduct⟩

/-- Finite representation of all positive-height `V1` zeros in the unbounded
half-strip `Re s >= 1/2`, `Im s <= T`. -/
noncomputable def conreyV1HalfStripZeros
    (g g0 g1 L : ℝ) (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ)
    (T : ℝ) : Finset ℂ :=
  conreyV1BoundedZeros g g0 g1 L
    (conreyEquation35FarRightEdge g g0 g1 L Y sigma0 P) T

/-- Finite representation of all positive-height `V1 * B` zeros in the
unbounded half-strip `Re s >= 1/2`, `Im s <= T`. -/
noncomputable def conreyMollifiedV1HalfStripZeros
    (g g0 g1 L : ℝ) (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ)
    (T : ℝ) : Finset ℂ :=
  conreyMollifiedV1BoundedZeros g g0 g1 L Y sigma0 P
    (conreyEquation35FarRightEdge g g0 g1 L Y sigma0 P) T

theorem mem_conreyV1HalfStripZeros
    {g g0 g1 L sigma0 T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) {s : ℂ} :
    s ∈ conreyV1HalfStripZeros g g0 g1 L Y sigma0 P T ↔
      1 / 2 ≤ s.re ∧ 0 < s.im ∧ s.im ≤ T ∧
        conreyDegreeOneV1 g g0 g1 L s = 0 := by
  rw [conreyV1HalfStripZeros, mem_conreyV1BoundedZeros hg]
  constructor
  · rintro ⟨hsre, _hsedge, hsim, hsimT, hzero⟩
    exact ⟨hsre, hsim, hsimT, hzero⟩
  · rintro ⟨hsre, hsim, hsimT, hzero⟩
    have hsedge : s.re ≤ conreyEquation35FarRightEdge
        g g0 g1 L Y sigma0 P := by
      by_contra hnot
      have hright : conreyEquation35FarRightEdge
          g g0 g1 L Y sigma0 P ≤ s.re :=
        (lt_of_not_ge hnot).le
      exact (conreyEquation35FarRight_nonzero hg hY hP1 hright).1 hzero
    exact ⟨hsre, hsedge, hsim, hsimT, hzero⟩

theorem mem_conreyMollifiedV1HalfStripZeros
    {g g0 g1 L sigma0 T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) {s : ℂ} :
    s ∈ conreyMollifiedV1HalfStripZeros
        g g0 g1 L Y sigma0 P T ↔
      1 / 2 ≤ s.re ∧ 0 < s.im ∧ s.im ≤ T ∧
        conreyMollifiedDegreeOneV1
          g g0 g1 L Y sigma0 P s = 0 := by
  rw [conreyMollifiedV1HalfStripZeros,
    mem_conreyMollifiedV1BoundedZeros hg hY hP1]
  constructor
  · rintro ⟨hsre, _hsedge, hsim, hsimT, hzero⟩
    exact ⟨hsre, hsim, hsimT, hzero⟩
  · rintro ⟨hsre, hsim, hsimT, hzero⟩
    have hsedge : s.re ≤ conreyEquation35FarRightEdge
        g g0 g1 L Y sigma0 P := by
      by_contra hnot
      have hright : conreyEquation35FarRightEdge
          g g0 g1 L Y sigma0 P ≤ s.re :=
        (lt_of_not_ge hnot).le
      exact (conreyEquation35FarRight_nonzero hg hY hP1 hright).2 hzero
    exact ⟨hsre, hsedge, hsim, hsimT, hzero⟩

/-- Shared critical-line boundary of the two actual half-strip zero
families. -/
noncomputable def conreyV1MollifiedHalfStripCriticalBoundaryZeros
    (g g0 g1 L : ℝ) (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ)
    (T : ℝ) : Finset ℂ :=
  (conreyV1HalfStripZeros g g0 g1 L Y sigma0 P T ∪
    conreyMollifiedV1HalfStripZeros g g0 g1 L Y sigma0 P T).filter
      fun s => s.re = 1 / 2

/-- Actual half-weighted `V1` zero count on the unbounded right half-strip. -/
noncomputable def conreyV1HalfStripHalfWeightedZeroCount
    (g g0 g1 L : ℝ) (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ)
    (T : ℝ) : ℝ :=
  MathlibAux.halfWeightedMultiplicityMass
    (conreyV1HalfStripZeros g g0 g1 L Y sigma0 P T)
    (conreyV1MollifiedHalfStripCriticalBoundaryZeros
      g g0 g1 L Y sigma0 P T)
    (analyticOrderNatAt (conreyDegreeOneV1 g g0 g1 L))

/-- Actual half-weighted `V1 * B` zero count on the unbounded right
half-strip. -/
noncomputable def conreyMollifiedV1HalfStripHalfWeightedZeroCount
    (g g0 g1 L : ℝ) (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ)
    (T : ℝ) : ℝ :=
  MathlibAux.halfWeightedMultiplicityMass
    (conreyMollifiedV1HalfStripZeros g g0 g1 L Y sigma0 P T)
    (conreyV1MollifiedHalfStripCriticalBoundaryZeros
      g g0 g1 L Y sigma0 P T)
    (analyticOrderNatAt
      (conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P))

/-- Global half-strip form of Conrey's equation (35), with actual analytic
multiplicities and exact half weight on the critical line. -/
theorem conreyV1HalfStripHalfWeightedZeroCount_le_mollified
    {g g0 g1 L sigma0 T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) :
    conreyV1HalfStripHalfWeightedZeroCount
        g g0 g1 L Y sigma0 P T ≤
      conreyMollifiedV1HalfStripHalfWeightedZeroCount
        g g0 g1 L Y sigma0 P T := by
  simpa [conreyV1HalfStripHalfWeightedZeroCount,
    conreyMollifiedV1HalfStripHalfWeightedZeroCount,
    conreyV1MollifiedHalfStripCriticalBoundaryZeros,
    conreyV1HalfStripZeros, conreyMollifiedV1HalfStripZeros,
    conreyV1BoundedHalfWeightedZeroCount,
    conreyMollifiedV1BoundedHalfWeightedZeroCount,
    conreyV1MollifiedCriticalBoundaryZeros] using
      (conreyV1BoundedHalfWeightedZeroCount_le_mollified
        (A := conreyEquation35FarRightEdge
          g g0 g1 L Y sigma0 P) (T := T) hg hY hP1)

end HardyTheorem
