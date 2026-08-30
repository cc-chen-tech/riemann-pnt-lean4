import HardyTheorem.ConreyEquation37Edges

open Complex HardyTheorem

#check conreyHorizontalRightEdge_add_three_lt_exp
#check conreyEquation37HorizontalTerm
#check conreyEquation37BoundaryRemainder
#check exists_conreyEquation37SelectedHeights_boundaryRemainder_le

-- Lock the selected windows, zero-free horizontal sides, and complete bound.
example :
    ∃ Creg Cmass : ℝ, 1 ≤ Creg ∧ 1 ≤ Cmass ∧
      ∀ {Y : ℕ} {R L : ℝ}, 2 ≤ Y →
        (Y : ℝ) ≤ Real.exp L → 0 ≤ R → R ≤ 6 / 5 → 40000 ≤ L →
        Creg ≤ Real.exp L → Cmass ≤ Real.exp L →
        ∃ t0 t1 : ℝ,
          t0 ∈ Set.Icc (conreyHorizontalRightEdge L + 1)
              (conreyHorizontalRightEdge L + 2) ∧
          t1 ∈ Set.Icc (Real.exp L - 1) (Real.exp L) ∧
          t0 < t1 ∧
          (∀ x ∈ Set.Icc (conreyHorizontalLeftEdge R L)
              (conreyHorizontalRightEdge L),
            conreyHorizontalJensenProduct Y R L
              ((x : ℂ) + I * (t0 : ℂ)) ≠ 0) ∧
          (∀ x ∈ Set.Icc (conreyHorizontalLeftEdge R L)
              (conreyHorizontalRightEdge L),
            conreyHorizontalJensenProduct Y R L
              ((x : ℂ) + I * (t1 : ℂ)) ≠ 0) ∧
          |conreyEquation37HorizontalTerm Y R L t0| ≤
              1100000000000 * L ^ 7 ∧
          |conreyEquation37HorizontalTerm Y R L t1| ≤
              1100000000000 * L ^ 7 ∧
          |conreyEquation37BoundaryRemainder Y R L t0 t1| ≤
            507 * Real.exp L / L + 2200000000000 * L ^ 7 +
              (conreyHorizontalRightEdge L -
                conreyHorizontalLeftEdge R L) * Real.pi :=
  exists_conreyEquation37SelectedHeights_boundaryRemainder_le

#print axioms conreyHorizontalRightEdge_add_three_lt_exp
#print axioms exists_conreyEquation37SelectedHeights_boundaryRemainder_le
