import HardyTheorem.ConreySelectedEtaMainCount

open Complex Set HardyTheorem

/-! The actual selected-height mean-square count with eta eliminated by
its proved integral main term, preserving the original long product. -/

example : ∃ L0 : ℝ, 40000 ≤ L0 ∧ ∀ {Y : ℕ} {R L : ℝ},
    2 ≤ Y → (Y : ℝ) ≤ Real.exp L → 0 < R → R ≤ 6 / 5 → L0 ≤ L →
    ∃ U T : ℝ,
      U ∈ Icc (2 * Real.log L + 1) (2 * Real.log L + 2) ∧
      T ∈ Icc (Real.exp L - 1) (Real.exp L) ∧ U < T ∧
      (∀ z ∈ (Icc (1 / 2 - R / L) (2 * Real.log L) ×ℂ Icc U T),
        z.im = U ∨ z.re = 2 * Real.log L ∨ z.im = T →
          conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
            (1 / 2 - R / L) conreyExplicitP z ≠ 0) ∧
      0 < (∫ t in U..T,
        ‖conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
          (1 / 2 - R / L) conreyExplicitP
          (((1 / 2 - R / L : ℝ) : ℂ) + I * t)‖ ^ 2) ∧
      conreyEtaThreeEdgeLowerMain L U T / Real.pi -
        ((T - U) * Real.log ((∫ t in U..T,
          ‖conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
            (1 / 2 - R / L) conreyExplicitP
            (((1 / 2 - R / L : ℝ) : ℂ) + I * t)‖ ^ 2) / (T - U)) +
          2 * (507 * Real.exp L / L + 2200000000000 * L ^ 7 +
            (2 * Real.log L - (1 / 2 - R / L)) * Real.pi)) /
          (2 * Real.pi * (R / L)) - 1 ≤ positiveCriticalLineSimpleZeroCount (Real.exp L) :=
  exists_conrey_selected_heights_simpleZeroCount_lower_bound_logMain

#print axioms exists_conrey_selected_heights_simpleZeroCount_lower_bound_logMain
