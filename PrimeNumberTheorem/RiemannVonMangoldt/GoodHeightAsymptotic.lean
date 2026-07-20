import PrimeNumberTheorem.RiemannVonMangoldt.CountPhaseIdentity

open Complex

namespace PrimeNumberTheorem
namespace RiemannVonMangoldt

/-- Between two good heights, the zero-count increment differs from the
Riemann-von Mangoldt main-term increment by a logarithmic error. -/
theorem exists_abs_zeroCountIncrement_sub_mainTermIncrement_le_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U T : ℝ, 4 ≤ U → 4 ≤ T → U < T →
      ExplicitFormulaAux.goodHeight U →
      ExplicitFormulaAux.goodHeight T →
      |((riemannZeroCount T - riemannZeroCount U : ℕ) : ℝ) -
        (riemannVonMangoldtMainTerm T - riemannVonMangoldtMainTerm U)| ≤
        C * (1 + Real.log (U + 5) + Real.log (T + 5)) := by
  rcases exists_verticalGammaPhase_difference_sub_mainTerm_difference_le_inv_sum with
    ⟨Cgamma, hCgamma, hgamma⟩
  rcases exists_abs_zetaHalfPathArgument_le_log with
    ⟨Czeta, hCzeta, hzeta⟩
  let C : ℝ := Cgamma + Czeta / Real.pi
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro U T hU hT hUT hUgood hTgood
  let gammaError : ℝ :=
    (HardyTheorem.verticalGammaUnwrappedPhase T -
        HardyTheorem.verticalGammaUnwrappedPhase U) / Real.pi -
      (riemannVonMangoldtMainTerm T - riemannVonMangoldtMainTerm U)
  let L : ℝ := 1 + Real.log (U + 5) + Real.log (T + 5)
  have hcount := riemannZeroCount_sub_eq_gammaPhase_add_zetaHalfPathArgument
    hU hUT hUgood hTgood
  have hcountDiv :
      ((riemannZeroCount T - riemannZeroCount U : ℕ) : ℝ) =
        (HardyTheorem.verticalGammaUnwrappedPhase T -
            HardyTheorem.verticalGammaUnwrappedPhase U) / Real.pi +
          zetaHalfPathArgument U T / Real.pi := by
    have hcombined :
        ((riemannZeroCount T - riemannZeroCount U : ℕ) : ℝ) =
          ((HardyTheorem.verticalGammaUnwrappedPhase T -
              HardyTheorem.verticalGammaUnwrappedPhase U) +
            zetaHalfPathArgument U T) / Real.pi := by
      apply (eq_div_iff Real.pi_ne_zero).2
      simpa [mul_comm, add_assoc] using hcount
    rw [hcombined]
    ring
  have hrewrite :
      ((riemannZeroCount T - riemannZeroCount U : ℕ) : ℝ) -
          (riemannVonMangoldtMainTerm T - riemannVonMangoldtMainTerm U) =
        gammaError + zetaHalfPathArgument U T / Real.pi := by
    rw [hcountDiv]
    dsimp [gammaError]
    ring
  have hgammaBound : |gammaError| ≤ Cgamma / U + Cgamma / T := by
    exact hgamma U T (by linarith) (by linarith)
  have hzetaBound : |zetaHalfPathArgument U T| ≤ Czeta * L := by
    exact hzeta U T hU hT hUgood hTgood
  have hlogU : 0 ≤ Real.log (U + 5) :=
    Real.log_nonneg (by linarith)
  have hlogT : 0 ≤ Real.log (T + 5) :=
    Real.log_nonneg (by linarith)
  have hL : 1 ≤ L := by
    dsimp [L]
    linarith
  have hgammaU : Cgamma / U ≤ Cgamma / 4 :=
    div_le_div_of_nonneg_left hCgamma (by norm_num) hU
  have hgammaT : Cgamma / T ≤ Cgamma / 4 :=
    div_le_div_of_nonneg_left hCgamma (by norm_num) hT
  have hgammaSimple : Cgamma / U + Cgamma / T ≤ Cgamma := by
    nlinarith
  have hzetaDiv :
      |zetaHalfPathArgument U T / Real.pi| ≤
        (Czeta * L) / Real.pi := by
    rw [abs_div, abs_of_pos Real.pi_pos]
    exact div_le_div_of_nonneg_right hzetaBound Real.pi_pos.le
  rw [hrewrite]
  calc
    |gammaError + zetaHalfPathArgument U T / Real.pi| ≤
        |gammaError| + |zetaHalfPathArgument U T / Real.pi| :=
      abs_add_le _ _
    _ ≤ (Cgamma / U + Cgamma / T) + (Czeta * L) / Real.pi :=
      add_le_add hgammaBound hzetaDiv
    _ ≤ Cgamma + (Czeta * L) / Real.pi :=
      add_le_add hgammaSimple le_rfl
    _ = Cgamma + (Czeta / Real.pi) * L := by ring
    _ ≤ Cgamma * L + (Czeta / Real.pi) * L := by
      gcongr
      nlinarith
    _ = C * L := by
      dsimp [C]
      ring

/-- At every good height `T ≥ 6`, the standard zero count satisfies the
Riemann-von Mangoldt formula with logarithmic error. -/
theorem exists_abs_riemannZeroCount_sub_mainTerm_le_log_of_goodHeight :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 6 ≤ T →
      ExplicitFormulaAux.goodHeight T →
      |(riemannZeroCount T : ℝ) - riemannVonMangoldtMainTerm T| ≤
        C * (1 + Real.log (T + 5)) := by
  rcases ExplicitFormulaAux.exists_goodHeight_Ioo 4 with
    ⟨U, hU4, hU5, hUgood⟩
  rcases exists_abs_zeroCountIncrement_sub_mainTermIncrement_le_log with
    ⟨Cinc, hCinc, hinc⟩
  let baseline : ℝ :=
    (riemannZeroCount U : ℝ) - riemannVonMangoldtMainTerm U
  let C : ℝ :=
    Cinc * (1 + Real.log (U + 5)) + |baseline|
  have hlogU : 0 ≤ Real.log (U + 5) :=
    Real.log_nonneg (by linarith)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro T hT hTgood
  have hUT : U < T := by linarith
  have hmono : riemannZeroCount U ≤ riemannZeroCount T :=
    riemannZeroCount_mono hUT.le
  have hincT := hinc U T hU4.le (by linarith) hUT hUgood hTgood
  rw [Nat.cast_sub hmono] at hincT
  have hlogT : 0 ≤ Real.log (T + 5) :=
    Real.log_nonneg (by linarith)
  have hrewrite :
      (riemannZeroCount T : ℝ) - riemannVonMangoldtMainTerm T =
        (((riemannZeroCount T : ℝ) - (riemannZeroCount U : ℝ)) -
          (riemannVonMangoldtMainTerm T - riemannVonMangoldtMainTerm U)) +
        baseline := by
    dsimp [baseline]
    ring
  have hextra :
      0 ≤ (Cinc * Real.log (U + 5) + |baseline|) *
        Real.log (T + 5) := by
    positivity
  rw [hrewrite]
  calc
    |((riemannZeroCount T : ℝ) - (riemannZeroCount U : ℝ) -
          (riemannVonMangoldtMainTerm T - riemannVonMangoldtMainTerm U)) +
        baseline| ≤
        |(riemannZeroCount T : ℝ) - (riemannZeroCount U : ℝ) -
          (riemannVonMangoldtMainTerm T - riemannVonMangoldtMainTerm U)| +
        |baseline| := abs_add_le _ _
    _ ≤ Cinc * (1 + Real.log (U + 5) + Real.log (T + 5)) +
        |baseline| := add_le_add hincT le_rfl
    _ ≤ C * (1 + Real.log (T + 5)) := by
      dsimp [C]
      nlinarith

end RiemannVonMangoldt
end PrimeNumberTheorem
