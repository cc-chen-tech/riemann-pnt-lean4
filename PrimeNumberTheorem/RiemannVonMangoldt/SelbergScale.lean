import PrimeNumberTheorem.RiemannVonMangoldt.AllHeightAsymptotic

open Filter Set

namespace PrimeNumberTheorem
namespace RiemannVonMangoldt

/-- The multiplicity-weighted count of all nontrivial zeros has the same
`T log T / (2 pi)` scale used to normalize Selberg's critical-line target.

This is an all-zero statement only: it does not compare `riemannZeroCount`
with `HardyTheorem.zeroCountOnCriticalLine`. -/
theorem exists_eventually_riemannZeroCount_ge_selbergScale :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T in atTop,
      c * (T / (2 * Real.pi) * Real.log T) ≤ (riemannZeroCount T : ℝ) := by
  rcases exists_abs_riemannZeroCount_sub_mainTerm_le_log with ⟨C, hC, herror⟩
  refine ⟨1 / 4, by norm_num, ?_⟩
  let D : ℝ := 2 * Real.pi
  let T0 : ℝ := max 8 (max (Real.exp (2 * (Real.log D + 1)) )
    (max (Real.exp 1) (12 * D * C)))
  filter_upwards [eventually_ge_atTop T0] with T hT
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hD_one : 1 < D := by
    dsimp [D]
    nlinarith [Real.pi_gt_three]
  have hlogD_nonneg : 0 ≤ Real.log D := Real.log_nonneg hD_one.le
  have hT8 : 8 ≤ T := le_trans (le_max_left 8 (max (Real.exp (2 * (Real.log D + 1)))
    (max (Real.exp 1) (12 * D * C)))) hT
  have hTexp : Real.exp (2 * (Real.log D + 1)) ≤ T :=
    le_trans (le_max_left (Real.exp (2 * (Real.log D + 1)))
      (max (Real.exp 1) (12 * D * C)))
      (le_trans (le_max_right 8 (max (Real.exp (2 * (Real.log D + 1)))
        (max (Real.exp 1) (12 * D * C)))) hT)
  have hTe : Real.exp 1 ≤ T :=
    le_trans (le_max_left (Real.exp 1) (12 * D * C))
      (le_trans (le_max_right (Real.exp (2 * (Real.log D + 1)))
        (max (Real.exp 1) (12 * D * C)))
        (le_trans (le_max_right 8 (max (Real.exp (2 * (Real.log D + 1)))
          (max (Real.exp 1) (12 * D * C)))) hT))
  have hTC : 12 * D * C ≤ T :=
    le_trans (le_max_right (Real.exp 1) (12 * D * C))
      (le_trans (le_max_right (Real.exp (2 * (Real.log D + 1)))
        (max (Real.exp 1) (12 * D * C)))
        (le_trans (le_max_right 8 (max (Real.exp (2 * (Real.log D + 1)))
          (max (Real.exp 1) (12 * D * C)))) hT))
  have hTpos : 0 < T := by linarith
  have hlogT_one : 1 ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 1) hTe
    simpa using this
  have hlogT_large : 2 * (Real.log D + 1) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos (2 * (Real.log D + 1))) hTexp
    simpa using this
  have hlogT_nonneg : 0 ≤ Real.log T := hlogT_one.trans' (by norm_num)
  have hlog_main : Real.log (T / D) = Real.log T - Real.log D := by
    rw [Real.log_div hTpos.ne' hDpos.ne']
  have hmain :
      (1 / 2 : ℝ) * (T / D * Real.log T) ≤ riemannVonMangoldtMainTerm T := by
    rw [riemannVonMangoldtMainTerm, hlog_main]
    have hfactor : (1 / 2 : ℝ) * Real.log T ≤ Real.log T - Real.log D - 1 := by
      linarith
    have hTD_nonneg : 0 ≤ T / D := div_nonneg hTpos.le hDpos.le
    nlinarith [mul_le_mul_of_nonneg_left hfactor hTD_nonneg]
  have hlogTplus6 : Real.log (T + 6) ≤ 2 * Real.log T := by
    have hsum : T + 6 ≤ 2 * T := by linarith
    calc
      Real.log (T + 6) ≤ Real.log (2 * T) :=
        Real.log_le_log (by linarith) hsum
      _ = Real.log 2 + Real.log T := by rw [Real.log_mul (by norm_num) hTpos.ne']
      _ ≤ Real.log T + Real.log T := by
        have hlog2 : Real.log 2 ≤ Real.log T :=
          Real.log_le_log (by norm_num) (by linarith)
        linarith
      _ = 2 * Real.log T := by ring
  have herror_small : C * (1 + Real.log (T + 6)) ≤
      (1 / 4 : ℝ) * (T / D * Real.log T) := by
    have hthreeC : 3 * C ≤ T / (4 * D) := by
      apply (le_div_iff₀ (by positivity : 0 < 4 * D)).2
      nlinarith
    have hleft : C * (1 + Real.log (T + 6)) ≤ 3 * C * Real.log T := by
      have hinner : 1 + Real.log (T + 6) ≤ 3 * Real.log T := by
        linarith
      calc
        C * (1 + Real.log (T + 6)) ≤ C * (3 * Real.log T) :=
          mul_le_mul_of_nonneg_left hinner hC
        _ = 3 * C * Real.log T := by ring
    calc
      C * (1 + Real.log (T + 6)) ≤ 3 * C * Real.log T := hleft
      _ ≤ (T / (4 * D)) * Real.log T :=
        mul_le_mul_of_nonneg_right hthreeC hlogT_nonneg
      _ = (1 / 4 : ℝ) * (T / D * Real.log T) := by ring
  have hcount_error := herror T hT8
  have hcount_lower : riemannVonMangoldtMainTerm T - C * (1 + Real.log (T + 6)) ≤
      (riemannZeroCount T : ℝ) := by
    rw [abs_le] at hcount_error
    linarith
  change (1 / 4 : ℝ) * (T / D * Real.log T) ≤ (riemannZeroCount T : ℝ)
  linarith

end RiemannVonMangoldt
end PrimeNumberTheorem
