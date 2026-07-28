import PrimeNumberTheorem.ZeroDensityLayerBudgetPsi0FloorRounding

open Filter Topology Asymptotics

namespace PrimeNumberTheorem

/--
Public pointwise logarithmic bound for the real-input von Mangoldt jump.
-/
theorem jumpVonMangoldt_nonneg_le_log_of_one_le
    {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ jumpVonMangoldt x ∧ jumpVonMangoldt x ≤ Real.log x := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  constructor
  · classical
    rw [jumpVonMangoldt]
    split_ifs with h
    · rw [vonMangoldt_eq_mathlib]
      exact ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl
  · classical
    rw [jumpVonMangoldt]
    split_ifs with h
    · have hchoose := Classical.choose_spec h
      rw [vonMangoldt_eq_mathlib]
      calc
        ArithmeticFunction.vonMangoldt (Classical.choose h) ≤
            Real.log ((Classical.choose h : ℕ) : ℝ) :=
          ArithmeticFunction.vonMangoldt_le_log
        _ = Real.log x := by rw [← hchoose]
    · exact hlog

/--
The full midpoint floor-rounding budget is at most logarithmic plus one.
-/
theorem chebyshevPsi0FloorRoundingBudget_le_log_add_one
    {x : ℝ} (hx : 1 ≤ x) :
    chebyshevPsi0FloorRoundingBudget x ≤ Real.log x + 1 := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hfloorLe : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx0
  have hfloorNat : 1 ≤ Nat.floor x :=
    (Nat.le_floor_iff hx0).2 (by simpa using hx)
  have hfloorOne : (1 : ℝ) ≤ (Nat.floor x : ℝ) := by
    exact_mod_cast hfloorNat
  have hfloorPos : 0 < (Nat.floor x : ℝ) := zero_lt_one.trans_le hfloorOne
  rcases jumpVonMangoldt_nonneg_le_log_of_one_le hx with
    ⟨hjump0, hjumpLog⟩
  rcases jumpVonMangoldt_nonneg_le_log_of_one_le hfloorOne with
    ⟨hfloorJump0, hfloorJumpLog⟩
  have hlogFloor : Real.log (Nat.floor x : ℝ) ≤ Real.log x :=
    Real.log_le_log hfloorPos hfloorLe
  have hdist0 : 0 ≤ x - (Nat.floor x : ℝ) :=
    sub_nonneg.mpr hfloorLe
  have hdist : x - (Nat.floor x : ℝ) ≤ 1 := by
    have hlt : x < (Nat.floor x : ℝ) + 1 := by
      simpa using Nat.lt_floor_add_one x
    linarith
  unfold chebyshevPsi0FloorRoundingBudget
  rw [abs_of_nonneg hjump0, abs_of_nonneg hfloorJump0,
    abs_of_nonneg hdist0]
  linarith

/--
For every positive target real part `beta`, floor rounding is negligible
relative to the zero-forced power scale `x^beta`.
-/
theorem chebyshevPsi0FloorRoundingBudget_isLittleO_targetPower
    {beta : ℝ} (hbeta : 0 < beta) :
    (fun x : ℝ => chebyshevPsi0FloorRoundingBudget x)
      =o[atTop] (fun x : ℝ => x ^ beta) := by
  have hbudgetLog :
      (fun x : ℝ => chebyshevPsi0FloorRoundingBudget x)
        =O[atTop] Real.log := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
    have hxone : 1 ≤ x := by
      have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
      exact this.trans hx
    have hlogOne : 1 ≤ Real.log x :=
      (Real.le_log_iff_exp_le hxpos).2 hx
    have hbudget :=
      chebyshevPsi0FloorRoundingBudget_le_log_add_one hxone
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (chebyshevPsi0FloorRoundingBudget_nonneg x),
      abs_of_nonneg (by linarith : 0 ≤ Real.log x)]
    linarith
  exact
    hbudgetLog.trans_isLittleO
      (isLittleO_log_rpow_atTop hbeta)

end PrimeNumberTheorem
