import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace HardyTheorem

/-!
# An explicit numerical certificate for Conrey's two-fifths inequality

This file formalizes only the exact final numerical calculation.  It does not
formalize the analytic mean-square theorem or the Deshouillers--Iwaniec
spectral estimate used to obtain that mean square.

The parameters are

* `theta = 571 / 1000`,
* `R = 6 / 5`,
* `Q(y) = 1 - 51 y / 50`, and
* `P(x) = (84 x + 15 x^3 + x^5) / 100`.

Expanding Conrey's mean-square integral for these polynomials gives the exact
constant defined below.
-/

/-- The mollifier-length exponent in the explicit certificate. -/
noncomputable def conreyExplicitTheta : ℝ := 571 / 1000

/-- The horizontal shift parameter in the explicit certificate. -/
noncomputable def conreyExplicitR : ℝ := 6 / 5

/-- The exact expansion of Conrey's mean-square constant for the parameters
recorded in the module docstring. -/
noncomputable def conreyExplicitMeanSquareConstant : ℝ :=
  -(7119751197749681 / 5935545000000000 : ℝ) +
    (43767545344030157 / 148388625000000000 : ℝ) * Real.exp (12 / 5)

theorem conreyExplicitTheta_lt_four_sevenths :
    conreyExplicitTheta < (4 : ℝ) / 7 := by
  norm_num [conreyExplicitTheta]

private theorem exp_twelve_fifths_lt :
    Real.exp (12 / 5 : ℝ) < (110231764 : ℝ) / 10000000 := by
  let U : ℝ :=
    (∑ m ∈ Finset.range 10, ((4 : ℝ) / 5) ^ m / m.factorial) +
      ((4 : ℝ) / 5) ^ 10 * (10 + 1) / (Nat.factorial 10 * 10)
  have hexp : Real.exp ((4 : ℝ) / 5) ≤ U := by
    simpa [U] using
      (Real.exp_bound' (x := (4 : ℝ) / 5) (by norm_num) (by norm_num)
        (n := 10) (by norm_num))
  have hcube : U ^ 3 < (110231764 : ℝ) / 10000000 := by
    norm_num [U, Finset.sum_range_succ, Nat.factorial]
  calc
    Real.exp (12 / 5 : ℝ) = Real.exp ((3 : ℕ) * ((4 : ℝ) / 5)) := by norm_num
    _ = Real.exp ((4 : ℝ) / 5) ^ 3 := Real.exp_nat_mul _ _
    _ ≤ U ^ 3 := by gcongr
    _ < (110231764 : ℝ) / 10000000 := hcube

private theorem rational_lt_exp_eighteen_twenty_fifths :
    (20544332 : ℝ) / 10000000 < Real.exp (18 / 25 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (x := (18 : ℝ) / 25) (by norm_num) 11
  apply lt_of_lt_of_le _ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem conreyExplicitMeanSquareConstant_lt_rational :
    conreyExplicitMeanSquareConstant <
      (253719660815417568775579 : ℝ) / 123657187500000000000000 := by
  have h := exp_twelve_fifths_lt
  norm_num [conreyExplicitMeanSquareConstant] at *
  nlinarith

theorem conreyExplicitMeanSquareConstant_lt_exp :
    conreyExplicitMeanSquareConstant < Real.exp (18 / 25 : ℝ) := by
  exact conreyExplicitMeanSquareConstant_lt_rational.trans
    (by
      apply lt_trans (b := (20544332 : ℝ) / 10000000)
      · norm_num
      · exact rational_lt_exp_eighteen_twenty_fifths)

private theorem conreyExplicitMeanSquareConstant_pos :
    0 < conreyExplicitMeanSquareConstant := by
  have h := Real.sum_le_exp_of_nonneg (x := (12 : ℝ) / 5) (by norm_num) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  norm_num [conreyExplicitMeanSquareConstant]
  nlinarith

theorem conreyExplicitProportion_gt_two_fifths :
    (2 : ℝ) / 5 <
      1 - Real.log conreyExplicitMeanSquareConstant / conreyExplicitR := by
  have hlog : Real.log conreyExplicitMeanSquareConstant < (18 : ℝ) / 25 :=
    (Real.log_lt_iff_lt_exp conreyExplicitMeanSquareConstant_pos).2
      conreyExplicitMeanSquareConstant_lt_exp
  norm_num [conreyExplicitR] at *
  linarith

end HardyTheorem
