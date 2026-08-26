import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# A two-scale Selberg mollifier with an exact Moebius plateau

The inner cutoff `Y0` carries the untapered Moebius coefficient.  Between
`Y0` and `Y1` the coefficient decreases linearly in the logarithmic
variable.  The exact inner plateau is the arithmetic feature needed to make
the coefficients of `zeta * M - 1` vanish below `Y0`.
-/

/-- The plateau--taper weight used by the two-scale Carlson mollifier. -/
noncomputable def twoScaleSelbergWeight (Y0 Y1 n : ℕ) : ℝ :=
  if n ≤ Y0 then 1
  else if n ≤ Y1 then
    Real.log ((Y1 : ℝ) / (n : ℝ)) /
      Real.log ((Y1 : ℝ) / (Y0 : ℝ))
  else 0

/-- The real Moebius coefficient carrying the two-scale weight. -/
noncomputable def twoScaleSelbergCoeff (Y0 Y1 n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ) *
    twoScaleSelbergWeight Y0 Y1 n

/-- The finite two-scale Selberg mollifier. -/
noncomputable def twoScaleSelbergMollifier
    (Y0 Y1 : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 Y1,
    (twoScaleSelbergCoeff Y0 Y1 n : ℂ) *
      (1 / (n : ℂ) ^ s)

/-- The collected coefficient of `zeta * M` at an integer index. -/
noncomputable def twoScaleMollifiedZetaCoeff
    (Y0 Y1 k : ℕ) : ℝ :=
  ∑ d ∈ k.divisors, twoScaleSelbergCoeff Y0 Y1 d

/-- Every index in the inner range sees weight exactly one. -/
@[simp] theorem twoScaleSelbergWeight_eq_one
    {Y0 Y1 n : ℕ} (hn : n ≤ Y0) :
    twoScaleSelbergWeight Y0 Y1 n = 1 := by
  simp [twoScaleSelbergWeight, hn]

/-- Hence the inner coefficients are the genuine Moebius coefficients. -/
@[simp] theorem twoScaleSelbergCoeff_eq_moebius
    {Y0 Y1 n : ℕ} (hn : n ≤ Y0) :
    twoScaleSelbergCoeff Y0 Y1 n =
      (ArithmeticFunction.moebius n : ℝ) := by
  simp [twoScaleSelbergCoeff, hn]

/-- Below the plateau cutoff, Moebius inversion makes every nonconstant
coefficient of `zeta * M` vanish exactly. -/
theorem twoScaleMollifiedZetaCoeff_eq_zero
    {Y0 Y1 k : ℕ} (hk : 1 < k) (hkY0 : k ≤ Y0) :
    twoScaleMollifiedZetaCoeff Y0 Y1 k = 0 := by
  classical
  rw [twoScaleMollifiedZetaCoeff]
  calc
    (∑ d ∈ k.divisors, twoScaleSelbergCoeff Y0 Y1 d) =
        ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply twoScaleSelbergCoeff_eq_moebius
      have hdk : d ≤ k :=
        Nat.le_of_dvd (Nat.zero_lt_of_lt hk) (Nat.dvd_of_mem_divisors hd)
      exact hdk.trans hkY0
    _ = 0 := by
      have hconv := congrArg (fun f : ArithmeticFunction ℝ => f k)
        (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
      change (((ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
        ArithmeticFunction.zeta) k) =
          (1 : ArithmeticFunction ℝ) k at hconv
      rw [ArithmeticFunction.coe_mul_zeta_apply] at hconv
      simpa [hk.ne'] using hconv

/-- On its full support the plateau--taper weight lies in `[0,1]`. -/
theorem twoScaleSelbergWeight_mem_Icc
    {Y0 Y1 n : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hn1 : 1 ≤ n) (hnY1 : n ≤ Y1) :
    twoScaleSelbergWeight Y0 Y1 n ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hnY0 : n ≤ Y0
  · simp [twoScaleSelbergWeight, hnY0]
  · have hY0n : Y0 < n := Nat.lt_of_not_ge hnY0
    have hY0pos : (0 : ℝ) < Y0 := by
      exact_mod_cast (Nat.zero_lt_one.trans_le hY0)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hY1pos : (0 : ℝ) < Y1 := hY0pos.trans (by exact_mod_cast hY01)
    have hdenRatio : (1 : ℝ) < (Y1 : ℝ) / (Y0 : ℝ) :=
      (one_lt_div hY0pos).2 (by exact_mod_cast hY01)
    have hdenLog : 0 < Real.log ((Y1 : ℝ) / (Y0 : ℝ)) :=
      Real.log_pos hdenRatio
    have hnumRatio : (1 : ℝ) ≤ (Y1 : ℝ) / (n : ℝ) :=
      (le_div_iff₀ hnpos).2 (by simpa using (show (n : ℝ) ≤ Y1 by exact_mod_cast hnY1))
    have hnumLog : 0 ≤ Real.log ((Y1 : ℝ) / (n : ℝ)) :=
      Real.log_nonneg hnumRatio
    have hratioLe : (Y1 : ℝ) / (n : ℝ) ≤
        (Y1 : ℝ) / (Y0 : ℝ) := by
      apply (div_le_div_iff₀ hnpos hY0pos).2
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hY0n.le) hY1pos.le
    have hlogLe : Real.log ((Y1 : ℝ) / (n : ℝ)) ≤
        Real.log ((Y1 : ℝ) / (Y0 : ℝ)) :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one hnumRatio) hratioLe
    simp only [twoScaleSelbergWeight, if_neg hnY0, if_pos hnY1]
    exact ⟨div_nonneg hnumLog hdenLog.le, (div_le_one hdenLog).2 hlogLe⟩

/-- The two-scale Moebius coefficients have modulus at most one. -/
theorem abs_twoScaleSelbergCoeff_le_one
    {Y0 Y1 n : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hn1 : 1 ≤ n) (hnY1 : n ≤ Y1) :
    |twoScaleSelbergCoeff Y0 Y1 n| ≤ 1 := by
  have hw := twoScaleSelbergWeight_mem_Icc hY0 hY01 hn1 hnY1
  have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  rw [twoScaleSelbergCoeff, abs_mul, abs_of_nonneg hw.1]
  calc
    |(ArithmeticFunction.moebius n : ℝ)| *
          twoScaleSelbergWeight Y0 Y1 n ≤
        1 * twoScaleSelbergWeight Y0 Y1 n :=
      mul_le_mul_of_nonneg_right hmu hw.1
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hw.2 zero_le_one
    _ = 1 := one_mul 1

/-- The constant Dirichlet coefficient is exactly one. -/
@[simp] theorem twoScaleSelbergCoeff_one
    {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) :
    twoScaleSelbergCoeff Y0 Y1 1 = 1 := by
  simp [twoScaleSelbergCoeff, hY0]

end HardyTheorem
