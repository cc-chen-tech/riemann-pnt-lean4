import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators ArithmeticFunction
open Filter Topology

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

/-- The standard linear logarithmic Selberg weight, repeated here without
importing the much larger Hardy-theorem dependency graph. -/
noncomputable def linearLogSelbergWeight (Y n : ℕ) : ℝ :=
  1 - Real.log n / Real.log Y

/-- The corresponding real linearly tapered Moebius coefficient. -/
noncomputable def linearLogSelbergCoeff (Y n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ) * linearLogSelbergWeight Y n

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

/-- Coefficient-level form of the exact decomposition into two standard
linear Selberg tapers. -/
theorem twoScaleSelbergWeight_eq_linear_combination
    {Y0 Y1 n : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    (hn1 : 1 ≤ n) (hnY1 : n ≤ Y1) :
    twoScaleSelbergWeight Y0 Y1 n =
      Real.log Y1 / Real.log ((Y1 : ℝ) / (Y0 : ℝ)) *
          linearLogSelbergWeight Y1 n -
        (if n ≤ Y0 then
          Real.log Y0 / Real.log ((Y1 : ℝ) / (Y0 : ℝ)) *
            linearLogSelbergWeight Y0 n
        else 0) := by
  have hY0pos : (0 : ℝ) < Y0 := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hY0)
  have hY0one : (1 : ℝ) < Y0 := by exact_mod_cast hY0
  have hY1pos : (0 : ℝ) < Y1 := hY0pos.trans (by exact_mod_cast hY01)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlogY0 : 0 < Real.log (Y0 : ℝ) := Real.log_pos hY0one
  have hlogY1 : 0 < Real.log (Y1 : ℝ) :=
    Real.log_pos (hY0one.trans (by exact_mod_cast hY01))
  have hratio : (1 : ℝ) < (Y1 : ℝ) / (Y0 : ℝ) :=
    (one_lt_div hY0pos).2 (by exact_mod_cast hY01)
  have hlogRatio : 0 < Real.log ((Y1 : ℝ) / (Y0 : ℝ)) :=
    Real.log_pos hratio
  have hlogY10 : Real.log ((Y1 : ℝ) / (Y0 : ℝ)) =
      Real.log (Y1 : ℝ) - Real.log (Y0 : ℝ) := by
    rw [Real.log_div hY1pos.ne' hY0pos.ne']
  have hlogDiffNe :
      Real.log (Y1 : ℝ) - Real.log (Y0 : ℝ) ≠ 0 := by
    rw [← hlogY10]
    exact hlogRatio.ne'
  have hlogY1n : Real.log ((Y1 : ℝ) / (n : ℝ)) =
      Real.log (Y1 : ℝ) - Real.log (n : ℝ) := by
    rw [Real.log_div hY1pos.ne' hnpos.ne']
  by_cases hnY0 : n ≤ Y0
  · simp only [twoScaleSelbergWeight, if_pos hnY0,
      linearLogSelbergWeight]
    rw [hlogY10]
    field_simp [hlogY0.ne', hlogY1.ne', hlogDiffNe]
    ring
  · simp only [twoScaleSelbergWeight, if_neg hnY0, if_pos hnY1,
      linearLogSelbergWeight, sub_zero]
    rw [hlogY1n]
    field_simp [hlogY1.ne', hlogRatio.ne']

/-- The same exact decomposition after multiplication by the Moebius
coefficient. -/
theorem twoScaleSelbergCoeff_eq_linear_combination
    {Y0 Y1 n : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    (hn1 : 1 ≤ n) (hnY1 : n ≤ Y1) :
    twoScaleSelbergCoeff Y0 Y1 n =
      Real.log Y1 / Real.log ((Y1 : ℝ) / (Y0 : ℝ)) *
          linearLogSelbergCoeff Y1 n -
        (if n ≤ Y0 then
          Real.log Y0 / Real.log ((Y1 : ℝ) / (Y0 : ℝ)) *
            linearLogSelbergCoeff Y0 n
        else 0) := by
  rw [twoScaleSelbergCoeff, linearLogSelbergCoeff,
    linearLogSelbergCoeff,
    twoScaleSelbergWeight_eq_linear_combination hY0 hY01 hn1 hnY1]
  split_ifs <;> ring

/-- The finite two-scale mollifier is entire as a function of its complex
argument. -/
theorem analyticAt_twoScaleSelbergMollifier
    (Y0 Y1 : ℕ) (s : ℂ) :
    AnalyticAt ℂ (twoScaleSelbergMollifier Y0 Y1) s := by
  unfold twoScaleSelbergMollifier
  apply Finset.analyticAt_fun_sum
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
  have hpow : AnalyticAt ℂ (fun z : ℂ => (n : ℂ) ^ z) s :=
    (differentiable_id.const_cpow (.inl hn0)).analyticAt s
  exact analyticAt_const.mul
    (analyticAt_const.div hpow
      (Complex.cpow_ne_zero_iff.mpr (.inl hn0)))

/-- Along the positive real axis the normalized two-scale mollifier tends to
its constant coefficient, namely one. -/
theorem tendsto_twoScaleSelbergMollifier_real_atTop
    {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) :
    Tendsto (fun sigma : ℝ =>
      twoScaleSelbergMollifier Y0 Y1 (sigma : ℂ)) atTop (𝓝 1) := by
  have hY1 : 1 ≤ Y1 := hY0.trans hY01.le
  unfold twoScaleSelbergMollifier
  have hterm : ∀ n ∈ Finset.Icc 1 Y1,
      Tendsto (fun sigma : ℝ =>
        (twoScaleSelbergCoeff Y0 Y1 n : ℂ) *
          (1 / (n : ℂ) ^ (sigma : ℂ))) atTop
        (𝓝 (if n = 1 then 1 else 0)) := by
    intro n hn
    by_cases hnOne : n = 1
    · subst n
      simpa [twoScaleSelbergCoeff_one hY0] using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℝ => (1 : ℂ)) atTop (𝓝 1))
    · have hnTwo : 2 ≤ n := by
        have hnLow := (Finset.mem_Icc.mp hn).1
        exact Nat.lt_of_le_of_ne hnLow (Ne.symm hnOne)
      have hnReal : (1 : ℝ) < n := by exact_mod_cast hnTwo
      have hnPos : (0 : ℝ) < n := by
        exact_mod_cast (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1)
      have hInvPos : 0 < ((n : ℝ)⁻¹) := inv_pos.mpr hnPos
      have hInvLt : ((n : ℝ)⁻¹) < 1 :=
        (inv_lt_one₀ hnPos).2 hnReal
      have hreal : Tendsto (fun sigma : ℝ => ((n : ℝ)⁻¹) ^ sigma)
          atTop (𝓝 0) :=
        tendsto_rpow_atTop_of_base_lt_one _
          (neg_one_lt_zero.trans hInvPos) hInvLt
      have hcomplex : Tendsto (fun sigma : ℝ =>
          ((((n : ℝ)⁻¹) ^ sigma : ℝ) : ℂ)) atTop (𝓝 0) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
      have hmul : Tendsto (fun sigma : ℝ =>
          (twoScaleSelbergCoeff Y0 Y1 n : ℂ) *
            ((((n : ℝ)⁻¹) ^ sigma : ℝ) : ℂ)) atTop (𝓝 0) := by
        simpa only [mul_zero] using
          hcomplex.const_mul (twoScaleSelbergCoeff Y0 Y1 n : ℂ)
      rw [if_neg hnOne]
      convert hmul using 1
      funext sigma
      rw [one_div]
      have hcpow : (n : ℂ) ^ (sigma : ℂ) =
          (((n : ℝ) ^ sigma : ℝ) : ℂ) := by
        simpa only [Complex.ofReal_natCast] using
          (Complex.ofReal_cpow (Nat.cast_nonneg n) sigma).symm
      rw [hcpow, ← Complex.ofReal_inv,
        ← Real.inv_rpow (Nat.cast_nonneg n) sigma]
  have hsum := tendsto_finsetSum (Finset.Icc 1 Y1) hterm
  convert hsum using 1
  simp [hY1]

/-- The two-scale mollifier is not identically zero. -/
theorem exists_twoScaleSelbergMollifier_ne_zero
    {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) :
    ∃ s : ℂ, twoScaleSelbergMollifier Y0 Y1 s ≠ 0 := by
  have heventually :=
    (tendsto_twoScaleSelbergMollifier_real_atTop hY0 hY01).eventually_ne
      one_ne_zero
  obtain ⟨x, hx⟩ := heventually.exists
  exact ⟨(x : ℂ), hx⟩

/-- Consequently its analytic order is finite at every point. -/
theorem analyticOrderAt_twoScaleSelbergMollifier_ne_top
    {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) (s : ℂ) :
    analyticOrderAt (twoScaleSelbergMollifier Y0 Y1) s ≠ ⊤ := by
  obtain ⟨z, hz⟩ :=
    exists_twoScaleSelbergMollifier_ne_zero hY0 hY01
  have hanalytic : AnalyticOnNhd ℂ
      (twoScaleSelbergMollifier Y0 Y1) Set.univ :=
    fun u _hu => analyticAt_twoScaleSelbergMollifier Y0 Y1 u
  have hzorder : analyticOrderAt
      (twoScaleSelbergMollifier Y0 Y1) z ≠ ⊤ := by
    rw [(hanalytic z (by simp)).analyticOrderAt_eq_zero.mpr hz]
    exact ENat.natCast_ne_top 0
  exact hanalytic.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (by simp) (by simp) hzorder

end HardyTheorem
