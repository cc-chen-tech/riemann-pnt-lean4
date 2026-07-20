/-
# ξ 增长阶 ≤ 1：Gamma 因子的初等上界（Hadamard 切片六 a）

本文件给出 ξ 增长阶论证的 **Gamma 因子界**，全程初等（不用 Stirling）：

1. `pow_ceil_le_exp_mul_log`：`⌈y⌉^⌈y⌉ ≤ exp((y+1)·log(y+1))`（`1 ≤ y`）。
2. `real_Gamma_le_ceil_pow_ceil`：`2 ≤ x` 时 `Γ(x) ≤ ⌈x⌉^⌈x⌉`
   （Γ 在 `[2, ∞)` 严格增 + `Γ(n) = (n−1)! ≤ (n−1)^(n−1)`）。
3. `real_Gamma_le_exp`：统一指数形式
   `Γ(x) ≤ exp(log(16/5) + (x+3)·log(x+3))`（`1/4 ≤ x`）。
   小区间 `x ∈ [1/4, 2]` 用函数方程 `Γ(x) = Γ(x+2)/(x(x+1))` 放大到大区间。
4. `Complex.norm_Gamma_le_real_Gamma`：Euler 积分表示给出
   `‖Γ(z)‖ ≤ Γ(re z)`（`0 < re z`）——被积函数的模恰为实 Gamma 核。
5. `Complex.norm_Gamma_le_exp`：复 Γ 的阶 1 增长界。

## 证明纪律

无 `sorry`/`admit`/新公理；公理审计见 `Test/XiFunctionAxiomAudit.lean`。
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Data.Nat.Factorial.BigOperators

namespace RiemannExplorer

/-- 幂的指数上界：`1 ≤ y` 时 `⌈y⌉₊^⌈y⌉₊ ≤ exp((y+1)·log(y+1))`。 -/
theorem pow_ceil_le_exp_mul_log {y : ℝ} (hy : 1 ≤ y) :
    (⌈y⌉₊ : ℝ) ^ ⌈y⌉₊ ≤ Real.exp ((y + 1) * Real.log (y + 1)) := by
  have hceil : (⌈y⌉₊ : ℝ) ≤ y + 1 :=
    (Nat.ceil_lt_add_one (le_trans zero_le_one hy)).le
  have hlog : 0 ≤ Real.log (y + 1) := Real.log_nonneg (by linarith)
  have hn0 : (0:ℝ) ≤ (⌈y⌉₊ : ℝ) := by positivity
  calc (⌈y⌉₊ : ℝ) ^ ⌈y⌉₊ ≤ (y + 1) ^ ⌈y⌉₊ := pow_le_pow_left₀ hn0 hceil _
    _ = (y + 1) ^ (⌈y⌉₊ : ℝ) := (Real.rpow_natCast (y + 1) ⌈y⌉₊).symm
    _ = Real.exp (Real.log (y + 1) * (⌈y⌉₊ : ℝ)) := Real.rpow_def_of_pos (by linarith) _
    _ = Real.exp ((⌈y⌉₊ : ℝ) * Real.log (y + 1)) := by rw [mul_comm]
    _ ≤ Real.exp ((y + 1) * Real.log (y + 1)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hceil hlog)

/-- 实 Γ 的初等上界（大变量）：`2 ≤ x` 时 `Γ(x) ≤ ⌈x⌉₊^⌈x⌉₊`。 -/
theorem real_Gamma_le_ceil_pow_ceil {x : ℝ} (hx : 2 ≤ x) :
    Real.Gamma x ≤ (⌈x⌉₊ : ℝ) ^ ⌈x⌉₊ := by
  have hn2 : 2 ≤ ⌈x⌉₊ := by
    calc 2 = ⌈(2 : ℝ)⌉₊ := (Nat.ceil_natCast 2).symm
      _ ≤ ⌈x⌉₊ := Nat.ceil_mono hx
  have hmon : Real.Gamma x ≤ Real.Gamma (⌈x⌉₊ : ℝ) :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn hx
      (le_trans hx (Nat.le_ceil x)) (Nat.le_ceil x)
  have hΓn : Real.Gamma (⌈x⌉₊ : ℝ) = (Nat.factorial (⌈x⌉₊ - 1) : ℝ) := by
    have hcast : (⌈x⌉₊ : ℝ) = ((⌈x⌉₊ - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ ⌈x⌉₊), Nat.cast_one]
      ring
    rw [hcast, Real.Gamma_nat_eq_factorial]
  have hfact : Nat.factorial (⌈x⌉₊ - 1) ≤ (⌈x⌉₊ - 1) ^ (⌈x⌉₊ - 1) := by
    rw [Nat.factorial_eq_prod_range_add_one]
    calc ∏ i ∈ Finset.range (⌈x⌉₊ - 1), (i + 1)
        ≤ ∏ _i ∈ Finset.range (⌈x⌉₊ - 1), (⌈x⌉₊ - 1) :=
          Finset.prod_le_prod (fun i _ => Nat.zero_le _)
            (fun i hi => by
              simp only [Finset.mem_range] at hi
              omega)
      _ = (⌈x⌉₊ - 1) ^ (⌈x⌉₊ - 1) := by
          rw [Finset.prod_const, Finset.card_range]
  calc Real.Gamma x ≤ Real.Gamma (⌈x⌉₊ : ℝ) := hmon
    _ = (Nat.factorial (⌈x⌉₊ - 1) : ℝ) := hΓn
    _ ≤ (((⌈x⌉₊ - 1) ^ (⌈x⌉₊ - 1) : ℕ) : ℝ) := by exact_mod_cast hfact
    _ ≤ (⌈x⌉₊ : ℝ) ^ ⌈x⌉₊ := by
        have hbase : (((⌈x⌉₊ - 1) ^ (⌈x⌉₊ - 1) : ℕ) : ℝ) ≤
            (⌈x⌉₊ : ℝ) ^ (⌈x⌉₊ - 1) := by
          rw [Nat.cast_pow]
          exact_mod_cast Nat.pow_le_pow_left (Nat.sub_le _ _) (⌈x⌉₊ - 1)
        exact hbase.trans (pow_le_pow_right₀
          (by exact_mod_cast (by omega : 1 ≤ ⌈x⌉₊) : (1:ℝ) ≤ ⌈x⌉₊)
          (Nat.sub_le ⌈x⌉₊ 1))

/-- 实 Γ 的统一指数上界：`1/4 ≤ x` 时
`Γ(x) ≤ exp(log(16/5) + (x+3)·log(x+3))`。 -/
theorem real_Gamma_le_exp {x : ℝ} (hx : 1 / 4 ≤ x) :
    Real.Gamma x ≤ Real.exp (Real.log (16 / 5) + (x + 3) * Real.log (x + 3)) := by
  have hx0 : 0 < x := by linarith
  by_cases h2 : 2 ≤ x
  · calc Real.Gamma x ≤ (⌈x⌉₊ : ℝ) ^ ⌈x⌉₊ := real_Gamma_le_ceil_pow_ceil h2
      _ ≤ Real.exp ((x + 1) * Real.log (x + 1)) := pow_ceil_le_exp_mul_log (by linarith)
      _ ≤ Real.exp (Real.log (16 / 5) + (x + 3) * Real.log (x + 3)) := by
          apply Real.exp_le_exp.mpr
          have hlog1 : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
          have h1 : (x + 1) * Real.log (x + 1) ≤ (x + 3) * Real.log (x + 1) :=
            mul_le_mul_of_nonneg_right (by linarith) hlog1
          have h2' : (x + 3) * Real.log (x + 1) ≤ (x + 3) * Real.log (x + 3) :=
            mul_le_mul_of_nonneg_left
              (Real.log_le_log (by linarith) (by linarith)) (by linarith)
          have h3 : 0 ≤ Real.log (16 / 5 : ℝ) := Real.log_nonneg (by norm_num)
          linarith [h1.trans h2']
  · have hx2 : x < 2 := lt_of_not_ge h2
    have hG1 : Real.Gamma (x + 1) = x * Real.Gamma x :=
      Real.Gamma_add_one (ne_of_gt hx0)
    have hG2 : Real.Gamma (x + 2) = x * (x + 1) * Real.Gamma x := by
      rw [show x + 2 = (x + 1) + 1 from by ring,
        Real.Gamma_add_one (ne_of_gt (by linarith : (0:ℝ) < x + 1)), hG1]
      ring
    have hxx1 : (5 / 16 : ℝ) ≤ x * (x + 1) := by nlinarith [hx]
    have hbound : Real.Gamma x ≤ (16 / 5) * Real.Gamma (x + 2) := by
      have hpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx0
      have hge : (1:ℝ) ≤ (16 / 5) * (x * (x + 1)) := by nlinarith [hxx1]
      calc Real.Gamma x = 1 * Real.Gamma x := (one_mul _).symm
        _ ≤ ((16 / 5) * (x * (x + 1))) * Real.Gamma x :=
            mul_le_mul_of_nonneg_right hge hpos.le
        _ = (16 / 5) * Real.Gamma (x + 2) := by rw [hG2]; ring
    calc Real.Gamma x ≤ (16 / 5) * Real.Gamma (x + 2) := hbound
      _ ≤ (16 / 5) * Real.exp ((x + 3) * Real.log (x + 3)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 16 / 5)
          have hpow : (⌈x + 2⌉₊ : ℝ) ^ ⌈x + 2⌉₊ ≤
              Real.exp ((x + 3) * Real.log (x + 3)) := by
            have h := pow_ceil_le_exp_mul_log (by linarith : (1:ℝ) ≤ x + 2)
            have heq : x + 2 + 1 = x + 3 := by ring
            rwa [heq] at h
          exact (real_Gamma_le_ceil_pow_ceil (by linarith : (2:ℝ) ≤ x + 2)).trans hpow
      _ = Real.exp (Real.log (16 / 5) + (x + 3) * Real.log (x + 3)) := by
          rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 16 / 5)]

/-- Euler 积分表示给出复 Γ 的模长界：`0 < re z` 时 `‖Γ(z)‖ ≤ Γ(re z)`。 -/
theorem Complex.norm_Gamma_le_real_Gamma {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz]
  unfold Complex.GammaIntegral
  calc ‖∫ x in Set.Ioi (0 : ℝ), (↑(-x).exp : ℂ) * (x : ℂ) ^ (z - 1)‖
      ≤ ∫ x in Set.Ioi (0 : ℝ), ‖(↑(-x).exp : ℂ) * (x : ℂ) ^ (z - 1)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ (z.re - 1) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
          Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]
    _ = Real.Gamma z.re := (Real.Gamma_eq_integral hz).symm

/-- 复 Γ 的阶 1 增长界：`1/4 ≤ re z` 时
`‖Γ(z)‖ ≤ exp(log(16/5) + (re z + 3)·log(re z + 3))`。 -/
theorem Complex.norm_Gamma_le_exp {z : ℂ} (hz : 1 / 4 ≤ z.re) :
    ‖Complex.Gamma z‖ ≤
      Real.exp (Real.log (16 / 5) + (z.re + 3) * Real.log (z.re + 3)) :=
  (Complex.norm_Gamma_le_real_Gamma (by linarith)).trans (real_Gamma_le_exp hz)

end RiemannExplorer
