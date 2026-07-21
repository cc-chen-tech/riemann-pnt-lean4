/-
# ζ 在实轴区间 (0,1) 上无零点（无条件，Dirichlet η 配对级数路线）

本文件证明 `riemannZeta (↑x) ≠ 0`（`0 < x < 1`）。这是 ξ 零点分类
（`xiFunction_zero_imp_isNontrivialZero`）与重数加权部分分式修正的
无条件整性（`differentiable_xiWeightedEntireCorrection`）所需的关键输入：
ξ 的零点若虚部为零，则落在实轴上，而实轴段 (0,1) 上 ζ 无零点
（ξ 的零点同时在 0、1 处由 ξ(0) = ξ(1) = 1/2 ≠ 0 排除）。

## 数学路线（经典）

定义配对 Dirichlet η 级数

```text
η̃(s) = Σ_k [(2k+1)^{-s} − (2k+2)^{-s}]
```

1. **半平面解析**：对复 s 无交错性可用，改用配对绝对收敛：
   在球 `ball s₀ (s₀.re/2)` 上，`(2k+1) ≥ ‖s₀‖ + s₀.re/2` 时
   `(2k+2)^{-s} = (2k+1)^{-s}·(1 + (2k+1)^{-1})^{-s}`，而
   `‖1 − (1+a^{-1})^{-s}‖ = ‖1 − exp(log(1+a^{-1})·(−s))‖ ≤ 2a^{-1}M`
   （`norm_exp_sub_one_le`），Weierstrass M 判别给出 `η̃` 在 `{0 < re}` 解析。
2. **可去奇点修正**：`fac(s) = 1 − 2·2^{-s}` 在 `s = 1` 有一阶零点
   （导数 `log 2 ≠ 0`），`ζ` 在 `s = 1` 留数为 1，故
   `fac·ζ` 在 `s = 1` 可去，修正值 `log 2`
   （`differentiableOn_update_limUnder_of_isLittleO` 粘合）。
3. **恒等式**：`re s > 1` 时 `η̃(s) = (1 − 2^{1−s})·ζ(s)`
   （奇偶 tsum 拆分：偶数项和 `= 2^{-s}·ζ(s)`）；
   恒等定理（聚点 2）延拓到整个 `{0 < re}`。
4. **正性**：实轴 `x ∈ (0,1)` 上逐项 `(2k+1)^{-x} − (2k+2)^{-x} > 0`，
   首项 `1 − 2^{-x} > 0`，故 `η̃(↑x).re ≥ 1 − 2^{-x} > 0`，
   从而 `fac(↑x)·ζ(↑x) ≠ 0`，于是 `ζ(↑x) ≠ 0`。
   （注意：不需要因子 `1 − 2^{1−x}` 非零——若 ζ 为零则乘积为零即矛盾。）
-/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Classical Complex ComplexConjugate
open scoped Topology

/-!
## 配对 η 级数：定义与逐项可微性
-/

/-- 配对 η 级数的第 `k` 项：`(2k+1)^{-s} − (2k+2)^{-s}`。 -/
noncomputable def etaPairTerm (s : ℂ) (k : ℕ) : ℂ :=
  ((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s)

/-- 配对 Dirichlet η 级数：`η̃(s) = Σ_k [(2k+1)^{-s} − (2k+2)^{-s}]`。 -/
noncomputable def dirichletEtaPair (s : ℂ) : ℂ := ∑' k : ℕ, etaPairTerm s k

theorem differentiableAt_etaPairTerm (k : ℕ) (s : ℂ) :
    DifferentiableAt ℂ (fun w => etaPairTerm w k) s := by
  have h1 : DifferentiableAt ℂ (fun w : ℂ => ((2 * k + 1 : ℕ) : ℂ) ^ (-w)) s :=
    DifferentiableAt.const_cpow differentiableAt_id.neg
      (Or.inl (Nat.cast_ne_zero.mpr (by omega : 2 * k + 1 ≠ 0)))
  have h2 : DifferentiableAt ℂ (fun w : ℂ => ((2 * k + 2 : ℕ) : ℂ) ^ (-w)) s :=
    DifferentiableAt.const_cpow differentiableAt_id.neg
      (Or.inl (Nat.cast_ne_zero.mpr (by omega : 2 * k + 2 ≠ 0)))
  exact h1.sub h2

theorem differentiable_etaPairTerm (k : ℕ) :
    Differentiable ℂ (fun w => etaPairTerm w k) :=
  fun s => differentiableAt_etaPairTerm k s

/-!
## 球内一致界（Weierstrass M 判别）
-/

/-- 粗界：球 `ball s₀ (s₀.re/2)` 内每项范数 ≤ 2（底 ≥ 1、指数实部为负）。 -/
theorem etaPairTerm_norm_le_two {s₀ : ℂ} (hs₀ : 0 < s₀.re) {s : ℂ}
    (hs : s ∈ Metric.ball s₀ (s₀.re / 2)) (k : ℕ) :
    ‖etaPairTerm s k‖ ≤ 2 := by
  have h1 : ‖s - s₀‖ < s₀.re / 2 := by
    have h := Metric.mem_ball.mp hs
    rwa [dist_eq_norm] at h
  have h2 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
    have h := abs_re_le_norm (s - s₀)
    rwa [Complex.sub_re] at h
  have hsre : s₀.re / 2 < s.re := by
    have h3 := abs_le.mp h2
    linarith [h3.1]
  have hb1 : ‖((2 * k + 1 : ℕ) : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [← Complex.ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (by omega : 0 < 2 * k + 1)),
      Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (by omega : 1 ≤ 2 * k + 1)) (by linarith)
  have hb2 : ‖((2 * k + 2 : ℕ) : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [← Complex.ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (by omega : 0 < 2 * k + 2)),
      Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (by omega : 1 ≤ 2 * k + 2)) (by linarith)
  calc ‖etaPairTerm s k‖
      = ‖((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s)‖ := rfl
    _ ≤ ‖((2 * k + 1 : ℕ) : ℂ) ^ (-s)‖ + ‖((2 * k + 2 : ℕ) : ℂ) ^ (-s)‖ :=
        norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add hb1 hb2
    _ = 2 := by norm_num

/-- 细界：`(2k+1) ≥ ‖s₀‖ + s₀.re/2` 时，用 `(2k+2)^{-s} = (2k+1)^{-s}·(1+(2k+1)^{-1})^{-s}`
与 `‖1 − e^w‖ ≤ 2‖w‖` 得到按 `a^{-(s₀.re/2+1)}` 衰减的界。 -/
theorem etaPairTerm_norm_le_exp {s₀ : ℂ} (hs₀ : 0 < s₀.re) {s : ℂ}
    (hs : s ∈ Metric.ball s₀ (s₀.re / 2)) {k : ℕ}
    (hk : ¬ ((2 * k + 1 : ℕ) : ℝ) < ‖s₀‖ + s₀.re / 2) :
    ‖etaPairTerm s k‖ ≤
      2 * (‖s₀‖ + s₀.re / 2) * ((k + 1 : ℕ) : ℝ) ^ (-(s₀.re / 2 + 1)) := by
  set M := ‖s₀‖ + s₀.re / 2 with hMdef
  set a : ℝ := ((2 * k + 1 : ℕ) : ℝ) with ha_def
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have ha : 0 < a := by
    rw [ha_def]
    exact Nat.cast_pos.mpr (by omega)
  have ha1 : 1 ≤ a := by
    rw [ha_def]
    exact_mod_cast (by omega : 1 ≤ 2 * k + 1)
  have haM : M ≤ a := not_lt.mp hk
  have hai0 : (0 : ℝ) ≤ a⁻¹ := inv_nonneg.mpr (le_of_lt ha)
  have hb0 : (0 : ℝ) < 1 + a⁻¹ :=
    lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right hai0)
  -- s 的实部与范数估计
  have h1 : ‖s - s₀‖ < s₀.re / 2 := by
    have h := Metric.mem_ball.mp hs
    rwa [dist_eq_norm] at h
  have h2 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
    have h := abs_re_le_norm (s - s₀)
    rwa [Complex.sub_re] at h
  have hsre : s₀.re / 2 < s.re := by
    have h3 := abs_le.mp h2
    linarith [h3.1]
  have hsnorm : ‖s‖ < M := by
    calc ‖s‖ = ‖s₀ + (s - s₀)‖ := by rw [add_sub_cancel]
      _ ≤ ‖s₀‖ + ‖s - s₀‖ := norm_add_le _ _
      _ < ‖s₀‖ + s₀.re / 2 := by linarith [h1]
      _ = M := hMdef.symm
  -- 底数拆分 (2k+2) = (2k+1)·(1 + (2k+1)⁻¹)
  have hcast2 : ((2 * k + 2 : ℕ) : ℂ) = ((a * (1 + a⁻¹)) : ℝ) := by
    have hR : ((2 * k + 2 : ℕ) : ℝ) = a * (1 + a⁻¹) := by
      rw [ha_def, mul_add, mul_inv_cancel₀ (by positivity : ((2 * k + 1 : ℕ) : ℝ) ≠ 0),
        mul_one]
      push_cast
      ring
    rw [← hR]
    exact (Complex.ofReal_natCast _).symm
  -- 项的因式分解
  have haC : ((a : ℝ) : ℂ) = ((2 * k + 1 : ℕ) : ℂ) := by
    rw [ha_def]
    exact (Complex.ofReal_natCast _).symm
  have hterm : etaPairTerm s k =
      ((2 * k + 1 : ℕ) : ℂ) ^ (-s) * (1 - ((1 + a⁻¹ : ℝ) : ℂ) ^ (-s)) := by
    show ((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s) = _
    rw [hcast2, ofReal_mul,
      mul_cpow_ofReal_nonneg (le_of_lt ha) (le_of_lt hb0), haC]
    ring_nf
  -- 指数形式的衰减
  have hw_eq : ((1 + a⁻¹ : ℝ) : ℂ) ^ (-s) =
      Complex.exp (↑(Real.log (1 + a⁻¹)) * (-s)) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hb0))]
    congr 1
    rw [← ofReal_log (le_of_lt hb0)]
  have hw_norm : ‖(↑(Real.log (1 + a⁻¹)) : ℂ) * (-s)‖ ≤ a⁻¹ * M := by
    have hlog0 : 0 ≤ Real.log (1 + a⁻¹) :=
      Real.log_nonneg (le_add_of_nonneg_right hai0)
    have hlogle : Real.log (1 + a⁻¹) ≤ a⁻¹ := by
      have h := Real.log_le_sub_one_of_pos hb0
      rwa [add_sub_cancel_left] at h
    have hnrm : ‖(↑(Real.log (1 + a⁻¹)) : ℂ)‖ = |Real.log (1 + a⁻¹)| := by simp
    rw [norm_mul, norm_neg, hnrm, abs_of_nonneg hlog0]
    exact mul_le_mul hlogle (le_of_lt hsnorm) (norm_nonneg _) hai0
  have hw1 : ‖(↑(Real.log (1 + a⁻¹)) : ℂ) * (-s)‖ ≤ 1 := by
    refine le_trans hw_norm ?_
    have h3 : a⁻¹ * M ≤ a⁻¹ * a := mul_le_mul_of_nonneg_left haM hai0
    rw [inv_mul_cancel₀ (ne_of_gt ha)] at h3
    linarith [h3]
  have hdecay : ‖1 - ((1 + a⁻¹ : ℝ) : ℂ) ^ (-s)‖ ≤ 2 * a⁻¹ * M := by
    rw [hw_eq]
    have h3 : ‖Complex.exp (↑(Real.log (1 + a⁻¹)) * (-s)) - 1‖ ≤
        2 * ‖(↑(Real.log (1 + a⁻¹)) : ℂ) * (-s)‖ :=
      norm_exp_sub_one_le hw1
    have hflip : ‖1 - Complex.exp (↑(Real.log (1 + a⁻¹)) * (-s))‖ =
        ‖Complex.exp (↑(Real.log (1 + a⁻¹)) * (-s)) - 1‖ := by
      rw [← norm_neg]
      congr 1
      ring
    rw [hflip]
    calc ‖Complex.exp (↑(Real.log (1 + a⁻¹)) * (-s)) - 1‖
        ≤ 2 * ‖(↑(Real.log (1 + a⁻¹)) : ℂ) * (-s)‖ := h3
      _ ≤ 2 * (a⁻¹ * M) := mul_le_mul_of_nonneg_left hw_norm (by norm_num)
      _ = 2 * a⁻¹ * M := by ring
  -- 第一个因子的界
  have hnA : ‖((2 * k + 1 : ℕ) : ℂ) ^ (-s)‖ ≤ a ^ (-(s₀.re / 2)) := by
    rw [← Complex.ofReal_natCast, norm_cpow_eq_rpow_re_of_pos ha, Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le ha1 (by linarith : -s.re ≤ -(s₀.re / 2))
  calc ‖etaPairTerm s k‖
      = ‖((2 * k + 1 : ℕ) : ℂ) ^ (-s) * (1 - ((1 + a⁻¹ : ℝ) : ℂ) ^ (-s))‖ := by
        rw [hterm]
    _ ≤ ‖((2 * k + 1 : ℕ) : ℂ) ^ (-s)‖ * ‖1 - ((1 + a⁻¹ : ℝ) : ℂ) ^ (-s)‖ :=
        norm_mul_le _ _
    _ ≤ a ^ (-(s₀.re / 2)) * (2 * a⁻¹ * M) :=
        mul_le_mul hnA hdecay (norm_nonneg _) (Real.rpow_nonneg (le_of_lt ha) _)
    _ = 2 * M * (a ^ (-(s₀.re / 2)) * a ^ (-1 : ℝ)) := by
        rw [← Real.rpow_neg_one a]
        ring
    _ = 2 * M * a ^ (-(s₀.re / 2) + -1) := by rw [← Real.rpow_add ha]
    _ = 2 * M * a ^ (-(s₀.re / 2 + 1)) := by
        rw [show (-(s₀.re / 2) + -1 : ℝ) = -(s₀.re / 2 + 1) by ring]
    _ = 2 * M * ((2 * k + 1 : ℕ) : ℝ) ^ (-(s₀.re / 2 + 1)) := by rw [ha_def]
    _ ≤ 2 * M * ((k + 1 : ℕ) : ℝ) ^ (-(s₀.re / 2 + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hM0)
        exact Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))
          (by exact_mod_cast (by omega : k + 1 ≤ 2 * k + 1))
          (by linarith : -(s₀.re / 2 + 1) ≤ 0)

/-- M 判别所用的可和界函数：前有限项取 2，其后取 `2M(k+1)^{-(s₀.re/2+1)}`。 -/
theorem summable_etaPairTerm_bound {s₀ : ℂ} (hs₀ : 0 < s₀.re) :
    Summable (fun k : ℕ => if ((2 * k + 1 : ℕ) : ℝ) < ‖s₀‖ + s₀.re / 2 then (2 : ℝ)
      else 2 * (‖s₀‖ + s₀.re / 2) * ((k + 1 : ℕ) : ℝ) ^ (-(s₀.re / 2 + 1))) := by
  set M := ‖s₀‖ + s₀.re / 2 with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hp1 : 1 < s₀.re / 2 + 1 := by linarith
  have htail : Summable (fun k : ℕ =>
      (2 : ℝ) * M * ((k + 1 : ℕ) : ℝ) ^ (-(s₀.re / 2 + 1))) := by
    have hbase := Real.summable_one_div_nat_rpow.mpr hp1
    have hconv : (fun n : ℕ => 1 / (n : ℝ) ^ (s₀.re / 2 + 1)) =
        fun n : ℕ => (n : ℝ) ^ (-(s₀.re / 2 + 1)) := by
      funext n
      rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]
    rw [hconv] at hbase
    exact ((summable_nat_add_iff 1).mpr hbase).mul_left _
  have hzero : ∀ k ∉ Finset.range (2 * ⌈M⌉₊),
      (if ((2 * k + 1 : ℕ) : ℝ) < M then (2 : ℝ) else 0) = 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hnot : ¬ ((2 * k + 1 : ℕ) : ℝ) < M := by
      intro hlt
      have hlt1 : ((2 * k + 1 : ℕ) : ℝ) < (⌈M⌉₊ : ℝ) :=
        lt_of_lt_of_le hlt (Nat.le_ceil M)
      have hlt2 : 2 * k + 1 < ⌈M⌉₊ := by exact_mod_cast hlt1
      omega
    rw [if_neg hnot]
  have hfin : Summable (fun k : ℕ => if ((2 * k + 1 : ℕ) : ℝ) < M then (2 : ℝ) else 0) :=
    summable_of_ne_finset_zero hzero
  have htl : Summable (fun k : ℕ => if ((2 * k + 1 : ℕ) : ℝ) < M then (0 : ℝ)
      else 2 * M * ((k + 1 : ℕ) : ℝ) ^ (-(s₀.re / 2 + 1))) := by
    refine Summable.of_norm_bounded htail fun k => ?_
    by_cases hk : ((2 * k + 1 : ℕ) : ℝ) < M
    · rw [if_pos hk, norm_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hM0)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · rw [if_neg hk]
      exact (Real.norm_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))).le
  refine (hfin.add htl).congr fun k => ?_
  by_cases hk : ((2 * k + 1 : ℕ) : ℝ) < M
  · simp only [if_pos hk, add_zero]
  · simp only [if_neg hk, zero_add]

/-- 配对 η 级数在 `{0 < re}` 上（绝对）可和。 -/
theorem summable_etaPairTerm {s : ℂ} (hs : 0 < s.re) :
    Summable (fun k : ℕ => etaPairTerm s k) := by
  refine Summable.of_norm_bounded (summable_etaPairTerm_bound hs) fun k => ?_
  by_cases hk : ((2 * k + 1 : ℕ) : ℝ) < ‖s‖ + s.re / 2
  · rw [if_pos hk]
    exact etaPairTerm_norm_le_two hs
      (Metric.mem_ball_self (by linarith : (0 : ℝ) < s.re / 2)) k
  · rw [if_neg hk]
    exact etaPairTerm_norm_le_exp hs
      (Metric.mem_ball_self (by linarith : (0 : ℝ) < s.re / 2)) hk

/-- 配对 η 级数在球 `ball s₀ (s₀.re/2)` 上可微（M 判别 + 逐项可微）。 -/
theorem differentiableOn_dirichletEtaPair_ball {s₀ : ℂ} (hs₀ : 0 < s₀.re) :
    DifferentiableOn ℂ (fun w => ∑' k : ℕ, etaPairTerm w k)
      (Metric.ball s₀ (s₀.re / 2)) :=
  differentiableOn_tsum_of_summable_norm (summable_etaPairTerm_bound hs₀)
    (fun k => (differentiable_etaPairTerm k).differentiableOn) Metric.isOpen_ball
    fun k w hw => by
      by_cases hk : ((2 * k + 1 : ℕ) : ℝ) < ‖s₀‖ + s₀.re / 2
      · rw [if_pos hk]
        exact etaPairTerm_norm_le_two hs₀ hw k
      · rw [if_neg hk]
        exact etaPairTerm_norm_le_exp hs₀ hw hk

theorem analyticAt_dirichletEtaPair {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ dirichletEtaPair s :=
  (differentiableOn_dirichletEtaPair_ball hs).analyticAt
    (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self (by linarith : (0 : ℝ) < s.re / 2)))

/-- 配对 η 级数在右半平面 `{0 < re}` 上解析。 -/
theorem analyticOnNhd_dirichletEtaPair :
    AnalyticOnNhd ℂ dirichletEtaPair {s : ℂ | 0 < s.re} :=
  fun _s hs => analyticAt_dirichletEtaPair hs

/-!
## `(1 − 2·2^{-s})·ζ(s)` 在 `s = 1` 的可去奇点修正
-/

/-- η 因子：`fac(s) = 1 − 2·2^{-s}`（即 `1 − 2^{1−s}`）。 -/
noncomputable def zetaEtaFactor (s : ℂ) : ℂ := 1 - 2 * (2 : ℂ) ^ (-s)

theorem zetaEtaFactor_one : zetaEtaFactor 1 = 0 := by
  show (1 : ℂ) - 2 * (2 : ℂ) ^ (-(1 : ℂ)) = 0
  rw [cpow_neg, cpow_one, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), sub_self]

theorem differentiableAt_zetaEtaFactor (s : ℂ) :
    DifferentiableAt ℂ zetaEtaFactor s := by
  have h1 : DifferentiableAt ℂ (fun w : ℂ => (2 : ℂ) ^ (-w)) s :=
    DifferentiableAt.const_cpow differentiableAt_id.neg
      (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  exact (differentiableAt_const (1 : ℂ)).sub ((differentiableAt_const (2 : ℂ)).mul h1)

/-- `fac` 在 `s = 1` 的导数等于 `log 2 ≠ 0`（一阶零点）。 -/
theorem hasDerivAt_zetaEtaFactor_one :
    HasDerivAt zetaEtaFactor (↑(Real.log 2)) 1 := by
  have hmain : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ (-w))
      ((2 : ℂ) ^ (-(1 : ℂ)) * Complex.log 2 * (-1)) 1 :=
    HasDerivAt.const_cpow (hasDerivAt_id' (1 : ℂ)).neg
      (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  have hfull := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub
    ((hasDerivAt_const (1 : ℂ) (2 : ℂ)).mul hmain)
  convert hfull using 1
  have hval : (0 : ℂ) - (0 * (2 : ℂ) ^ (-(1 : ℂ)) +
      2 * ((2 : ℂ) ^ (-(1 : ℂ)) * Complex.log 2 * (-1))) = ↑(Real.log 2) := by
    rw [cpow_neg, cpow_one,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num [Complex.ext_iff],
      ← ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
    ring
  rw [hval]

/-- 留数：`fac(s)·ζ(s) → log 2`（`s → 1`，去心）。 -/
theorem tendsto_oneSubTwoCpowMulZeta_one :
    Filter.Tendsto (fun s => zetaEtaFactor s * riemannZeta s) (𝓝[≠] 1)
      (𝓝 (↑(Real.log 2))) := by
  have hslope : Filter.Tendsto (slope zetaEtaFactor 1) (𝓝[≠] 1)
      (𝓝 (↑(Real.log 2))) :=
    hasDerivAt_iff_tendsto_slope.mp hasDerivAt_zetaEtaFactor_one
  have hprod := riemannZeta_residue_one.mul hslope
  rw [one_mul] at hprod
  refine hprod.congr' (Filter.Eventually.of_forall fun z => ?_)
  show (z - 1) * riemannZeta z * slope zetaEtaFactor 1 z =
    zetaEtaFactor z * riemannZeta z
  by_cases hz : z = 1
  · subst hz
    show (1 - 1) * riemannZeta 1 * slope zetaEtaFactor 1 1 =
      zetaEtaFactor 1 * riemannZeta 1
    rw [zetaEtaFactor_one, sub_self, zero_mul, zero_mul]
  · rw [slope_def_field, zetaEtaFactor_one, sub_zero]
    field_simp [sub_ne_zero.mpr hz]

/-- `fac·ζ` 在 `s = 1` 的可去奇点修正：在 1 处取值 `log 2`。 -/
noncomputable def oneSubTwoCpowMulZetaReg : ℂ → ℂ :=
  Function.update (fun s => zetaEtaFactor s * riemannZeta s) 1 (↑(Real.log 2))

/-- 修正后的 `fac·ζ` 是整函数（在 1 处用可去奇点引理粘合）。 -/
theorem differentiable_oneSubTwoCpowMulZetaReg :
    Differentiable ℂ oneSubTwoCpowMulZetaReg := by
  intro s
  by_cases hs : s = 1
  · subst hs
    have hDball : DifferentiableOn ℂ (fun z => zetaEtaFactor z * riemannZeta z)
        (Metric.ball 1 (1 / 2) \ {1}) :=
      fun z hz => DifferentiableAt.differentiableWithinAt
        ((differentiableAt_zetaEtaFactor z).mul
          (differentiableAt_riemannZeta (Set.mem_compl_singleton_iff.mp hz.2)))
    have hfac0 : Filter.Tendsto zetaEtaFactor (𝓝[≠] 1) (𝓝 0) := by
      have h : Filter.Tendsto zetaEtaFactor (𝓝[≠] 1) (𝓝 (zetaEtaFactor 1)) :=
        (differentiableAt_zetaEtaFactor 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      rwa [zetaEtaFactor_one] at h
    have h1 : Filter.Tendsto (fun z => (z - 1) * (zetaEtaFactor z * riemannZeta z))
        (𝓝[≠] 1) (𝓝 0) := by
      have h := hfac0.mul riemannZeta_residue_one
      rw [zero_mul] at h
      exact h.congr' (Filter.Eventually.of_forall fun z => by ring)
    have hsub0 : Filter.Tendsto (fun z : ℂ => z - 1) (𝓝[≠] 1) (𝓝 0) := by
      have h : Filter.Tendsto (fun z : ℂ => z - 1) (𝓝 1) (𝓝 0) := by
        have h := (continuous_sub_right (1 : ℂ)).tendsto 1
        simpa using h
      exact h.mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto (fun z => (z - 1) * (zetaEtaFactor 1 * riemannZeta 1))
        (𝓝[≠] 1) (𝓝 (0 * (zetaEtaFactor 1 * riemannZeta 1))) :=
      hsub0.mul tendsto_const_nhds
    rw [zero_mul] at h2
    have hDs := h1.sub h2
    rw [sub_zero] at hDs
    have hquot : Filter.Tendsto
        (fun z => (zetaEtaFactor z * riemannZeta z - zetaEtaFactor 1 * riemannZeta 1) /
          (z - 1)⁻¹) (𝓝[≠] 1) (𝓝 0) :=
      hDs.congr' (Filter.Eventually.of_forall fun z => by
        show (z - 1) * (zetaEtaFactor z * riemannZeta z) -
            (z - 1) * (zetaEtaFactor 1 * riemannZeta 1) =
          (zetaEtaFactor z * riemannZeta z - zetaEtaFactor 1 * riemannZeta 1) /
            (z - 1)⁻¹
        rw [div_inv_eq_mul]
        ring)
    have ho : (fun z => zetaEtaFactor z * riemannZeta z -
        zetaEtaFactor 1 * riemannZeta 1) =o[𝓝[≠] 1] fun z => (z - 1)⁻¹ :=
      (Asymptotics.isLittleO_iff_tendsto fun z hz0 => by
        have hzs : z = 1 := sub_eq_zero.mp (inv_eq_zero.mp hz0)
        rw [hzs, sub_self]).mpr hquot
    have hUpd := differentiableOn_update_limUnder_of_isLittleO
      (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)) hDball ho
    have hlim : Filter.limUnder (𝓝[≠] 1) (fun z => zetaEtaFactor z * riemannZeta z) =
        ↑(Real.log 2) := tendsto_oneSubTwoCpowMulZeta_one.limUnder_eq
    rw [hlim] at hUpd
    exact (hUpd 1 (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)))
  · have hev : oneSubTwoCpowMulZetaReg =ᶠ[𝓝 s]
        (fun z => zetaEtaFactor z * riemannZeta z) :=
      (eventually_ne_nhds hs).mono fun z hz => by
        unfold oneSubTwoCpowMulZetaReg
        exact Function.update_of_ne hz (↑(Real.log 2))
          (fun w => zetaEtaFactor w * riemannZeta w)
    exact ((differentiableAt_zetaEtaFactor s).mul
      (differentiableAt_riemannZeta hs)).congr_of_eventuallyEq hev

/-- 修正后的 `fac·ζ` 在 `{0 < re}` 上解析。 -/
theorem analyticOnNhd_oneSubTwoCpowMulZetaReg :
    AnalyticOnNhd ℂ oneSubTwoCpowMulZetaReg {s : ℂ | 0 < s.re} :=
  (differentiable_oneSubTwoCpowMulZetaReg.differentiableOn
    (s := {s : ℂ | 0 < s.re})).analyticOnNhd (isOpen_Ioi.preimage continuous_re)

/-!
## `re s > 1` 上的恒等式 `η̃ = fac·ζ`
-/

theorem summable_cpow_neg_nat {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ((n : ℂ)) ^ (-s)) := by
  have hs0 : s ≠ 0 := by
    intro h
    subst h
    norm_num at hs
  have h1 : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  exact Summable.congr h1 fun n => by
    rw [LSeries.term_of_ne_zero' hs0, Pi.one_apply, one_div, ← cpow_neg]

/-- 奇数位项可和：`(2k+1)^{-s}`。 -/
theorem summable_odd_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable (fun k : ℕ => ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) := by
  have hbase : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-s.re)) := by
    have h1 := Real.summable_one_div_nat_rpow.mpr hs
    have hconv : (fun n : ℕ => 1 / (n : ℝ) ^ s.re) =
        fun n : ℕ => (n : ℝ) ^ (-s.re) := by
      funext n
      rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]
    rw [hconv] at h1
    exact (summable_nat_add_iff 1).mpr h1
  refine Summable.of_norm_bounded hbase fun k => ?_
  rw [← Complex.ofReal_natCast,
    norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (by omega : 0 < 2 * k + 1)),
    Complex.neg_re]
  exact Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))
    (by exact_mod_cast (by omega : k + 1 ≤ 2 * k + 1)) (by linarith)

/-- 偶数（正）位项可和：`(2(k+1))^{-s}`。 -/
theorem summable_even_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable (fun k : ℕ => ((2 * (k + 1) : ℕ) : ℂ) ^ (-s)) := by
  have hbase : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-s.re)) := by
    have h1 := Real.summable_one_div_nat_rpow.mpr hs
    have hconv : (fun n : ℕ => 1 / (n : ℝ) ^ s.re) =
        fun n : ℕ => (n : ℝ) ^ (-s.re) := by
      funext n
      rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]
    rw [hconv] at h1
    exact (summable_nat_add_iff 1).mpr h1
  refine Summable.of_norm_bounded (hbase.mul_left 2) fun k => ?_
  rw [← Complex.ofReal_natCast,
    norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (by omega : 0 < 2 * (k + 1))),
    Complex.neg_re]
  rw [show ((2 * (k + 1) : ℕ) : ℝ) = (2 : ℝ) * ((k + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
  have hX : 0 ≤ ((k + 1 : ℕ) : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2 : (2 : ℝ) ^ (-s.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  calc (2 : ℝ) ^ (-s.re) * ((k + 1 : ℕ) : ℝ) ^ (-s.re)
      ≤ 1 * ((k + 1 : ℕ) : ℝ) ^ (-s.re) := mul_le_mul_of_nonneg_right h2 hX
    _ = ((k + 1 : ℕ) : ℝ) ^ (-s.re) := one_mul _
    _ ≤ 2 * ((k + 1 : ℕ) : ℝ) ^ (-s.re) := by linarith [hX]

/-- `re s > 1` 时 `ζ(s) = Σ_n n^{-s}`。 -/
theorem riemannZeta_eq_tsum_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, ((n : ℂ)) ^ (-s) := by
  have hs0 : s ≠ 0 := by
    intro h
    subst h
    norm_num at hs
  rw [← LSeries_one_eq_riemannZeta hs]
  show (∑' n : ℕ, LSeries.term 1 s n) = _
  exact tsum_congr fun n => by
    rw [LSeries.term_of_ne_zero' hs0, Pi.one_apply, one_div, ← cpow_neg]

/-- 自然数到奇数的映射。 -/
def natOddSucc (k : ℕ) : ↥({n : ℕ | Odd n} : Set ℕ) := ⟨2 * k + 1, ⟨k, rfl⟩⟩

/-- 奇数到自然数的逆映射。 -/
noncomputable def natOddPred (n : ↥({n : ℕ | Odd n} : Set ℕ)) : ℕ := n.2.choose

/-- `ℕ ≃ {奇数}`：`k ↦ 2k+1`。 -/
noncomputable def natOddEquiv : ℕ ≃ ↥({n : ℕ | Odd n} : Set ℕ) where
  toFun := natOddSucc
  invFun := natOddPred
  left_inv k := by
    have hspec : 2 * k + 1 = 2 * natOddPred (natOddSucc k) + 1 :=
      (natOddSucc k).2.choose_spec
    omega
  right_inv n := by
    have hspec : n.1 = 2 * n.2.choose + 1 := n.2.choose_spec
    apply Subtype.ext
    show 2 * n.2.choose + 1 = n.1
    omega

/-- 自然数到偶数（奇数补集）的映射。 -/
def natEvenDouble (k : ℕ) : ↥({n : ℕ | Odd n} : Set ℕ)ᶜ :=
  ⟨2 * k, Nat.not_odd_iff_even.mpr ⟨k, by ring⟩⟩

/-- 偶数到自然数的逆映射（取半）。 -/
noncomputable def natEvenHalve (n : ↥({n : ℕ | Odd n} : Set ℕ)ᶜ) : ℕ :=
  (Nat.not_odd_iff_even.mp n.2).choose

/-- `ℕ ≃ {偶数}`：`k ↦ 2k`。 -/
noncomputable def natEvenComplEquiv : ℕ ≃ ↥({n : ℕ | Odd n} : Set ℕ)ᶜ where
  toFun := natEvenDouble
  invFun := natEvenHalve
  left_inv k := by
    have hspec : 2 * k = natEvenHalve (natEvenDouble k) + natEvenHalve (natEvenDouble k) :=
      (Nat.not_odd_iff_even.mp (natEvenDouble k).2).choose_spec
    omega
  right_inv n := by
    have hspec : n.1 = natEvenHalve n + natEvenHalve n :=
      (Nat.not_odd_iff_even.mp n.2).choose_spec
    apply Subtype.ext
    show 2 * natEvenHalve n = n.1
    omega

theorem tsum_odd_cpow_neg_eq {s : ℂ} :
    (∑' x : ↥({n : ℕ | Odd n} : Set ℕ), ((x : ℕ) : ℂ) ^ (-s)) =
      ∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s) :=
  (Equiv.tsum_eq natOddEquiv
    (fun x : ↥({n : ℕ | Odd n} : Set ℕ) => ((x : ℕ) : ℂ) ^ (-s))).symm

theorem tsum_evenCompl_cpow_neg_eq {s : ℂ} :
    (∑' x : ↥({n : ℕ | Odd n} : Set ℕ)ᶜ, ((x : ℕ) : ℂ) ^ (-s)) =
      ∑' k : ℕ, ((2 * k : ℕ) : ℂ) ^ (-s) :=
  (Equiv.tsum_eq natEvenComplEquiv
    (fun x : ↥({n : ℕ | Odd n} : Set ℕ)ᶜ => ((x : ℕ) : ℂ) ^ (-s))).symm

/-- 正偶数项和：`Σ_k (2(k+1))^{-s} = 2^{-s}·ζ(s)`。 -/
theorem tsum_even_tail_cpow_neg_eq {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, ((2 * (k + 1) : ℕ) : ℂ) ^ (-s)) = (2 : ℂ) ^ (-s) * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst h
    norm_num at hs
  have h2r : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num [Complex.ext_iff]
  have h0 : ((0 : ℕ) : ℂ) ^ (-s) = 0 := by
    rw [Nat.cast_zero]
    exact zero_cpow (neg_ne_zero.mpr hs0)
  rw [riemannZeta_eq_tsum_cpow_neg hs, Summable.tsum_eq_zero_add (summable_cpow_neg_nat hs)]
  show (∑' k : ℕ, ((2 * (k + 1) : ℕ) : ℂ) ^ (-s)) =
    (2 : ℂ) ^ (-s) * (((0 : ℕ) : ℂ) ^ (-s) + ∑' i : ℕ, ((i + 1 : ℕ) : ℂ) ^ (-s))
  rw [h0, zero_add, ← tsum_mul_left]
  exact tsum_congr fun k => by
    have hcast : ((2 * (k + 1) : ℕ) : ℂ) = ((2 : ℝ) : ℂ) * (((k + 1 : ℕ) : ℝ) : ℂ) := by
      rw [h2r, Complex.ofReal_natCast]
      push_cast
      ring
    rw [hcast, mul_cpow_ofReal_nonneg (by norm_num) (Nat.cast_nonneg _), h2r,
      Complex.ofReal_natCast]

/-- 偶数位项和（含 0 项）：`Σ_k (2k)^{-s} = 2^{-s}·ζ(s)`。 -/
theorem tsum_even_cpow_neg_eq {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, ((2 * k : ℕ) : ℂ) ^ (-s)) = (2 : ℂ) ^ (-s) * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst h
    norm_num at hs
  have hsum0 : Summable (fun k : ℕ => ((2 * k : ℕ) : ℂ) ^ (-s)) :=
    (summable_nat_add_iff 1).mp (summable_even_cpow_neg hs)
  have h0 : ((2 * 0 : ℕ) : ℂ) ^ (-s) = 0 := by
    have e : (2 * 0 : ℕ) = 0 := by norm_num
    rw [e, Nat.cast_zero]
    exact zero_cpow (neg_ne_zero.mpr hs0)
  rw [Summable.tsum_eq_zero_add hsum0]
  show ((2 * 0 : ℕ) : ℂ) ^ (-s) + (∑' i : ℕ, ((2 * (i + 1) : ℕ) : ℂ) ^ (-s)) =
    (2 : ℂ) ^ (-s) * riemannZeta s
  rw [h0, zero_add]
  exact tsum_even_tail_cpow_neg_eq hs

/-- `ζ` 的奇偶拆分：`ζ = Σ_{奇} + 2^{-s}·ζ`。 -/
theorem riemannZeta_eq_tsum_odd_add_tsum_even {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = (∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) +
      (2 : ℂ) ^ (-s) * riemannZeta s := by
  have hsplit := Summable.tsum_add_tsum_compl (s := {n : ℕ | Odd n})
    ((summable_cpow_neg_nat hs).subtype _) ((summable_cpow_neg_nat hs).subtype _)
  have hodd_t : (∑' x : ↥({n : ℕ | Odd n} : Set ℕ), ((x : ℕ) : ℂ) ^ (-s)) =
      ∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s) := tsum_odd_cpow_neg_eq
  have heven_t : (∑' x : ↥({n : ℕ | Odd n} : Set ℕ)ᶜ, ((x : ℕ) : ℂ) ^ (-s)) =
      ∑' k : ℕ, ((2 * k : ℕ) : ℂ) ^ (-s) := tsum_evenCompl_cpow_neg_eq
  calc riemannZeta s = ∑' n : ℕ, ((n : ℂ)) ^ (-s) := riemannZeta_eq_tsum_cpow_neg hs
    _ = (∑' x : ↥({n : ℕ | Odd n} : Set ℕ), ((x : ℕ) : ℂ) ^ (-s)) +
          (∑' x : ↥({n : ℕ | Odd n} : Set ℕ)ᶜ, ((x : ℕ) : ℂ) ^ (-s)) := hsplit.symm
    _ = (∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) +
          (2 : ℂ) ^ (-s) * riemannZeta s := by
        rw [hodd_t, heven_t, tsum_even_cpow_neg_eq hs]

/-- `re s > 1` 上 `η̃(s) = (1 − 2^{1−s})·ζ(s)`。 -/
theorem dirichletEtaPair_eq {s : ℂ} (hs : 1 < s.re) :
    dirichletEtaPair s = zetaEtaFactor s * riemannZeta s := by
  show (∑' k : ℕ, (((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s))) = _
  have hodd := summable_odd_cpow_neg hs
  have heven : Summable (fun k : ℕ => ((2 * k + 2 : ℕ) : ℂ) ^ (-s)) :=
    Summable.congr (summable_even_cpow_neg hs) fun k => by
      rw [show (2 * k + 2 : ℕ) = 2 * (k + 1) by ring]
  have hts : (∑' k : ℕ, (((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s))) =
      (∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) -
        ∑' k : ℕ, ((2 * k + 2 : ℕ) : ℂ) ^ (-s) :=
    Summable.tsum_sub hodd heven
  have hE : (∑' k : ℕ, ((2 * k + 2 : ℕ) : ℂ) ^ (-s)) =
      (2 : ℂ) ^ (-s) * riemannZeta s := by
    have h1 : (∑' k : ℕ, ((2 * k + 2 : ℕ) : ℂ) ^ (-s)) =
        ∑' k : ℕ, ((2 * (k + 1) : ℕ) : ℂ) ^ (-s) :=
      tsum_congr fun k => by rw [show (2 * k + 2 : ℕ) = 2 * (k + 1) by ring]
    rw [h1, tsum_even_tail_cpow_neg_eq hs]
  have hO : (∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) =
      riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s := by
    have h := riemannZeta_eq_tsum_odd_add_tsum_even hs
    exact eq_sub_iff_add_eq.mpr h.symm
  rw [hts, hO, hE]
  show riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s -
      (2 : ℂ) ^ (-s) * riemannZeta s = (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s
  ring

/-- 恒等式延拓到整个右半平面：`0 < re s` 时 `η̃(s) = reg(s)`
（`reg` 为 `fac·ζ` 在 `s = 1` 的可去奇点修正）。 -/
theorem dirichletEtaPair_eq_on_halfplane {s : ℂ} (hs : 0 < s.re) :
    dirichletEtaPair s = oneSubTwoCpowMulZetaReg s := by
  have hdiff : AnalyticOnNhd ℂ (dirichletEtaPair - oneSubTwoCpowMulZetaReg)
      {z : ℂ | 0 < z.re} :=
    analyticOnNhd_dirichletEtaPair.sub analyticOnNhd_oneSubTwoCpowMulZetaReg
  have hpre : IsPreconnected {z : ℂ | 0 < z.re} :=
    (convex_halfSpace_re_gt 0).isPreconnected
  have hmem2 : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    show (0 : ℝ) < (2 : ℂ).re
    norm_num
  have hW : ∀ᶠ z in 𝓝 (2 : ℂ), (dirichletEtaPair - oneSubTwoCpowMulZetaReg) z = 0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self (by norm_num : (0 : ℝ) < (1 : ℝ) / 2))] with z hz
    have hzre : 1 < z.re := by
      have h1 : ‖z - 2‖ < 1 / 2 := by
        have h := Metric.mem_ball.mp hz
        rwa [dist_eq_norm] at h
      have h2 : |z.re - (2 : ℂ).re| ≤ ‖z - 2‖ := by
        have h := abs_re_le_norm (z - 2)
        rwa [Complex.sub_re] at h
      have h3 : (2 : ℂ).re = 2 := by norm_num
      have h4 := abs_le.mp h2
      linarith [h4.2]
    have hz1 : z ≠ 1 := by
      intro h
      rw [h, Complex.one_re] at hzre
      linarith
    show dirichletEtaPair z - oneSubTwoCpowMulZetaReg z = 0
    have h1 : dirichletEtaPair z = zetaEtaFactor z * riemannZeta z :=
      dirichletEtaPair_eq hzre
    have h2 : oneSubTwoCpowMulZetaReg z = zetaEtaFactor z * riemannZeta z := by
      unfold oneSubTwoCpowMulZetaReg
      exact Function.update_of_ne hz1 (↑(Real.log 2))
        (fun w => zetaEtaFactor w * riemannZeta w)
    rw [h1, h2, sub_self]
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), (dirichletEtaPair - oneSubTwoCpowMulZetaReg) z = 0 :=
    (hW.filter_mono nhdsWithin_le_nhds).frequently
  have hEq := hdiff.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre hmem2 hfreq
  have h := hEq hs
  simp only [Pi.zero_apply, Pi.sub_apply] at h
  exact sub_eq_zero.mp h

/-!
## 实轴点上的正性与主定理
-/

/-- 实轴 `x > 0` 上配对 η 级数的实部下界：首项 `1 − 2^{-x}`。 -/
theorem dirichletEtaPair_re_ge {x : ℝ} (hx : 0 < x) :
    1 - (2 : ℝ) ^ (-x) ≤ (dirichletEtaPair (↑x)).re := by
  have hsx : 0 < (↑x : ℂ).re := by rw [Complex.ofReal_re]; exact hx
  have hterm : ∀ k : ℕ, etaPairTerm (↑x) k =
      (↑(((2 * k + 1 : ℕ) : ℝ) ^ (-x) - ((2 * k + 2 : ℕ) : ℝ) ^ (-x)) : ℂ) := by
    intro k
    show ((2 * k + 1 : ℕ) : ℂ) ^ (-(x : ℂ)) - ((2 * k + 2 : ℕ) : ℂ) ^ (-(x : ℂ)) = _
    rw [← Complex.ofReal_natCast, ← ofReal_neg, ← ofReal_cpow (Nat.cast_nonneg (2 * k + 1)),
      ← Complex.ofReal_natCast, ← ofReal_cpow (Nat.cast_nonneg (2 * k + 2)), ← ofReal_sub]
  have hsum : Summable (fun k : ℕ => etaPairTerm (↑x) k) := summable_etaPairTerm hsx
  have hsumr : Summable (fun k : ℕ =>
      ((2 * k + 1 : ℕ) : ℝ) ^ (-x) - ((2 * k + 2 : ℕ) : ℝ) ^ (-x)) :=
    Complex.summable_ofReal.mp (Summable.congr hsum hterm)
  have htsum : dirichletEtaPair (↑x) =
      (↑(∑' k : ℕ, (((2 * k + 1 : ℕ) : ℝ) ^ (-x) -
        ((2 * k + 2 : ℕ) : ℝ) ^ (-x))) : ℂ) := by
    show (∑' k : ℕ, etaPairTerm (↑x) k) = _
    rw [ofReal_tsum]
    exact tsum_congr hterm
  have hg0 : ∀ k : ℕ, 0 ≤
      ((2 * k + 1 : ℕ) : ℝ) ^ (-x) - ((2 * k + 2 : ℕ) : ℝ) ^ (-x) := fun k =>
    sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos
      (by positivity : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ))
      (by exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * k + 2))
      (by linarith : -x ≤ 0))
  have h0 : ((2 * 0 + 1 : ℕ) : ℝ) ^ (-x) - ((2 * 0 + 2 : ℕ) : ℝ) ^ (-x) =
      1 - (2 : ℝ) ^ (-x) := by
    have e1 : ((2 * 0 + 1 : ℕ) : ℝ) = 1 := by norm_num
    have e2 : ((2 * 0 + 2 : ℕ) : ℝ) = 2 := by norm_num
    rw [e1, e2, Real.one_rpow]
  have hle := hsumr.le_tsum 0 (fun j _ => hg0 j)
  rw [h0] at hle
  rw [htsum, ofReal_re]
  exact hle

/-- **主定理**：`ζ` 在实轴区间 `(0,1)` 上无零点。 -/
theorem riemannZeta_ofReal_ne_zero_of_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    riemannZeta (↑x) ≠ 0 := by
  have hsx : 0 < (↑x : ℂ).re := by rw [Complex.ofReal_re]; exact hx0
  have heq := dirichletEtaPair_eq_on_halfplane hsx
  have hne : (↑x : ℂ) ≠ 1 := by
    intro h
    have h2 := congrArg Complex.re h
    rw [Complex.ofReal_re, Complex.one_re] at h2
    linarith
  have hreg : oneSubTwoCpowMulZetaReg (↑x) = zetaEtaFactor (↑x) * riemannZeta (↑x) := by
    unfold oneSubTwoCpowMulZetaReg
    exact Function.update_of_ne hne (↑(Real.log 2))
      (fun w => zetaEtaFactor w * riemannZeta w)
  rw [hreg] at heq
  have hη := dirichletEtaPair_re_ge hx0
  have hg00 : (2 : ℝ) ^ (-x) < 1 := by
    have h1 : (2 : ℝ) ^ (-x) < (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    rwa [Real.rpow_zero] at h1
  intro hζ
  rw [hζ, mul_zero] at heq
  rw [heq, Complex.zero_re] at hη
  linarith [hη, hg00]
