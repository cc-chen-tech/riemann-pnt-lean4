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
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.PSeries
import ZeroFreeRegion.PhragmenLindelofZeta
import ZeroFreeRegion.MeromorphicAux
import RiemannExplorer.XiFunction

open scoped Topology

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

/-- ζ 的 Dirichlet 级数界：`2 ≤ re s` 时 `‖ζ(s)‖ ≤ π²/6`。 -/
theorem norm_riemannZeta_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ Real.pi ^ 2 / 6 := by
  have hs1 : 1 < s.re := by linarith
  have hterm : ∀ n : ℕ, ‖1 / (n : ℂ) ^ s‖ = 1 / (n : ℝ) ^ (s.re) := by
    intro n
    by_cases hn : n = 0
    · rw [hn]
      simp [Complex.zero_cpow (Complex.ne_zero_of_one_lt_re hs1),
        Real.zero_rpow (by linarith : (s.re) ≠ 0)]
    · have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [norm_div, norm_one, ← Complex.ofReal_natCast n,
        Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
  have hsumm : Summable fun n : ℕ => (1:ℝ) / (n : ℝ) ^ (s.re) :=
    Real.summable_one_div_nat_rpow.mpr hs1
  rw [zeta_eq_tsum_one_div_nat_cpow hs1]
  calc ‖∑' n : ℕ, 1 / (n : ℂ) ^ s‖ ≤ ∑' n : ℕ, ‖1 / (n : ℂ) ^ s‖ :=
        norm_tsum_le_tsum_norm (by simpa only [hterm] using hsumm)
    _ = ∑' n : ℕ, (1:ℝ) / (n : ℝ) ^ (s.re) := tsum_congr hterm
    _ ≤ ∑' n : ℕ, (1:ℝ) / (n : ℝ) ^ (2:ℝ) := by
        refine hsumm.tsum_le_tsum (fun n => ?_)
          (Real.summable_one_div_nat_rpow.mpr one_lt_two)
        by_cases hn : n = 0
        · rw [hn, Nat.cast_zero, Real.zero_rpow (by linarith : (s.re) ≠ 0),
            Real.zero_rpow (two_ne_zero : (2:ℝ) ≠ 0)]
        · have hn1 : (1:ℝ) ≤ (n : ℝ) := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
          exact one_div_le_one_div_of_le
            (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hn1) _)
            (Real.rpow_le_rpow_of_exponent_le hn1 hs)
    _ = Real.pi ^ 2 / 6 := by
        have h2 : (fun n : ℕ => (1:ℝ) / (n : ℝ) ^ (2:ℝ)) =
            fun n : ℕ => (1:ℝ) / (n : ℝ) ^ 2 := by
          funext n
          simp
        rw [h2, hasSum_zeta_two.tsum_eq]

/-- ζ 在避开极点的紧竖条上的有界性：`re ∈ [1/2, 4]`、`|im| ≤ 1`、
`|s − 1| ≥ 1` 时 `‖ζ‖` 有一致上界。 -/
theorem exists_norm_riemannZeta_le_on_compact_strip :
    ∃ M : ℝ, ∀ s : ℂ, s.re ∈ Set.Icc (1 / 2 : ℝ) 4 → |s.im| ≤ 1 →
      1 ≤ ‖s - 1‖ → ‖riemannZeta s‖ ≤ M := by
  let K : Set ℂ := {s | s.re ∈ Set.Icc (1 / 2 : ℝ) 4 ∧ |s.im| ≤ 1 ∧ 1 ≤ ‖s - 1‖}
  have hKclosed : IsClosed K :=
    ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const)).inter
      ((isClosed_le Complex.continuous_im.abs continuous_const).inter
        (isClosed_le continuous_const (continuous_id.sub continuous_const).norm))
  have hKbound : Bornology.IsBounded K := by
    apply Metric.isBounded_closedBall.subset
    intro s hs
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖s‖ = ‖(s.re : ℂ) + (s.im : ℂ) * Complex.I‖ := by rw [Complex.re_add_im]
      _ ≤ ‖(s.re : ℂ)‖ + ‖(s.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |s.re| + |s.im| := by
          have h1 : ‖(s.re : ℂ)‖ = |s.re| := RCLike.norm_ofReal s.re
          have h2 : ‖(s.im : ℂ) * Complex.I‖ = |s.im| := by
            rw [norm_mul, Complex.norm_I, mul_one]
            exact RCLike.norm_ofReal s.im
          rw [h1, h2]
      _ ≤ 4 + 1 := by
          have h1 : |s.re| ≤ 4 := by
            have hre := hs.1
            rw [abs_le]
            exact ⟨by linarith [hre.1], hre.2⟩
          have h2 : |s.im| ≤ 1 := hs.2.1
          linarith
      _ ≤ 5 := by norm_num
  have hKcomp : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKclosed hKbound
  have hcont : ContinuousOn (fun s => ‖riemannZeta s‖) K := by
    intro s hs
    have hsne : s ≠ 1 := by
      intro heq
      have h := hs.2.2
      rw [heq] at h
      norm_num at h
    exact ((differentiableAt_riemannZeta hsne).continuousAt.continuousWithinAt).norm
  obtain ⟨M, hM⟩ := hKcomp.bddAbove_image hcont
  exact ⟨M, fun s hsre hsim hsn =>
    hM (Set.mem_image_of_mem (fun s => ‖riemannZeta s‖) ⟨hsre, hsim, hsn⟩)⟩

/-- `(s − 1)·ζ(s)` 在右半平面（避开极点）的 5 次增长界：
`1/2 ≤ re s` 且 `1 ≤ ‖s − 1‖` 时 `‖(s − 1)·ζ(s)‖ ≤ C·(1 + ‖s‖)⁵`。 -/
theorem exists_norm_sub_one_mul_riemannZeta_le_fifth :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → 1 ≤ ‖s - 1‖ →
      ‖(s - 1) * riemannZeta s‖ ≤ C * (1 + ‖s‖) ^ 5 := by
  obtain ⟨C₀, hC₀, hstrip⟩ :=
    ZeroFreeRegion.exists_norm_riemannZeta_le_polynomial_on_zero_four
  obtain ⟨M, hM⟩ := exists_norm_riemannZeta_le_on_compact_strip
  refine ⟨max (Real.pi ^ 2 / 6) (max M (81 * C₀)), fun s hsre hsn => ?_⟩
  have hsn1 : ‖s - 1‖ ≤ 1 + ‖s‖ := by
    have h := norm_sub_le s 1
    rw [norm_one, add_comm ‖s‖ 1] at h
    exact h
  have h1s : (1:ℝ) ≤ 1 + ‖s‖ := le_add_of_nonneg_right (norm_nonneg s)
  by_cases h4 : 4 ≤ s.re
  · -- Dirichlet 级数区域
    have hz := norm_riemannZeta_le_of_two_le_re (by linarith : 2 ≤ s.re)
    calc ‖(s - 1) * riemannZeta s‖ = ‖s - 1‖ * ‖riemannZeta s‖ := norm_mul _ _
      _ ≤ (1 + ‖s‖) * (Real.pi ^ 2 / 6) :=
          mul_le_mul hsn1 hz (norm_nonneg _) (le_trans zero_le_one h1s)
      _ ≤ max (Real.pi ^ 2 / 6) (max M (81 * C₀)) * (1 + ‖s‖) ^ 5 := by
          have hpow : (1:ℝ) + ‖s‖ ≤ (1 + ‖s‖) ^ 5 := by
            have h1 : (1:ℝ) + ‖s‖ ≤ (1 + ‖s‖) ^ 1 := by rw [pow_one]
            exact h1.trans (pow_le_pow_right₀ h1s (by norm_num : 1 ≤ 5))
          calc (1 + ‖s‖) * (Real.pi ^ 2 / 6)
              ≤ (1 + ‖s‖) ^ 5 * (Real.pi ^ 2 / 6) :=
                mul_le_mul_of_nonneg_right hpow
                  (by positivity : (0:ℝ) ≤ Real.pi ^ 2 / 6)
            _ = (Real.pi ^ 2 / 6) * (1 + ‖s‖) ^ 5 := by ring
            _ ≤ max (Real.pi ^ 2 / 6) (max M (81 * C₀)) * (1 + ‖s‖) ^ 5 :=
                mul_le_mul_of_nonneg_right (le_max_left _ _)
                  (pow_nonneg (le_trans zero_le_one h1s) _)
  · have hre4 : s.re ≤ 4 := le_of_not_ge h4
    by_cases ht : 1 ≤ |s.im|
    · -- 临界带内、高虚部：项目的 Phragmén–Lindelöf 四次界
      have hz := hstrip s ⟨by linarith, hre4⟩ ht
      have hts : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
      have harg : (|s.im| + 3) ^ 4 ≤ (3 * (1 + ‖s‖)) ^ 4 := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [hts]
      calc ‖(s - 1) * riemannZeta s‖ = ‖s - 1‖ * ‖riemannZeta s‖ := norm_mul _ _
        _ ≤ (1 + ‖s‖) * (C₀ * (|s.im| + 3) ^ 4) :=
            mul_le_mul hsn1 hz (norm_nonneg _) (le_trans zero_le_one h1s)
        _ ≤ (1 + ‖s‖) * (C₀ * (3 * (1 + ‖s‖)) ^ 4) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left harg hC₀) (le_trans zero_le_one h1s)
        _ = 81 * C₀ * (1 + ‖s‖) ^ 5 := by ring
        _ ≤ max (Real.pi ^ 2 / 6) (max M (81 * C₀)) * (1 + ‖s‖) ^ 5 :=
            mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _))
              (pow_nonneg (le_trans zero_le_one h1s) _)
    · -- 临界带内、低虚部：紧竖条界
      have ht1 : |s.im| ≤ 1 := le_of_not_ge ht
      have hz := hM s ⟨hsre, hre4⟩ ht1 hsn
      have hMnn : 0 ≤ M := le_trans (norm_nonneg _) hz
      have hpow : (1:ℝ) + ‖s‖ ≤ (1 + ‖s‖) ^ 5 := by
        have h1 : (1:ℝ) + ‖s‖ ≤ (1 + ‖s‖) ^ 1 := by rw [pow_one]
        exact h1.trans (pow_le_pow_right₀ h1s (by norm_num : 1 ≤ 5))
      calc ‖(s - 1) * riemannZeta s‖ = ‖s - 1‖ * ‖riemannZeta s‖ := norm_mul _ _
        _ ≤ (1 + ‖s‖) * M :=
            mul_le_mul hsn1 hz (norm_nonneg _) (le_trans zero_le_one h1s)
        _ ≤ (1 + ‖s‖) ^ 5 * M := mul_le_mul_of_nonneg_right hpow hMnn
        _ = M * (1 + ‖s‖) ^ 5 := by ring
        _ ≤ max (Real.pi ^ 2 / 6) (max M (81 * C₀)) * (1 + ‖s‖) ^ 5 :=
            mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _))
              (pow_nonneg (le_trans zero_le_one h1s) _)

/-! ## ξ 的整体增长阶（≤ 1，对数尺度） -/

/-- 吸收引理：任何「正常数 × `(1+t)^a`」都被对数尺度的
`exp(K·(1+t)·log(4+t))` 控制（`t ≥ 0`）。 -/
theorem exists_exp_one_add_mul_log_bound (A : ℝ) (hA : 0 < A) (a : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t →
      A * (1 + t) ^ a ≤ Real.exp (K * (1 + t) * Real.log (4 + t)) := by
  refine ⟨max 0 (Real.log A / Real.log 4) + max 0 a,
    add_nonneg (le_max_left _ _) (le_max_left _ _), fun t ht => ?_⟩
  have hL4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have h1t : (0:ℝ) < 1 + t := by linarith
  have hL : Real.log 4 ≤ Real.log (4 + t) := Real.log_le_log (by norm_num) (by linarith)
  have hL1 : Real.log (1 + t) ≤ Real.log (4 + t) := Real.log_le_log h1t (by linarith)
  have hlog1nn : (0:ℝ) ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  have hLnn : (0:ℝ) ≤ Real.log (4 + t) := hL4.le.trans hL
  have hu : Real.log A ≤ max 0 (Real.log A / Real.log 4) * Real.log (4 + t) := by
    by_cases hA1 : 0 ≤ Real.log A
    · calc Real.log A = (Real.log A / Real.log 4) * Real.log 4 :=
          (div_mul_cancel₀ (Real.log A) hL4.ne').symm
        _ ≤ (Real.log A / Real.log 4) * Real.log (4 + t) :=
            mul_le_mul_of_nonneg_left hL (div_nonneg hA1 hL4.le)
        _ ≤ max 0 (Real.log A / Real.log 4) * Real.log (4 + t) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hLnn
    · exact (le_of_not_ge hA1).trans (mul_nonneg (le_max_left _ _) hLnn)
  have hv : a * Real.log (1 + t) ≤ max 0 a * Real.log (4 + t) := by
    by_cases ha : 0 ≤ a
    · calc a * Real.log (1 + t) ≤ a * Real.log (4 + t) :=
          mul_le_mul_of_nonneg_left hL1 ha
        _ ≤ max 0 a * Real.log (4 + t) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hLnn
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ha) hlog1nn).trans
        (mul_nonneg (le_max_left _ _) hLnn)
  have hkey : Real.log A + a * Real.log (1 + t) ≤
      (max 0 (Real.log A / Real.log 4) + max 0 a) * (1 + t) * Real.log (4 + t) := by
    have hnn : (0:ℝ) ≤
        (max 0 (Real.log A / Real.log 4) + max 0 a) * Real.log (4 + t) :=
      mul_nonneg (add_nonneg (le_max_left _ _) (le_max_left _ _)) hLnn
    calc Real.log A + a * Real.log (1 + t)
        ≤ max 0 (Real.log A / Real.log 4) * Real.log (4 + t) +
            max 0 a * Real.log (4 + t) := add_le_add hu hv
      _ = (max 0 (Real.log A / Real.log 4) + max 0 a) * Real.log (4 + t) := by ring
      _ = ((max 0 (Real.log A / Real.log 4) + max 0 a) * Real.log (4 + t)) * 1 :=
          (mul_one _).symm
      _ ≤ ((max 0 (Real.log A / Real.log 4) + max 0 a) * Real.log (4 + t)) * (1 + t) :=
          mul_le_mul_of_nonneg_left (by linarith) hnn
      _ = (max 0 (Real.log A / Real.log 4) + max 0 a) * (1 + t) * Real.log (4 + t) :=
          by ring
  calc A * (1 + t) ^ a = Real.exp (Real.log (A * (1 + t) ^ a)) :=
        (Real.exp_log (mul_pos hA (Real.rpow_pos_of_pos h1t a))).symm
    _ = Real.exp (Real.log A + a * Real.log (1 + t)) := by
        rw [Real.log_mul (ne_of_gt hA) (ne_of_gt (Real.rpow_pos_of_pos h1t a)),
          Real.log_rpow h1t]
    _ ≤ Real.exp ((max 0 (Real.log A / Real.log 4) + max 0 a) * (1 + t) *
          Real.log (4 + t)) := Real.exp_le_exp.mpr hkey

/-- **ξ 的增长阶至多为 1**（对数尺度）：存在常数 `K` 使对所有 `s : ℂ`，
`‖ξ(s)‖ ≤ exp(K·(1+‖s‖)·log(4+‖s‖))`。

证明分三区：右半平面大区（`1/2 ≤ re s`、`2 ≤ ‖s‖`）用经典乘积
`ξ = (1/2)·s·Gammaℝ·((s−1)ζ)` 配合 Γ 的阶 1 界（`Complex.norm_Gamma_le_exp`）、
`(s−1)ζ` 的五次界（`exists_norm_sub_one_mul_riemannZeta_le_fifth`）与
`‖π^(−s/2)‖ ≤ 1`；紧盘 `‖s‖ ≤ 2` 用连续性；左半平面用函数方程
`ξ(s) = ξ(1−s)` 归约。这是 Hadamard 展开缺口的「增长阶」组件。 -/
theorem exists_norm_xiFunction_le_exp_order_one :
    ∃ K : ℝ, ∀ s : ℂ,
      ‖xiFunction s‖ ≤ Real.exp (K * (1 + ‖s‖) * Real.log (4 + ‖s‖)) := by
  obtain ⟨C, hC⟩ := exists_norm_sub_one_mul_riemannZeta_le_fifth
  have hCnn : (0:ℝ) ≤ C := by
    have h := hC 2 (by simp; norm_num)
      (le_of_eq (by rw [show ((2:ℂ) - 1) = 1 by ring, norm_one]))
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) (by positivity)
  -- 紧盘 `‖s‖ ≤ 2` 上的界
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, ∀ s : ℂ, ‖s‖ ≤ 2 → ‖xiFunction s‖ ≤ M₀ := by
    have hcomp : IsCompact (Metric.closedBall (0 : ℂ) 2) := isCompact_closedBall _ _
    have hcont : ContinuousOn (fun s => ‖xiFunction s‖) (Metric.closedBall (0 : ℂ) 2) :=
      differentiable_xiFunction.continuous.norm.continuousOn
    obtain ⟨M₀, hM₀⟩ := hcomp.bddAbove_image hcont
    refine ⟨M₀, fun s hs => hM₀ (Set.mem_image_of_mem _
      (by rwa [Metric.mem_closedBall, dist_zero_right]))⟩
  have hM0nn : (0:ℝ) ≤ M₀ :=
    (norm_nonneg _).trans (hM₀ 0 (by rw [norm_zero]; norm_num))
  -- 吸收常数
  obtain ⟨K₁, hK₁, hK₁b⟩ := exists_exp_one_add_mul_log_bound (8 * C / 5 + 1)
    (by positivity) 6
  obtain ⟨K₂, hK₂, hK₂b⟩ := exists_exp_one_add_mul_log_bound (M₀ + 1)
    (by linarith) 0
  -- 右半平面的统一界（大区 + 小区）
  set K₃ := max (K₁ + 4) K₂ with hK₃def
  have hK₃nn : (0:ℝ) ≤ K₃ := (add_nonneg hK₁ (by norm_num)).trans (le_max_left _ _)
  have hAB : ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖xiFunction s‖ ≤ Real.exp (K₃ * (1 + ‖s‖) * Real.log (4 + ‖s‖)) := by
    intro s hsre
    have h1snn : (0:ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
    have hLnn : (0:ℝ) ≤ Real.log (4 + ‖s‖) :=
      Real.log_nonneg (by linarith [norm_nonneg s])
    by_cases h2 : 2 ≤ ‖s‖
    · -- 大区：经典乘积
      have hs0 : s ≠ 0 := by
        intro h; rw [h, norm_zero] at h2; norm_num at h2
      have hs1 : s ≠ 1 := by
        intro h; rw [h, norm_one] at h2; norm_num at h2
      have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
      have hsn1 : 1 ≤ ‖s - 1‖ := by
        have hle : ‖s‖ ≤ ‖s - 1‖ + 1 := by
          calc ‖s‖ = ‖(s - 1) + 1‖ := by rw [sub_add_cancel]
            _ ≤ ‖s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
            _ = ‖s - 1‖ + 1 := by rw [norm_one]
        linarith
      have hz := hC s hsre hsn1
      have hre2 : (s / 2 : ℂ).re = s.re / 2 := by
        rw [show (s / 2 : ℂ) = s * ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
        rw [Complex.mul_re]
        simp
        ring
      have hren2 : (-s / 2 : ℂ).re = -s.re / 2 := by
        rw [show (-s / 2 : ℂ) = s * ((-1 / 2 : ℝ) : ℂ) by push_cast; ring]
        rw [Complex.mul_re]
        simp
        ring
      have hpi : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, hren2]
        exact Real.rpow_le_one_of_one_le_of_nonpos
          (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ Real.pi) (by linarith)
      have hgam : ‖Complex.Gamma (s / 2)‖ ≤
          Real.exp (Real.log (16 / 5) + (s.re / 2 + 3) * Real.log (s.re / 2 + 3)) := by
        have h := Complex.norm_Gamma_le_exp (z := s / 2) (by rw [hre2]; linarith)
        rwa [hre2] at h
      have hGR : ‖Complex.Gammaℝ s‖ ≤
          Real.exp (Real.log (16 / 5) + (s.re / 2 + 3) * Real.log (s.re / 2 + 3)) := by
        have heq : ‖Complex.Gammaℝ s‖ =
            ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ := by
          rw [show Complex.Gammaℝ s =
              (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) from rfl, norm_mul]
        rw [heq]
        calc ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
            ≤ 1 * Real.exp (Real.log (16 / 5) +
                (s.re / 2 + 3) * Real.log (s.re / 2 + 3)) :=
              mul_le_mul hpi hgam (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
      -- `(x+3)·log(x+3)` 的单调性：把 `s.re/2` 换成 `‖s‖/2`
      have hsre_norm : s.re ≤ ‖s‖ := Complex.re_le_norm s
      have hmono : (s.re / 2 + 3) * Real.log (s.re / 2 + 3) ≤
          (‖s‖ / 2 + 3) * Real.log (‖s‖ / 2 + 3) := by
        have h1 : s.re / 2 + 3 ≤ ‖s‖ / 2 + 3 := by linarith
        have h2 : Real.log (s.re / 2 + 3) ≤ Real.log (‖s‖ / 2 + 3) :=
          Real.log_le_log (by linarith) h1
        exact mul_le_mul h1 h2 (Real.log_nonneg (by linarith)) (by linarith)
      have hquad : (‖s‖ / 2 + 3) * Real.log (‖s‖ / 2 + 3) ≤
          4 * (1 + ‖s‖) * Real.log (4 + ‖s‖) := by
        have hLl : Real.log (‖s‖ / 2 + 3) ≤ Real.log (4 + ‖s‖) :=
          Real.log_le_log (by linarith [norm_nonneg s]) (by linarith [norm_nonneg s])
        have hb2 : ‖s‖ / 2 + 3 ≤ 4 + ‖s‖ := by linarith [norm_nonneg s]
        calc (‖s‖ / 2 + 3) * Real.log (‖s‖ / 2 + 3)
            ≤ (4 + ‖s‖) * Real.log (4 + ‖s‖) :=
              mul_le_mul hb2 hLl (Real.log_nonneg (by linarith [norm_nonneg s]))
                (by linarith [norm_nonneg s])
          _ ≤ (4 * (1 + ‖s‖)) * Real.log (4 + ‖s‖) :=
              mul_le_mul_of_nonneg_right (by linarith [norm_nonneg s]) hLnn
          _ = 4 * (1 + ‖s‖) * Real.log (4 + ‖s‖) := by ring
      have hexp1 : Real.exp (Real.log (16 / 5) + (s.re / 2 + 3) * Real.log (s.re / 2 + 3)) ≤
          Real.exp (Real.log (16 / 5) + 4 * (1 + ‖s‖) * Real.log (4 + ‖s‖)) :=
        Real.exp_le_exp.mpr (add_le_add le_rfl (hmono.trans hquad))
      -- 主链：经典乘积的范数
      rw [xiFunction_eq_classical hs0 hs1 hG]
      have hrw : (1 / 2 : ℂ) * s * (s - 1) * Complex.Gammaℝ s * riemannZeta s =
          (1 / 2) * s * Complex.Gammaℝ s * ((s - 1) * riemannZeta s) := by ring
      rw [hrw]
      have hnorm : ‖(1 / 2 : ℂ) * s * Complex.Gammaℝ s * ((s - 1) * riemannZeta s)‖ =
          (1 / 2) * ‖s‖ * ‖Complex.Gammaℝ s‖ * ‖(s - 1) * riemannZeta s‖ := by
        have h1n : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
        rw [norm_mul, norm_mul, norm_mul, h1n]
      rw [hnorm]
      calc (1 / 2) * ‖s‖ * ‖Complex.Gammaℝ s‖ * ‖(s - 1) * riemannZeta s‖
          ≤ (1 / 2) * ‖s‖ *
              Real.exp (Real.log (16 / 5) + 4 * (1 + ‖s‖) * Real.log (4 + ‖s‖)) *
              (C * (1 + ‖s‖) ^ 5) := by
            apply mul_le_mul _ hz (norm_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_left (hGR.trans hexp1) (by positivity)
        _ = (16 / 5) * (C / 2) * ‖s‖ * (1 + ‖s‖) ^ 5 *
              Real.exp (4 * (1 + ‖s‖) * Real.log (4 + ‖s‖)) := by
            rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 16 / 5)]
            ring
        _ ≤ (8 * C / 5 + 1) * (1 + ‖s‖) ^ 6 *
              Real.exp (4 * (1 + ‖s‖) * Real.log (4 + ‖s‖)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            have hs6 : ‖s‖ * (1 + ‖s‖) ^ 5 ≤ (1 + ‖s‖) ^ 6 := by
              have e : (1 + ‖s‖) ^ 6 = (1 + ‖s‖) ^ 5 * (1 + ‖s‖) := by ring
              have hmul := mul_le_mul_of_nonneg_left
                (by linarith [norm_nonneg s] : ‖s‖ ≤ 1 + ‖s‖)
                (pow_nonneg h1snn 5)
              calc ‖s‖ * (1 + ‖s‖) ^ 5 = (1 + ‖s‖) ^ 5 * ‖s‖ := mul_comm _ _
                _ ≤ (1 + ‖s‖) ^ 5 * (1 + ‖s‖) := hmul
                _ = (1 + ‖s‖) ^ 6 := e.symm
            calc (16 / 5) * (C / 2) * ‖s‖ * (1 + ‖s‖) ^ 5
                = (8 * C / 5) * (‖s‖ * (1 + ‖s‖) ^ 5) := by ring
              _ ≤ (8 * C / 5) * ((1 + ‖s‖) ^ 6) :=
                  mul_le_mul_of_nonneg_left hs6 (by linarith [hCnn])
              _ = (8 * C / 5) * (1 + ‖s‖) ^ 6 := by ring
              _ ≤ (8 * C / 5 + 1) * (1 + ‖s‖) ^ 6 :=
                  mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg h1snn 6)
        _ ≤ Real.exp (K₁ * (1 + ‖s‖) * Real.log (4 + ‖s‖)) *
              Real.exp (4 * (1 + ‖s‖) * Real.log (4 + ‖s‖)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            have e : (8 * C / 5 + 1) * (1 + ‖s‖) ^ 6 =
                (8 * C / 5 + 1) * (1 + ‖s‖) ^ (6:ℝ) := by simp
            rw [e]
            exact hK₁b ‖s‖ (norm_nonneg _)
        _ = Real.exp ((K₁ + 4) * (1 + ‖s‖) * Real.log (4 + ‖s‖)) := by
            rw [← Real.exp_add]
            congr 1
            ring
        _ ≤ Real.exp (K₃ * (1 + ‖s‖) * Real.log (4 + ‖s‖)) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left _ _) h1snn) hLnn)
    · -- 小区：紧盘界
      have hs2 : ‖s‖ ≤ 2 := le_of_not_ge h2
      calc ‖xiFunction s‖ ≤ M₀ := hM₀ s hs2
        _ ≤ M₀ + 1 := by linarith
        _ = (M₀ + 1) * (1 + ‖s‖) ^ (0:ℝ) := by rw [Real.rpow_zero, mul_one]
        _ ≤ Real.exp (K₂ * (1 + ‖s‖) * Real.log (4 + ‖s‖)) :=
            hK₂b ‖s‖ (norm_nonneg _)
        _ ≤ Real.exp (K₃ * (1 + ‖s‖) * Real.log (4 + ‖s‖)) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_right _ _) h1snn) hLnn)
  -- 全平面：左半平面经函数方程归约
  refine ⟨4 * K₃, fun s => ?_⟩
  have h1snn : (0:ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have hLnn : (0:ℝ) ≤ Real.log (4 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
  by_cases hre : 1 / 2 ≤ s.re
  · exact (hAB s hre).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith [hK₃nn] : K₃ ≤ 4 * K₃) h1snn) hLnn))
  · have hre' : 1 / 2 ≤ (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith [le_of_not_ge hre]
    rw [xiFunction_one_sub]
    have h1s : ‖1 - s‖ ≤ 1 + ‖s‖ := by
      calc ‖1 - s‖ ≤ ‖(1 : ℂ)‖ + ‖s‖ := norm_sub_le _ _
        _ = 1 + ‖s‖ := by rw [norm_one]
    have hmono : (1 + ‖1 - s‖) * Real.log (4 + ‖1 - s‖) ≤
        4 * ((1 + ‖s‖) * Real.log (4 + ‖s‖)) := by
      have h1 : (1:ℝ) + ‖1 - s‖ ≤ 2 + ‖s‖ := by linarith
      have h2 : Real.log (4 + ‖1 - s‖) ≤ Real.log (5 + ‖s‖) :=
        Real.log_le_log (by linarith [norm_nonneg (1 - s)]) (by linarith [norm_nonneg s])
      have h3 : Real.log (5 + ‖s‖) ≤ 2 * Real.log (4 + ‖s‖) := by
        have h4 : (5 + ‖s‖) ≤ (4 + ‖s‖) ^ 2 := by nlinarith [norm_nonneg s]
        calc Real.log (5 + ‖s‖) ≤ Real.log ((4 + ‖s‖) ^ 2) :=
              Real.log_le_log (by linarith [norm_nonneg s]) h4
          _ = 2 * Real.log (4 + ‖s‖) := by rw [Real.log_pow]; norm_num
      calc (1 + ‖1 - s‖) * Real.log (4 + ‖1 - s‖)
          ≤ (2 + ‖s‖) * Real.log (5 + ‖s‖) :=
            mul_le_mul h1 h2 (Real.log_nonneg (by linarith [norm_nonneg (1 - s)]))
              (by linarith [norm_nonneg s])
        _ ≤ (2 * (1 + ‖s‖)) * (2 * Real.log (4 + ‖s‖)) :=
            mul_le_mul (by linarith [norm_nonneg s]) h3
              (Real.log_nonneg (by linarith [norm_nonneg s]))
              (by linarith [norm_nonneg s])
        _ = 4 * ((1 + ‖s‖) * Real.log (4 + ‖s‖)) := by ring
    calc ‖xiFunction (1 - s)‖
        ≤ Real.exp (K₃ * (1 + ‖1 - s‖) * Real.log (4 + ‖1 - s‖)) := hAB (1 - s) hre'
      _ ≤ Real.exp (K₃ * (4 * ((1 + ‖s‖) * Real.log (4 + ‖s‖)))) :=
          Real.exp_le_exp.mpr (by
            have h := mul_le_mul_of_nonneg_left hmono hK₃nn
            rw [← mul_assoc] at h
            exact h)
      _ = Real.exp (4 * K₃ * (1 + ‖s‖) * Real.log (4 + ‖s‖)) := by
          congr 1
          ring

/-- 临界带内 ξ 与 ζ 的解析重数相同：`ξ = ((1/2)·s·(s−1)·Gammaℝ)·ζ` 的
前置因子在 `0 < re s < 1` 处解析且非零（`Gammaℝ` 由整函数 `Gammaℝ_inv`
取逆得到解析性）。这是把按 ζ 重数计次的零点级数改写为按 ξ 重数计次的
转换引理。 -/
theorem analyticOrderNatAt_xiFunction_eq_riemannZeta_of_isNontrivialZero {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    analyticOrderNatAt xiFunction s = analyticOrderNatAt riemannZeta s := by
  classical
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at h0; exact (lt_irrefl _ h0).elim
  have hs1 : s ≠ 1 := by
    intro h; rw [h, Complex.one_re] at h1; exact (lt_irrefl _ h1).elim
  set f : ℂ → ℂ := fun z => (1 / 2) * z * (z - 1) * Complex.Gammaℝ z with hfdef
  -- 局部等式：在开的临界带 `{0 < re < 1}` 上 `ξ = f·ζ`
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hev : xiFunction =ᶠ[𝓝 s] f * riemannZeta := by
    refine Filter.eventually_of_mem (hopen.mem_nhds ⟨h0, h1⟩) fun z hz => ?_
    have hz0 : z ≠ 0 := by
      intro h
      have hz' := hz.1
      rw [h, Complex.zero_re] at hz'
      exact (lt_irrefl _ hz').elim
    have hz1 : z ≠ 1 := by
      intro h
      have hz' := hz.2
      rw [h, Complex.one_re] at hz'
      exact (lt_irrefl _ hz').elim
    have hG : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hz.1
    show xiFunction z = (f * riemannZeta) z
    rw [Pi.mul_apply]
    exact xiFunction_eq_classical hz0 hz1 hG
  -- 前置因子 f 在 `s` 处解析（`Gammaℝ = (Gammaℝ_inv)⁻¹`）
  have hGR : AnalyticAt ℂ Complex.Gammaℝ s := by
    have hfinv : (fun s => (Complex.Gammaℝ s)⁻¹)⁻¹ = Complex.Gammaℝ := by
      funext z
      simp
    have h2 := (Complex.differentiable_Gammaℝ_inv.analyticAt s).inv
      (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos h0))
    rw [hfinv] at h2
    exact h2
  have hfan : AnalyticAt ℂ f s := by
    have hconst : AnalyticAt ℂ (fun _ : ℂ => (1 / 2 : ℂ)) s := analyticAt_const
    have hid : AnalyticAt ℂ (fun z : ℂ => z) s := analyticAt_id
    have hsub : AnalyticAt ℂ (fun z : ℂ => z - 1) s := hid.sub analyticAt_const
    exact ((hconst.mul hid).mul hsub).mul hGR
  -- f s ≠ 0
  have hfne : f s ≠ 0 := by
    have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h0
    show (1 / 2 : ℂ) * s * (s - 1) * Complex.Gammaℝ s ≠ 0
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs0)
      (sub_ne_zero_of_ne hs1)) hG
  -- f 的解析重数为 0（值非零）
  have hftop : analyticOrderAt f s ≠ ⊤ := by
    intro htop
    exact hfne ((analyticOrderAt_eq_top.mp htop).self_of_nhds)
  have hford : analyticOrderNatAt f s = 0 := by
    have h0ord : analyticOrderAt f s = 0 := (hfan.analyticOrderAt_eq_zero).mpr hfne
    have hrfl : analyticOrderNatAt f s = (analyticOrderAt f s).toNat := rfl
    rw [hrfl, h0ord]
    rfl
  -- 重数链：`ξ =ᶠ f·ζ` ⇒ 重数相同；乘积重数拆分；f 重数为 0
  have hcongr : analyticOrderAt xiFunction s = analyticOrderAt (f * riemannZeta) s :=
    analyticOrderAt_congr hev
  have hnat : analyticOrderNatAt (f * riemannZeta) s =
      analyticOrderNatAt f s + analyticOrderNatAt riemannZeta s :=
    analyticOrderNatAt_mul hfan
      (ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one s hs1) hftop
      (ZeroFreeRegion.analyticOrderAt_riemannZeta_ne_top_of_ne_one hs1)
  calc analyticOrderNatAt xiFunction s
      = (analyticOrderAt xiFunction s).toNat := rfl
    _ = (analyticOrderAt (f * riemannZeta) s).toNat := by rw [hcongr]
    _ = analyticOrderNatAt (f * riemannZeta) s := rfl
    _ = analyticOrderNatAt f s + analyticOrderNatAt riemannZeta s := hnat
    _ = analyticOrderNatAt riemannZeta s := by rw [hford, zero_add]

end RiemannExplorer
