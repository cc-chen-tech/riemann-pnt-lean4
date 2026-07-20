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

end RiemannExplorer
