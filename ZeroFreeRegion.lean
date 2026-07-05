/-
# Zero-Free Regions for the Riemann Zeta Function

## Overview

This file formalizes the zero-free region for ζ(s), centered around
de la Vallée Poussin's 3-4-1 inequality:

  3·Re(-ζ'/ζ(σ)) + 4·Re(-ζ'/ζ(σ+it)) + Re(-ζ'/ζ(σ+2it)) ≥ 0

This file records verified supporting lemmas and target theorems for the
classical zero-free-region argument. The trigonometric identity and the full
logarithmic-derivative 3-4-1 combination are proved, as is the compact
zero-free strip for each bounded height. The zero-free-region theorems that
need deeper analytic input are recorded as `Prop` target statements in this
checkout.

## Verified and partial results

1. `trig_identity_nonneg` — 3 + 4cos θ + cos 2θ = 2(1+cos θ)² ≥ 0
2. `zeta_no_zeros_on_line_one` — ζ(s) ≠ 0 on Re(s) = 1
3. `log_deriv_zeta_re_series` — -Re(ζ'/ζ(s)) expressed as a Dirichlet series in von Mangoldt Λ
4. `log_deriv_zeta_nonneg_combination` — full 3-4-1 combination
5. `classical_zero_free_region_compact` — compact zero-free region for bounded height
6. `residue_bounds` — 1 < (σ-1)ζ(σ) ≤ σ for σ > 1, confirming residue 1 at s=1
7. `log_deriv_zeta_pos_real` — -Re(ζ'/ζ(σ)) > 0 for real σ > 1
8. `log_deriv_zeta_antitone` — -Re(ζ'/ζ) is decreasing on (1, ∞)

## Unproved target statements

- `classical_zero_free_region` — quantitative σ ≥ 1 - c/log|t|
  (requires zeta-specific growth/log-derivative estimates built from tools
  such as Mathlib's Borel-Carathéodory, Jensen, Phragmén-Lindelöf, and
  Hadamard three-lines theorems)
- `vinogradov_korobov_zero_free_region` — requires exponential sum estimates

## Dependencies

- Mathlib (riemannZeta, Complex analysis, L-series)
- RiemannExplorer
-/

import Mathlib
import RiemannExplorer

open Complex BigOperators Filter Nat Topology MeasureTheory Asymptotics
open scoped ArithmeticFunction LSeries.notation

namespace ZeroFreeRegion

/-- ζ 在 Re(s) = 1 上无零点（Hadamard-de la Vallée Poussin） -/
theorem zeta_no_zeros_on_line_one :
    ∀ s : ℂ, s.re = 1 → riemannZeta s ≠ 0 := by
  -- 这是素数定理证明的核心
  -- Hadamard 和 de la Vallée Poussin (1896) 证明
  -- 直接使用 Mathlib 和 RiemannExplorer 中的已知结果
  exact KnownResults.zeta_no_zeros_on_one_line

/-- 三角恒等式：3 + 4cos θ + cos(2θ) = 2(1 + cos θ)² ≥ 0
    这是 de la Vallée Poussin 零点自由区域证明的核心。 -/
lemma trig_identity_nonneg (θ : ℝ) : 3 + 4 * Real.cos θ + Real.cos (2 * θ) ≥ 0 := by
  have h : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  rw [h]
  have h2 : 3 + 4 * Real.cos θ + (2 * Real.cos θ ^ 2 - 1) = 2 * (1 + Real.cos θ) ^ 2 := by ring
  rw [h2]
  positivity

/-- ζ(s) > 0 对于所有实数 s > 1。
    这直接由Dirichlet级数定义得出。
    对于实数 s > 1，每个项 1/n^s 是正实数，因此级数和为正。 -/
lemma riemannZeta_pos_of_real_gt_one (s : ℝ) (hs : 1 < s) : 0 < (riemannZeta (s : ℂ)).re := by
  -- Mathlib 已有这个引理：riemannZeta_re_pos_of_one_lt
  -- 注意 Mathlib 中的 riemannZeta x 会自动将 x : ℝ 强制转换为 ℂ
  simpa using riemannZeta_re_pos_of_one_lt hs

/-- 对于实数 s > 1，log ζ(s) 可以表示为 von Mangoldt 函数的和。
    这是 de la Vallée Poussin 证明的起点。 -/
lemma log_riemannZeta_dirichlet_series (s : ℝ) (hs : 1 < s) :
    Real.log (riemannZeta (s : ℂ)).re = ∑' p : Nat.Primes, Real.log (1 / (1 - (p : ℝ) ^ (-s))) := by
  -- 1. 欧拉乘积的 exp-log 形式
  have h_euler := riemannZeta_eulerProduct_exp_log (show 1 < (s : ℂ).re by rw [Complex.ofReal_re]; exact_mod_cast hs)
  -- 2. ζ(s) 是正实数
  have h_zeta_pos : 0 < (riemannZeta (s : ℂ)).re := riemannZeta_re_pos_of_one_lt hs
  have h_zeta_im : (riemannZeta (s : ℂ)).im = 0 := riemannZeta_im_eq_zero_of_one_lt hs
  -- 3. 关键等式：每一项的复对数等于实对数
  have h_term (p : Nat.Primes) : -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) = (↑(Real.log (1 / (1 - (p : ℝ) ^ (-s)))) : ℂ) := by
    have hp1 : (p : ℂ) ^ (-(s : ℂ)) = (↑((p : ℝ) ^ (-s)) : ℂ) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast p.prop.pos.ne')]
      rw [Real.rpow_def_of_pos (by exact_mod_cast p.prop.pos)]
      simp [Complex.ofReal_exp, Complex.ofReal_log, Complex.ofReal_mul]
    have hp2 : (1 - (p : ℂ) ^ (-(s : ℂ)) : ℂ) = (↑(1 - (p : ℝ) ^ (-s)) : ℂ) := by
      rw [hp1]
      simp
    rw [hp2]
    have h_pos' : 0 < (1 - (p : ℝ) ^ (-s) : ℝ) := by
      have h_p : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
      have h_ps : 0 < (p : ℝ) ^ (-s) := by
        apply Real.rpow_pos_of_pos
        exact_mod_cast p.prop.pos
      have h_ps_lt : (p : ℝ) ^ (-s) < 1 := by
        rw [Real.rpow_neg (by exact_mod_cast p.prop.pos.le)]
        have h_one_lt : 1 < (p : ℝ) ^ s := by
          apply Real.one_lt_rpow
          · exact_mod_cast p.prop.one_lt
          · linarith
        exact inv_lt_one_of_one_lt₀ h_one_lt
      linarith
    have h3 : Complex.log (↑(1 - (p : ℝ) ^ (-s)) : ℂ) = (↑(Real.log (1 - (p : ℝ) ^ (-s))) : ℂ) := by
      rw [Complex.ofReal_log]
      exact_mod_cast h_pos'.le
    rw [h3]
    have h4 : -(↑(Real.log (1 - (p : ℝ) ^ (-s))) : ℂ) = (↑(-Real.log (1 - (p : ℝ) ^ (-s))) : ℂ) := by simp
    rw [h4]
    have h5 : (-Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) = Real.log (1 / (1 - (p : ℝ) ^ (-s))) := by
      rw [Real.log_div (by positivity) (by positivity)]
      simp
    rw [h5]
  -- 4. 证明级数可和
  have h_sum : Summable (fun p : Nat.Primes ↦ -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))) := by
    have hsum := summable_riemannZetaSummand (show 1 < (s : ℂ).re by rw [Complex.ofReal_re]; exact_mod_cast hs)
    have hsum' := hsum.of_norm
    have hsum_log := hsum'.clog_one_sub.neg.subtype {p | p.Prime}
    simpa using hsum_log
  -- 5. 证明级数的虚部为 0
  have h_sum_im : (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))).im = 0 := by
    rw [im_tsum h_sum]
    have h_zero : ∑' p : Nat.Primes, (-Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))).im = ∑' p : Nat.Primes, (0 : ℝ) := by
      apply tsum_congr
      intro p
      rw [h_term p]
      simp
    rw [h_zero, tsum_zero]
  -- 6. 由 exp(级数) = ζ(s) 取实部得 Real.exp(级数实部) = (ζ(s)).re
  have h_exp_re : Real.exp (∑' p : Nat.Primes, (-Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))).re)
      = (riemannZeta (s : ℂ)).re := by
    have h1 : (Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))))).re
        = Real.exp (∑' p : Nat.Primes, (-Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))).re) := by
      rw [Complex.exp_re]
      have : (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))).re
          = ∑' p : Nat.Primes, (-Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))).re := by
        rw [re_tsum h_sum]
      rw [this]
      simp [h_sum_im]
    have h2 : Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))))
        = (riemannZeta (s : ℂ)) := h_euler
    rw [← h1, h2]
  -- 7. 两边取 Real.log
  have h_log_eq : ∑' p : Nat.Primes, (-Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))).re
      = Real.log (riemannZeta (s : ℂ)).re := by
    rw [← h_exp_re]
    exact (Real.log_exp _).symm
  -- 8. 将 re 移入 tsum，并替换每一项
  have h_eq : (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))).re
      = ∑' p : Nat.Primes, Real.log (1 / (1 - (p : ℝ) ^ (-s))) := by
    rw [re_tsum h_sum]
    apply tsum_congr
    intro p
    rw [h_term p]
    simp
  -- 9. 综合完成证明
  have h_re_tsum : (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))).re
      = ∑' p : Nat.Primes, (-Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))).re := by
    rw [re_tsum h_sum]
  rw [← h_eq]
  linarith [h_re_tsum, h_log_eq]

/-- 辅助引理：n^(-s) 的实部展开。
    对于 n ≠ 0 和 s = σ + it，有 Re(n^(-s)) = n^(-σ) * cos(t * log n) -/
private lemma natCast_cpow_neg_re {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    ((n : ℂ) ^ (-s)).re = (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have h_log : Complex.log (n : ℂ) = (↑(Real.log (n : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_natCast]
    exact (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  have h1 : ((n : ℂ) ^ (-s)).re = (Complex.exp (Complex.log (n : ℂ) * (-s))).re := by
    rw [cpow_def_of_ne_zero hn']
  rw [h1, h_log]
  have h_re : ((↑(Real.log (n : ℝ)) : ℂ) * (-s)).re = -(s.re * Real.log n) := by
    have : (↑(Real.log (n : ℝ)) : ℂ) = ⟨Real.log n, 0⟩ := rfl
    rw [this]
    simp [Complex.mul_re, Complex.neg_re]
    ring
  have h_im : ((↑(Real.log (n : ℝ)) : ℂ) * (-s)).im = -(s.im * Real.log n) := by
    have : (↑(Real.log (n : ℝ)) : ℂ) = ⟨Real.log n, 0⟩ := rfl
    rw [this]
    simp [Complex.mul_im, Complex.neg_im]
    ring
  rw [Complex.exp_re, h_re, h_im]
  congr 1
  · rw [Real.rpow_def_of_pos hn_pos]; ring_nf
  · rw [Real.cos_neg]

/-- 对于 Re(s) > 1，-Re(ζ'(s)/ζ(s)) 可表示为 von Mangoldt 函数的 Dirichlet 级数。
    这是 de la Vallée Poussin 零点自由区域证明的核心公式。

    证明策略：由 Mathlib 的 LSeries_vonMangoldt_eq_deriv_riemannZeta_div 得
    L(↗Λ, s) = -ζ'(s)/ζ(s)，然后展开 L-series 的实部，利用
    n^(-s) = n^(-σ) * (cos(t*log n) - i*sin(t*log n)) 提取实部。 -/
lemma log_deriv_zeta_re_series (s : ℂ) (hs : 1 < s.re) :
    (- deriv riemannZeta s / riemannZeta s).re = ∑' n : ℕ, Λ n * Real.cos (s.im * Real.log n) / (n : ℝ) ^ s.re := by
  have h_lseries := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [← h_lseries]
  have h_sum : LSeriesSummable (↗Λ) s := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  rw [LSeries, Complex.re_tsum h_sum.hasSum.summable]
  apply tsum_congr
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_def₀ (by simp : (↗Λ) 0 = 0)]
    have hn' : n ≠ 0 := hn.ne'
    have h_re := natCast_cpow_neg_re hn' s
    show (↑(Λ n) * (↑n : ℂ) ^ (-s)).re = _
    rw [Complex.re_ofReal_mul, h_re, Real.rpow_neg (Nat.cast_nonneg n)]
    ring

/-- 对于实数 σ > 1，ζ(σ) 的实部等于 Σ 1/(n+1)^σ (实数级数)。
    这里 (n+1)^σ 是实数的 rpow，利用 ofReal_cpow 将复数幂还原为实数幂。 -/
lemma riemannZeta_re_eq_tsum_real (σ : ℝ) (hσ : 1 < σ) :
    (riemannZeta (σ : ℂ)).re = ∑' n : ℕ, 1 / (↑n + 1 : ℝ) ^ σ := by
  have hσ_re : 1 < (↑σ : ℂ).re := by simp [hσ]
  have h_sum : Summable (fun n : ℕ ↦ 1 / (↑n + 1 : ℂ) ^ (↑σ : ℂ)) := by
    have h := (Complex.summable_one_div_nat_cpow (p := (↑σ : ℂ))).mpr hσ_re
    exact ((summable_nat_add_iff (f := fun n => 1 / (↑n : ℂ) ^ (↑σ : ℂ)) 1).mpr h).congr
      (fun n => by push_cast; ring_nf)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hσ_re, Complex.re_tsum h_sum]
  congr 1; ext n
  have h_pos : (0 : ℝ) ≤ (↑n + 1 : ℝ) := by positivity
  have h_cpow : (↑n + 1 : ℂ) ^ (↑σ : ℂ) = ↑((↑n + 1 : ℝ) ^ σ) := by
    have h_cast : (↑n + 1 : ℂ) = (↑(↑n + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [h_cast, ← Complex.ofReal_cpow h_pos σ]
  rw [h_cpow, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]

/-- 对于实数 σ > 1，Σ 1/(n+1)^σ 可求和 (实数)。 -/
lemma summable_one_div_rpow (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ ↦ 1 / (↑n + 1 : ℝ) ^ σ) := by
  have hσ_re : 1 < (↑σ : ℂ).re := by simp [hσ]
  have h_sum : Summable (fun n : ℕ ↦ 1 / (↑n + 1 : ℂ) ^ (↑σ : ℂ)) := by
    have h := (Complex.summable_one_div_nat_cpow (p := (↑σ : ℂ))).mpr hσ_re
    exact ((summable_nat_add_iff (f := fun n => 1 / (↑n : ℂ) ^ (↑σ : ℂ)) 1).mpr h).congr
      (fun n => by push_cast; ring_nf)
  exact (Complex.reCLM.summable h_sum).congr (fun n => by
    have h_pos : (0 : ℝ) ≤ (↑n + 1 : ℝ) := by positivity
    simp only [Complex.reCLM_apply]
    have h_cpow : (↑n + 1 : ℂ) ^ (↑σ : ℂ) = ↑((↑n + 1 : ℝ) ^ σ) := by
      have h_cast : (↑n + 1 : ℂ) = (↑(↑n + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [h_cast, ← Complex.ofReal_cpow h_pos σ]
    rw [h_cpow, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re])

/-- 对于实数 σ > 1，ζ(σ).re > 1。
    从级数 ζ(σ) = 1 + 1/2^σ + ... > 1 推出。 -/
lemma riemannZeta_re_gt_one (σ : ℝ) (hσ : 1 < σ) :
    (riemannZeta (σ : ℂ)).re > 1 := by
  rw [riemannZeta_re_eq_tsum_real σ hσ]
  have h_sum := summable_one_div_rpow σ hσ
  rw [h_sum.tsum_eq_zero_add]
  have h_first : 1 / (↑(0 : ℕ) + 1 : ℝ) ^ σ = 1 := by simp
  rw [h_first]
  have h_shifted : Summable (fun n : ℕ => 1 / (↑(n + 1) + 1 : ℝ) ^ σ) :=
    (summable_nat_add_iff (f := fun n => 1 / (↑n + 1 : ℝ) ^ σ) 1).mpr h_sum
  have h_pos_0 : (0 : ℝ) < 1 / (↑(0 + 1 : ℕ) + 1 : ℝ) ^ σ := by positivity
  linarith [h_shifted.tsum_pos (fun n => by positivity) 0 h_pos_0]

/-- 对于实数 σ > 1，ζ(σ) > 1/(σ-1)。
    这从 Dirichlet 级数 ζ(σ) = Σ 1/n^σ > ∫₁^∞ x^{-σ} dx = 1/(σ-1) 导出。 -/
lemma riemannZeta_gt_one_div_sub (σ : ℝ) (hσ : 1 < σ) :
    (riemannZeta (σ : ℂ)).re > 1 / (σ - 1) := by
  by_cases hσ2 : σ ≥ 2
  · have h1 := riemannZeta_re_gt_one σ hσ
    have h2 : 1 / (σ - 1) ≤ 1 := by
      rw [div_le_one (by linarith : (0:ℝ) < σ - 1)]; linarith
    linarith
  · push Not at hσ2
    have h_eq := ZetaAsymptotics.zeta_limit_aux1 hσ
    rw [riemannZeta_re_eq_tsum_real σ hσ]
    have h_term_le : ZetaAsymptotics.term_tsum σ ≤ 1 - Real.eulerMascheroniConstant := by
      have h_summable_1 := ZetaAsymptotics.term_tsum_one.summable
      have h_le : ∀ n, ZetaAsymptotics.term (n + 1) σ ≤ ZetaAsymptotics.term (n + 1) 1 := by
        intro n
        unfold ZetaAsymptotics.term
        have hab : (↑(n + 1) : ℝ) ≤ ↑(n + 1) + 1 := by linarith
        apply intervalIntegral.integral_mono_on hab
        · exact ZetaAsymptotics.term_welldef (by omega : 0 < n + 1) (by linarith : (0:ℝ) < σ)
        · exact ZetaAsymptotics.term_welldef (by omega : 0 < n + 1) zero_lt_one
        · intro x hx
          have hx_lb := hx.1
          have hx_pos : (0 : ℝ) < x := by
            have : (0 : ℝ) < (↑(n + 1) : ℝ) := by positivity
            linarith
          have hx_ge_one : (1 : ℝ) ≤ x := by
            have : (1 : ℝ) ≤ (↑(n + 1) : ℝ) := by norm_cast; omega
            linarith
          apply div_le_div_of_nonneg_left
          · linarith
          · exact Real.rpow_pos_of_pos hx_pos _
          · exact Real.rpow_le_rpow_of_exponent_le hx_ge_one (by linarith)
      have h_summable_σ : Summable (fun n => ZetaAsymptotics.term (n + 1) σ) :=
        Summable.of_nonneg_of_le (fun n => ZetaAsymptotics.term_nonneg _ _) h_le h_summable_1
      calc ZetaAsymptotics.term_tsum σ
          = ∑' n, ZetaAsymptotics.term (n + 1) σ := rfl
        _ ≤ ∑' n, ZetaAsymptotics.term (n + 1) 1 :=
            h_summable_σ.tsum_le_tsum h_le h_summable_1
        _ = 1 - Real.eulerMascheroniConstant := ZetaAsymptotics.term_tsum_one.tsum_eq
    have hγ := Real.one_half_lt_eulerMascheroniConstant
    have h1 : σ * ZetaAsymptotics.term_tsum σ ≤ σ * (1 - Real.eulerMascheroniConstant) :=
      mul_le_mul_of_nonneg_left h_term_le (by linarith)
    have h2 : σ * (1 - Real.eulerMascheroniConstant) < 1 := by nlinarith
    linarith

/-- 对于实数 σ > 1，ζ(σ) ≤ σ/(σ-1)。
    与 riemannZeta_gt_one_div_sub 给出的下界 1/(σ-1) 互补。 -/
lemma riemannZeta_re_le_sigma_div_sub (σ : ℝ) (hσ : 1 < σ) :
    (riemannZeta (σ : ℂ)).re ≤ σ / (σ - 1) := by
  rw [riemannZeta_re_eq_tsum_real σ hσ]
  have h_eq := ZetaAsymptotics.zeta_limit_aux1 hσ
  have h_tsum_nonneg : 0 ≤ ZetaAsymptotics.term_tsum σ :=
    tsum_nonneg (fun n => ZetaAsymptotics.term_nonneg (n + 1) σ)
  have h_mul_nonneg : 0 ≤ σ * ZetaAsymptotics.term_tsum σ :=
    mul_nonneg (by linarith) h_tsum_nonneg
  have h_le : (∑' n : ℕ, 1 / (↑n + 1 : ℝ) ^ σ) ≤ 1 / (σ - 1) + 1 := by linarith
  have h_rw : σ / (σ - 1) = 1 / (σ - 1) + 1 := by
    have hsub : (σ - 1 : ℝ) ≠ 0 := by linarith
    field_simp; ring
  linarith

/-- (σ-1)*ζ(σ) 有界：1 < (σ-1)*ζ(σ) ≤ σ。
    这证实了 ζ 在 s=1 处的留数为 1。 -/
lemma residue_bounds (σ : ℝ) (hσ : 1 < σ) :
    1 < (σ - 1) * (riemannZeta (σ : ℂ)).re ∧
    (σ - 1) * (riemannZeta (σ : ℂ)).re ≤ σ := by
  have hsub : (0 : ℝ) < σ - 1 := by linarith
  constructor
  · have h := riemannZeta_gt_one_div_sub σ hσ
    calc 1 = (σ - 1) * (1 / (σ - 1)) := by field_simp
      _ < (σ - 1) * (riemannZeta (σ : ℂ)).re :=
        mul_lt_mul_of_pos_left h hsub
  · have h := riemannZeta_re_le_sigma_div_sub σ hσ
    calc (σ - 1) * (riemannZeta (σ : ℂ)).re
        ≤ (σ - 1) * (σ / (σ - 1)) := mul_le_mul_of_nonneg_left h (le_of_lt hsub)
      _ = σ := by field_simp

/-- 对于实数 σ > 1，-ζ'/ζ(σ) 的实部严格正，
    因为它等于 Σ Λ(n)/n^σ ≥ Λ(2)/2^σ = log(2)/2^σ > 0。 -/
lemma log_deriv_zeta_pos_real (σ : ℝ) (hσ : 1 < σ) :
    0 < (- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
  have h_series := log_deriv_zeta_re_series (σ : ℂ) (by simp [hσ] : 1 < (↑σ : ℂ).re)
  rw [h_series]
  simp only [Complex.ofReal_im, zero_mul, Real.cos_zero, mul_one]
  have h_nonneg : ∀ n : ℕ, 0 ≤ Λ n / (↑n : ℝ) ^ σ := fun n ↦ by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ArithmeticFunction.vonMangoldt]
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  have h_term2 : (0 : ℝ) < Λ 2 / (2 : ℝ) ^ σ := by
    apply _root_.div_pos
    · rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      exact Real.log_pos (by norm_num : (1:ℝ) < 2)
    · exact Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) σ
  have h_summable : Summable (fun n : ℕ ↦ Λ n / (↑n : ℝ) ^ σ) := by
    have h_re : 1 < (↑σ : ℂ).re := by simp [hσ]
    have h_ls := ArithmeticFunction.LSeriesSummable_vonMangoldt h_re
    have h_map := Complex.reCLM.summable h_ls
    exact h_map.congr (fun n ↦ by
      simp only [Complex.reCLM_apply, LSeries.term]
      split_ifs with hn
      · subst hn; simp
      · rw [div_eq_mul_inv, ← cpow_neg, Complex.re_ofReal_mul,
            natCast_cpow_neg_re hn, Real.rpow_neg (Nat.cast_nonneg n)]
        simp only [Complex.ofReal_im, Complex.ofReal_re, zero_mul, Real.cos_zero, mul_one,
          div_eq_mul_inv])
  exact h_summable.tsum_pos h_nonneg 2 h_term2

/-- 对于实数 σ > 1，-ζ'/ζ(σ) 的 Dirichlet 级数表示。
    这是 log_deriv_zeta_re_series 对纯实数参数的特化。 -/
lemma log_deriv_zeta_real_eq_series (σ : ℝ) (hσ : 1 < σ) :
    (- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re =
    ∑' n : ℕ, Λ n / (n : ℝ) ^ σ := by
  have h := log_deriv_zeta_re_series (σ : ℂ) (by simp [hσ] : 1 < (↑σ : ℂ).re)
  simp only [Complex.ofReal_im, Complex.ofReal_re, zero_mul, Real.cos_zero, mul_one] at h
  exact h

/-- Norm of one von Mangoldt L-series term in the half-plane expression.

This removes the oscillatory factor from `n^{-s}`: the norm only sees
`n^{-Re(s)}`. It is the termwise input for bounding the vertical logarithmic
derivative by the real-axis one. -/
lemma norm_LSeries_vonMangoldt_term_eq_real (s : ℂ) (n : ℕ) :
    ‖LSeries.term (↗Λ) s n‖ = Λ n / (n : ℝ) ^ s.re := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term, ArithmeticFunction.vonMangoldt]
  · rw [LSeries.term_def₀ (by simp : (↗Λ) 0 = 0)]
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    rw [norm_mul]
    have h_cast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
    rw [h_cast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos (-s)]
    simp only [neg_re]
    have h_normΛ : ‖(↑(Λ n) : ℂ)‖ = Λ n := by
      simp [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [h_normΛ]
    rw [Real.rpow_neg (le_of_lt hn_pos)]
    ring

/-- In `Re(s) > 1`, the von Mangoldt L-series is dominated by the same
Dirichlet series on the real axis.

This is just the triangle inequality for absolutely convergent L-series,
together with `norm_LSeries_vonMangoldt_term_eq_real`. -/
lemma norm_LSeries_vonMangoldt_le_real_series (s : ℂ) (hs : 1 < s.re) :
    ‖LSeries (↗Λ) s‖ ≤ ∑' n : ℕ, Λ n / (n : ℝ) ^ s.re := by
  have h_ls : LSeriesSummable (↗Λ) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have h_norm_summable :
      Summable (fun n : ℕ => ‖LSeries.term (↗Λ) s n‖) :=
    summable_norm_iff.mpr h_ls
  calc
    ‖LSeries (↗Λ) s‖ = ‖∑' n : ℕ, LSeries.term (↗Λ) s n‖ := by rfl
    _ ≤ ∑' n : ℕ, ‖LSeries.term (↗Λ) s n‖ :=
      norm_tsum_le_tsum_norm h_norm_summable
    _ = ∑' n : ℕ, Λ n / (n : ℝ) ^ s.re := by
      apply tsum_congr
      intro n
      exact norm_LSeries_vonMangoldt_term_eq_real s n

/-- For `Re(s) > 1`, the logarithmic derivative on the vertical line is
bounded by the real-axis logarithmic derivative at the same real part.

This is the Dirichlet-series triangle inequality for von Mangoldt's series:
`‖ζ'/ζ(s)‖ ≤ -Re(ζ'/ζ(Re(s)))`. It is a useful zeta-specific replacement for
one of the generic vertical-strip estimates in the quantitative zero-free
region chain, valid in the half-plane of absolute convergence. -/
lemma norm_logDeriv_riemannZeta_le_real_neg_deriv_div (s : ℂ) (hs : 1 < s.re) :
    ‖logDeriv riemannZeta s‖ ≤
      (-deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)).re := by
  have h_lseries := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have h_real := log_deriv_zeta_real_eq_series s.re hs
  rw [h_real]
  calc
    ‖logDeriv riemannZeta s‖ = ‖LSeries (↗Λ) s‖ := by
      rw [h_lseries]
      change ‖deriv riemannZeta s / riemannZeta s‖ =
        ‖-deriv riemannZeta s / riemannZeta s‖
      rw [neg_div, norm_neg]
    _ ≤ ∑' n : ℕ, Λ n / (n : ℝ) ^ s.re :=
      norm_LSeries_vonMangoldt_le_real_series s hs

/-- -ζ'/ζ(σ) 关于 σ 单调递减：若 σ₁ ≤ σ₂ 且 1 < σ₁，
    则 -Re(ζ'/ζ(σ₂)) ≤ -Re(ζ'/ζ(σ₁))。
    由 Dirichlet 级数逐项递减得出。 -/
lemma log_deriv_zeta_antitone {σ₁ σ₂ : ℝ} (hσ₁ : 1 < σ₁) (hσ₂ : σ₁ ≤ σ₂) :
    (- deriv riemannZeta (σ₂ : ℂ) / riemannZeta (σ₂ : ℂ)).re ≤
    (- deriv riemannZeta (σ₁ : ℂ) / riemannZeta (σ₁ : ℂ)).re := by
  rw [log_deriv_zeta_real_eq_series σ₁ hσ₁,
      log_deriv_zeta_real_eq_series σ₂ (lt_of_lt_of_le hσ₁ hσ₂)]
  have h_pointwise : ∀ n : ℕ, Λ n / (↑n : ℝ) ^ σ₂ ≤ Λ n / (↑n : ℝ) ^ σ₁ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ArithmeticFunction.vonMangoldt]
    · apply div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
      · exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) σ₁
      · exact Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast hn : (1 : ℝ) ≤ ↑n) hσ₂
  have h_summable : ∀ σ : ℝ, 1 < σ → Summable (fun n : ℕ => Λ n / (↑n : ℝ) ^ σ) := by
    intro σ hσ
    have h_re : 1 < (↑σ : ℂ).re := by simp [hσ]
    have h_ls := ArithmeticFunction.LSeriesSummable_vonMangoldt h_re
    exact (Complex.reCLM.summable h_ls).congr (fun n => by
      simp only [Complex.reCLM_apply, LSeries.term]
      split_ifs with hn
      · subst hn; simp [ArithmeticFunction.vonMangoldt]
      · rw [div_eq_mul_inv, ← cpow_neg, Complex.re_ofReal_mul,
            natCast_cpow_neg_re hn, Real.rpow_neg (Nat.cast_nonneg n)]
        simp only [Complex.ofReal_im, Complex.ofReal_re, zero_mul, Real.cos_zero, mul_one,
          div_eq_mul_inv])
  exact (h_summable σ₂ (lt_of_lt_of_le hσ₁ hσ₂)).tsum_le_tsum h_pointwise (h_summable σ₁ hσ₁)

/-- Fixed-margin vertical logarithmic bound for the zeta logarithmic derivative.

For every `ε > 0`, the absolute-convergence half-plane
`1 + ε ≤ Re(s)` has a constant `C` such that
`‖logDeriv ζ(s)‖ ≤ C log(|Im(s)| + 3)`. This is a genuine high-line bound
available from the von Mangoldt L-series triangle inequality and real-axis
monotonicity. It deliberately stays a fixed distance from `Re(s)=1`; the
quantitative zero-free region still needs the missing boundary-strip estimate
with `1 ≤ Re(s) ≤ 2`. -/
lemma exists_norm_logDeriv_riemannZeta_le_log_abs_im_add_three_of_one_add_le_re
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 + ε ≤ z.re →
      ‖logDeriv riemannZeta z‖ ≤ C * Real.log (|z.im| + 3) := by
  let σ₀ : ℝ := 1 + ε
  let K : ℝ := (-deriv riemannZeta (σ₀ : ℂ) / riemannZeta (σ₀ : ℂ)).re
  let log3 : ℝ := Real.log (3 : ℝ)
  have hσ₀ : 1 < σ₀ := by
    dsimp [σ₀]
    linarith
  have hK_pos : 0 < K := by
    dsimp [K]
    exact log_deriv_zeta_pos_real σ₀ hσ₀
  have hlog3_pos : 0 < log3 := by
    dsimp [log3]
    exact Real.log_pos (by norm_num : (1 : ℝ) < 3)
  refine ⟨K / log3, div_nonneg hK_pos.le hlog3_pos.le, ?_⟩
  intro z hz
  have hz_gt : 1 < z.re := lt_of_lt_of_le hσ₀ hz
  have hlog_le : log3 ≤ Real.log (|z.im| + 3) := by
    dsimp [log3]
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 3)
    nlinarith [abs_nonneg z.im]
  have hK_eq : (K / log3) * log3 = K := by
    exact div_mul_cancel₀ K (ne_of_gt hlog3_pos)
  calc
    ‖logDeriv riemannZeta z‖
        ≤ (-deriv riemannZeta (z.re : ℂ) / riemannZeta (z.re : ℂ)).re :=
          norm_logDeriv_riemannZeta_le_real_neg_deriv_div z hz_gt
    _ ≤ K := by
          dsimp [K, σ₀]
          exact log_deriv_zeta_antitone hσ₀ hz
    _ = (K / log3) * log3 := hK_eq.symm
    _ ≤ (K / log3) * Real.log (|z.im| + 3) :=
          mul_le_mul_of_nonneg_left hlog_le (div_nonneg hK_pos.le hlog3_pos.le)

/-- Signed fixed-margin vertical logarithmic bound for the zeta logarithmic
derivative, in the `-logDeriv ζ` convention used by 3-4-1. -/
lemma exists_norm_neg_logDeriv_riemannZeta_le_log_abs_im_add_three_of_one_add_le_re
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 + ε ≤ z.re →
      ‖-logDeriv riemannZeta z‖ ≤ C * Real.log (|z.im| + 3) := by
  rcases exists_norm_logDeriv_riemannZeta_le_log_abs_im_add_three_of_one_add_le_re
      hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro z hz
  calc
    ‖-logDeriv riemannZeta z‖ = ‖logDeriv riemannZeta z‖ := norm_neg _
    _ ≤ C * Real.log (|z.im| + 3) := hbound z hz

/-- Coordinate form of
`exists_norm_logDeriv_riemannZeta_le_log_abs_im_add_three_of_one_add_le_re`
on vertical lines `σ + it`. -/
lemma exists_norm_logDeriv_riemannZeta_sigma_it_le_log_abs_add_three_of_one_add_le
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 + ε ≤ σ →
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
        C * Real.log (|t| + 3) := by
  rcases exists_norm_logDeriv_riemannZeta_le_log_abs_im_add_three_of_one_add_le_re
      hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro σ t hσ
  simpa using hbound ((σ : ℂ) + I * t) (by simpa using hσ)

/-- Signed coordinate form of the fixed-margin vertical logarithmic bound on
points `σ + it`. -/
lemma exists_norm_neg_logDeriv_riemannZeta_sigma_it_le_log_abs_add_three_of_one_add_le
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 + ε ≤ σ →
      ‖-logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
        C * Real.log (|t| + 3) := by
  rcases exists_norm_neg_logDeriv_riemannZeta_le_log_abs_im_add_three_of_one_add_le_re
      hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro σ t hσ
  simpa using hbound ((σ : ℂ) + I * t) (by simpa using hσ)

/-- Elementary log comparison used to move from the point `σ + 2it` back to
the same height scale `log(|t|+3)`. -/
lemma log_abs_two_mul_add_three_le_two_log_abs_add_three (t : ℝ) :
    Real.log (|2 * t| + 3) ≤ 2 * Real.log (|t| + 3) := by
  have ht_nonneg : 0 ≤ |t| := abs_nonneg t
  have hleft_pos : 0 < |2 * t| + 3 := by
    nlinarith [abs_nonneg (2 * t)]
  have hbase_pos : 0 < |t| + 3 := by
    nlinarith
  have h_abs_two : |2 * t| = 2 * |t| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hle : |2 * t| + 3 ≤ (|t| + 3) ^ 2 := by
    rw [h_abs_two]
    nlinarith [sq_nonneg |t|]
  have hlog_le : Real.log (|2 * t| + 3) ≤ Real.log ((|t| + 3) ^ 2) :=
    Real.log_le_log hleft_pos hle
  have hlog_sq : Real.log ((|t| + 3) ^ 2) = 2 * Real.log (|t| + 3) := by
    rw [sq, Real.log_mul (ne_of_gt hbase_pos) (ne_of_gt hbase_pos)]
    ring
  simpa [hlog_sq] using hlog_le

/-- Fixed-margin `σ + 2it` norm bound for the zeta logarithmic derivative.

This is the shifted third point used by the 3-4-1 combination, but still under
the fixed-margin hypothesis `1+ε ≤ σ`. -/
lemma exists_norm_logDeriv_riemannZeta_sigma_two_it_le_log_abs_add_three_of_one_add_le
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 + ε ≤ σ →
      ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤
        C * Real.log (|t| + 3) := by
  rcases exists_norm_logDeriv_riemannZeta_le_log_abs_im_add_three_of_one_add_le_re
      hε with ⟨C, hC, hbound⟩
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro σ t hσ
  have hmain :=
    hbound ((σ : ℂ) + 2 * I * t) (by simpa using hσ)
  calc
    ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖
        ≤ C * Real.log (|2 * t| + 3) := by
          simpa using hmain
    _ ≤ C * (2 * Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_left
            (log_abs_two_mul_add_three_le_two_log_abs_add_three t) hC
    _ = (2 * C) * Real.log (|t| + 3) := by ring

/-- Signed fixed-margin `σ + 2it` norm bound for the zeta logarithmic
derivative in the `-logDeriv ζ` convention. -/
lemma exists_norm_neg_logDeriv_riemannZeta_sigma_two_it_le_log_abs_add_three_of_one_add_le
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 + ε ≤ σ →
      ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ ≤
        C * Real.log (|t| + 3) := by
  rcases exists_norm_logDeriv_riemannZeta_sigma_two_it_le_log_abs_add_three_of_one_add_le
      hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro σ t hσ
  calc
    ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖
        = ‖logDeriv riemannZeta ((σ : ℂ) + 2 * I * t)‖ := norm_neg _
    _ ≤ C * Real.log (|t| + 3) := hbound σ t hσ

/-- **de la Vallée Poussin 三角组合的非负性**

    对于 σ > 1 和实数 t，有

    3*(-Re ζ'(σ)/ζ(σ)) + 4*(-Re ζ'(σ+it)/ζ(σ+it)) + (-Re ζ'(σ+2it)/ζ(σ+2it)) ≥ 0

    这是经典零点自由区域证明的核心不等式。

    证明策略：由 log_deriv_zeta_re_series 展开三个级数，
    组合为 ∑ Λ(n)/n^σ * (3 + 4cos(t log n) + cos(2t log n))，
    由 trig_identity_nonneg 每项非负。 -/
lemma log_deriv_zeta_nonneg_combination (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    3 * (- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
    + 4 * (- deriv riemannZeta ((σ : ℂ) + I * t) / riemannZeta ((σ : ℂ) + I * t)).re
    + (- deriv riemannZeta ((σ : ℂ) + 2 * I * t) / riemannZeta ((σ : ℂ) + 2 * I * t)).re ≥ 0 := by
  have hσ_re1 : 1 < ((σ : ℂ)).re := by simp [hσ]
  have hσ_re2 : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ]
  have hσ_re3 : 1 < ((σ : ℂ) + 2 * I * (t : ℂ)).re := by simp [hσ]
  rw [log_deriv_zeta_re_series _ hσ_re1, log_deriv_zeta_re_series _ hσ_re2,
    log_deriv_zeta_re_series _ hσ_re3]
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im,
    Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, one_mul, mul_zero, sub_zero, add_zero, zero_add, mul_one]
  -- 合并级数并逐项验证非负性
  -- 核心论证：∑ Λ(n)/n^σ * (3 + 4cos(t log n) + cos(2t log n)) ≥ 0
  -- 由 trig_identity_nonneg 知每项非负
  -- 从 LSeriesSummable 推出实部级数可和
  have h_re_summable : ∀ (s : ℂ), 1 < s.re →
      Summable (fun n : ℕ ↦ Λ n * Real.cos (s.im * Real.log ↑n) / (↑n : ℝ) ^ s.re) := by
    intro s hs
    have h_ls := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
    have h_map := Complex.reCLM.summable h_ls
    exact h_map.congr (fun n ↦ by
      simp only [Complex.reCLM_apply, LSeries.term]
      split_ifs with hn
      · subst hn; simp [ArithmeticFunction.vonMangoldt]
      · rw [div_eq_mul_inv, ← cpow_neg, Complex.re_ofReal_mul,
            natCast_cpow_neg_re hn, Real.rpow_neg (Nat.cast_nonneg n)]
        ring)
  have hs1 := h_re_summable _ hσ_re1
  have hs2 := h_re_summable _ hσ_re2
  have hs3 := h_re_summable _ hσ_re3
  have h1c : Summable (fun n : ℕ ↦ Λ n * Real.cos 0 / (↑n : ℝ) ^ σ) := by
    simpa using hs1
  have h1' : Summable (fun n : ℕ ↦ Λ n / (↑n : ℝ) ^ σ) := by
    simpa using hs1
  have h2' : Summable (fun n : ℕ ↦ Λ n * Real.cos (t * Real.log ↑n) / (↑n : ℝ) ^ σ) := by
    simpa using hs2
  have h3' : Summable (fun n : ℕ ↦ Λ n * Real.cos (2 * t * Real.log ↑n) / (↑n : ℝ) ^ σ) := by
    simpa [mul_assoc] using hs3
  -- Combine the three series into one
  have h_sum : Summable (fun n : ℕ ↦
    Λ n * (3 + 4 * Real.cos (t * Real.log ↑n) + Real.cos (2 * t * Real.log ↑n)) / (↑n : ℝ) ^ σ) := by
    refine ((h1'.mul_left 3).add ((h2'.mul_left 4).add h3')).congr ?_
    intro n
    ring
  have h_lhs :
      3 * (∑' n : ℕ, Λ n * Real.cos 0 / (↑n : ℝ) ^ σ)
        + 4 * (∑' n : ℕ, Λ n * Real.cos (t * Real.log ↑n) / (↑n : ℝ) ^ σ)
        + (∑' n : ℕ, Λ n * Real.cos (2 * t * Real.log ↑n) / (↑n : ℝ) ^ σ)
      =
      ∑' n : ℕ, Λ n * (3 + 4 * Real.cos (t * Real.log ↑n)
        + Real.cos (2 * t * Real.log ↑n)) / (↑n : ℝ) ^ σ := by
    have hsum0 := h1c.mul_left 3
    have hsum1 := h2'.mul_left 4
    have hsum2 := h3'
    rw [← tsum_mul_left, ← tsum_mul_left, ← hsum0.tsum_add hsum1,
      ← (hsum0.add hsum1).tsum_add hsum2]
    apply tsum_congr
    intro n
    simp [Real.cos_zero]
    ring
  rw [h_lhs]
  exact tsum_nonneg (fun n ↦ by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ArithmeticFunction.vonMangoldt]
    · have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      have hden : 0 ≤ (n : ℝ) ^ σ :=
        (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) σ).le
      have htrig : 0 ≤ 3 + 4 * Real.cos (t * Real.log (n : ℝ))
          + Real.cos (2 * t * Real.log (n : ℝ)) := by
        simpa [mul_assoc] using trig_identity_nonneg (t * Real.log (n : ℝ))
      exact div_nonneg (mul_nonneg hΛ htrig) hden)

private lemma finset_summable_sum_real {ι : Type*}
    (S : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ S, Summable (f i)) :
    Summable (fun n : ℕ => ∑ i ∈ S, f i n) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | insert a S ha ih =>
      have hfa : Summable (f a) := hf a (Finset.mem_insert_self a S)
      have hfS : ∀ i ∈ S, Summable (f i) := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have hsumS : Summable (fun n : ℕ => ∑ i ∈ S, f i n) := ih hfS
      refine (hfa.add hsumS).congr ?_
      intro n
      simp [ha]

private lemma finset_sum_tsum_eq_tsum_sum_real {ι : Type*}
    (S : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ S, Summable (f i)) :
    (∑ i ∈ S, ∑' n : ℕ, f i n) =
      ∑' n : ℕ, ∑ i ∈ S, f i n := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | insert a S ha ih =>
      have hfa : Summable (f a) := hf a (Finset.mem_insert_self a S)
      have hfS : ∀ i ∈ S, Summable (f i) := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have hsumS : Summable (fun n : ℕ => ∑ i ∈ S, f i n) :=
        finset_summable_sum_real S f hfS
      have hih := ih hfS
      calc
        (∑ i ∈ insert a S, ∑' n : ℕ, f i n)
            = (∑' n : ℕ, f a n) + ∑ i ∈ S, ∑' n : ℕ, f i n := by
                simp [ha]
        _ = (∑' n : ℕ, f a n) + ∑' n : ℕ, ∑ i ∈ S, f i n := by
                rw [hih]
        _ = ∑' n : ℕ, (f a n + ∑ i ∈ S, f i n) := by
                rw [← hfa.tsum_add hsumS]
        _ = ∑' n : ℕ, ∑ i ∈ insert a S, f i n := by
                apply tsum_congr
                intro n
                simp [ha]

/-! ### Finite trigonometric-detector skeleton

The following lemmas isolate the part of the de la Vallée Poussin/Heath-Brown
method that only uses nonnegativity of a finite trigonometric polynomial.  The
analytic identity `hseries` is deliberately explicit: proving it automatically
for large detector polynomials is a separate finite-sum/Dirichlet-series
exchange step.
-/

/-- Finite logarithmic-derivative combinations can be expanded into one
von Mangoldt Dirichlet series weighted by the corresponding finite cosine
polynomial. -/
lemma log_deriv_zeta_finset_series_identity
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ) (S : Finset ℕ) (a : ℕ → ℝ) :
      (∑ k ∈ S, a k *
        (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
          riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re)
        =
      ∑' n : ℕ,
        Λ n *
          (∑ k ∈ S, a k * Real.cos ((k : ℝ) * (t * Real.log (n : ℝ)))) /
            (n : ℝ) ^ σ := by
  classical
  let term : ℕ → ℕ → ℝ :=
    fun k n =>
      Λ n * Real.cos ((k : ℝ) * (t * Real.log (n : ℝ))) / (n : ℝ) ^ σ
  have h_re_summable : ∀ (s : ℂ), 1 < s.re →
      Summable (fun n : ℕ ↦ Λ n * Real.cos (s.im * Real.log ↑n) / (↑n : ℝ) ^ s.re) := by
    intro s hs
    have h_ls := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
    have h_map := Complex.reCLM.summable h_ls
    exact h_map.congr (fun n ↦ by
      simp only [Complex.reCLM_apply, LSeries.term]
      split_ifs with hn
      · subst hn; simp [ArithmeticFunction.vonMangoldt]
      · rw [div_eq_mul_inv, ← cpow_neg, Complex.re_ofReal_mul,
            natCast_cpow_neg_re hn, Real.rpow_neg (Nat.cast_nonneg n)]
        ring)
  have hterm_summable : ∀ k : ℕ, Summable (term k) := by
    intro k
    have hs : 1 < (((σ : ℂ) + (k : ℂ) * I * t)).re := by
      simp [hσ]
    have h := h_re_summable (((σ : ℂ) + (k : ℂ) * I * t)) hs
    simpa [term, mul_assoc] using h
  have hweighted : ∀ k ∈ S, Summable (fun n : ℕ => a k * term k n) := by
    intro k _hk
    exact (hterm_summable k).mul_left (a k)
  have hseries : ∀ k ∈ S,
      (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
          riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re =
        ∑' n : ℕ, term k n := by
    intro k _hk
    have hs : 1 < (((σ : ℂ) + (k : ℂ) * I * t)).re := by
      simp [hσ]
    have h := log_deriv_zeta_re_series (((σ : ℂ) + (k : ℂ) * I * t)) hs
    simpa [term, mul_assoc] using h
  calc
    (∑ k ∈ S, a k *
        (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
          riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re)
        = ∑ k ∈ S, a k * (∑' n : ℕ, term k n) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [hseries k hk]
    _ = ∑ k ∈ S, ∑' n : ℕ, a k * term k n := by
            apply Finset.sum_congr rfl
            intro k _hk
            rw [tsum_mul_left]
    _ = ∑' n : ℕ, ∑ k ∈ S, a k * term k n :=
            finset_sum_tsum_eq_tsum_sum_real S (fun k n => a k * term k n) hweighted
    _ =
      ∑' n : ℕ,
        Λ n *
          (∑ k ∈ S, a k * Real.cos ((k : ℝ) * (t * Real.log (n : ℝ)))) /
            (n : ℝ) ^ σ := by
            apply tsum_congr
            intro n
            dsimp [term]
            rw [Finset.mul_sum, Finset.sum_div]
            apply Finset.sum_congr rfl
            intro k _hk
            ring

/-- General finite trigonometric detector: once a finite logarithmic-derivative
combination is identified with a von Mangoldt Dirichlet series weighted by a
nonnegative trigonometric polynomial, the combination is nonnegative. -/
lemma log_deriv_zeta_nonneg_finset_combination
    (σ : ℝ) (_hσ : 1 < σ) (t : ℝ) (S : Finset ℕ) (a : ℕ → ℝ)
    (hseries :
      (∑ k ∈ S, a k *
        (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
          riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re)
        =
      ∑' n : ℕ,
        Λ n *
          (∑ k ∈ S, a k * Real.cos ((k : ℝ) * (t * Real.log (n : ℝ)))) /
            (n : ℝ) ^ σ)
    (hpoly : ∀ θ : ℝ, 0 ≤ ∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ)) :
    0 ≤
      ∑ k ∈ S, a k *
        (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
          riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re := by
  rw [hseries]
  exact tsum_nonneg (fun n ↦ by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ArithmeticFunction.vonMangoldt]
    · have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      have htrig : 0 ≤
          ∑ k ∈ S, a k * Real.cos ((k : ℝ) * (t * Real.log (n : ℝ))) :=
        hpoly (t * Real.log (n : ℝ))
      have hden : 0 ≤ (n : ℝ) ^ σ :=
        (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) σ).le
      exact div_nonneg (mul_nonneg hΛ htrig) hden)

/-- Isolate one term from a nonnegative finite weighted sum.  This is the
pure algebraic step used to turn a finite detector nonnegativity statement into
a lower bound for one selected logarithmic-derivative term. -/
lemma finset_weighted_nonneg_term_lower_bound
    (S : Finset ℕ) (a x : ℕ → ℝ) {m : ℕ}
    (hm : m ∈ S) (ha : 0 < a m)
    (hnonneg : 0 ≤ ∑ k ∈ S, a k * x k) :
    x m ≥ - (∑ k ∈ S.erase m, a k * x k) / a m := by
  have hsum :
      a m * x m + ∑ k ∈ S.erase m, a k * x k =
        ∑ k ∈ S, a k * x k := by
    exact Finset.add_sum_erase S (fun k => a k * x k) hm
  have hnonneg' : 0 ≤ a m * x m + ∑ k ∈ S.erase m, a k * x k := by
    simpa [hsum] using hnonneg
  have hmul : -(∑ k ∈ S.erase m, a k * x k) ≤ a m * x m := by
    linarith
  exact (div_le_iff₀ ha).mpr (by simpa [mul_comm] using hmul)

/-- Lower bound for a selected shifted logarithmic-derivative term from any
nonnegative finite trigonometric detector. -/
lemma log_deriv_zeta_term_lower_bound_of_finset_detector
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ) (S : Finset ℕ) (a : ℕ → ℝ) {m : ℕ}
    (hm : m ∈ S) (ha : 0 < a m)
    (hpoly : ∀ θ : ℝ, 0 ≤ ∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ)) :
    (-deriv riemannZeta ((σ : ℂ) + (m : ℂ) * I * t) /
        riemannZeta ((σ : ℂ) + (m : ℂ) * I * t)).re ≥
      - (∑ k ∈ S.erase m, a k *
          (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
            riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re) / a m := by
  let x : ℕ → ℝ := fun k =>
    (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
      riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re
  change x m ≥ - (∑ k ∈ S.erase m, a k * x k) / a m
  exact finset_weighted_nonneg_term_lower_bound S a x hm ha
    (log_deriv_zeta_nonneg_finset_combination σ hσ t S a
      (log_deriv_zeta_finset_series_identity σ hσ t S a) hpoly)

/-- List-indexed wrapper for `log_deriv_zeta_nonneg_finset_combination`. -/
lemma log_deriv_zeta_nonneg_list_combination
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ) (ks : List ℕ) (a : ℕ → ℝ)
    (hseries :
      (∑ k ∈ ks.toFinset, a k *
        (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
          riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re)
        =
      ∑' n : ℕ,
        Λ n *
          (∑ k ∈ ks.toFinset, a k * Real.cos ((k : ℝ) * (t * Real.log (n : ℝ)))) /
            (n : ℝ) ^ σ)
    (hpoly : ∀ θ : ℝ, 0 ≤ ∑ k ∈ ks.toFinset, a k * Real.cos ((k : ℝ) * θ)) :
    0 ≤
      ∑ k ∈ ks.toFinset, a k *
        (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
          riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re :=
  log_deriv_zeta_nonneg_finset_combination σ hσ t ks.toFinset a hseries hpoly

/-- Automatic finite trigonometric detector: the finite
logarithmic-derivative combination is nonnegative once the corresponding
finite cosine polynomial is pointwise nonnegative. -/
lemma log_deriv_zeta_nonneg_finset_combination_auto
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ) (S : Finset ℕ) (a : ℕ → ℝ)
    (hpoly : ∀ θ : ℝ, 0 ≤ ∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ)) :
    0 ≤
      ∑ k ∈ S, a k *
        (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
          riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re :=
  log_deriv_zeta_nonneg_finset_combination σ hσ t S a
    (log_deriv_zeta_finset_series_identity σ hσ t S a) hpoly

/-- List-indexed automatic finite trigonometric detector. -/
lemma log_deriv_zeta_nonneg_list_combination_auto
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ) (ks : List ℕ) (a : ℕ → ℝ)
    (hpoly : ∀ θ : ℝ, 0 ≤ ∑ k ∈ ks.toFinset, a k * Real.cos ((k : ℝ) * θ)) :
    0 ≤
      ∑ k ∈ ks.toFinset, a k *
        (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
          riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re :=
  log_deriv_zeta_nonneg_finset_combination_auto σ hσ t ks.toFinset a hpoly

/-! ### Finite-detector algebraic lower bounds

The next lemmas are detector-agnostic algebra: once a finite detector
combination is nonnegative and the coefficient of one frequency is positive,
that frequency's logarithmic-derivative term can be bounded below by the
remaining detector terms.  If the remaining coefficients are nonnegative, any
upper bounds for those shifted terms can be absorbed into the same lower-bound
shape.  This is the algebraic handoff used by higher-degree
Stechkin/Heath-Brown/Bellotti-Trudgian-Yang detectors.
-/

/-- Solve a nonnegative finite weighted sum for one positive-coefficient
summand. -/
lemma finite_weighted_sum_single_lower_bound
    (S : Finset ℕ) (a x : ℕ → ℝ) {m : ℕ}
    (hm : m ∈ S) (ha : 0 < a m)
    (hnonneg : 0 ≤ ∑ k ∈ S, a k * x k) :
    x m ≥ - (∑ k ∈ S.erase m, a k * x k) / a m := by
  have hsum :
      a m * x m + ∑ k ∈ S.erase m, a k * x k =
        ∑ k ∈ S, a k * x k := by
    exact Finset.add_sum_erase S (fun k => a k * x k) hm
  have hnonneg' : 0 ≤ a m * x m + ∑ k ∈ S.erase m, a k * x k := by
    simpa [hsum] using hnonneg
  have hmul : -(∑ k ∈ S.erase m, a k * x k) ≤ a m * x m := by
    linarith
  exact (div_le_iff₀ ha).mpr (by simpa [mul_comm] using hmul)

/-- Solve a nonnegative finite weighted sum for one positive-coefficient
summand, after replacing all other summands by coefficient-compatible upper
bounds. -/
lemma finite_weighted_sum_single_lower_bound_of_upper_bounds
    (S : Finset ℕ) (a x B : ℕ → ℝ) {m : ℕ}
    (hm : m ∈ S) (ha : 0 < a m)
    (ha_nonneg : ∀ k, k ∈ S.erase m → 0 ≤ a k)
    (hx_upper : ∀ k, k ∈ S.erase m → x k ≤ B k)
    (hnonneg : 0 ≤ ∑ k ∈ S, a k * x k) :
    x m ≥ - (∑ k ∈ S.erase m, a k * B k) / a m := by
  have hbase :
      x m ≥ - (∑ k ∈ S.erase m, a k * x k) / a m :=
    finite_weighted_sum_single_lower_bound S a x hm ha hnonneg
  have hsum_le :
      (∑ k ∈ S.erase m, a k * x k) ≤
        ∑ k ∈ S.erase m, a k * B k := by
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_left (hx_upper k hk) (ha_nonneg k hk)
  have hdiv :
      - (∑ k ∈ S.erase m, a k * B k) / a m ≤
      - (∑ k ∈ S.erase m, a k * x k) / a m :=
    div_le_div_of_nonneg_right (neg_le_neg hsum_le) (le_of_lt ha)
  exact le_trans hdiv hbase

/-- Uniform-upper-bound version of
`finite_weighted_sum_single_lower_bound_of_upper_bounds`.  This is the algebra
needed when one common estimate controls every shifted term except the selected
positive-coefficient term. -/
lemma finite_weighted_sum_single_lower_bound_of_uniform_upper_bound
    (S : Finset ℕ) (a x : ℕ → ℝ) {m : ℕ} (B : ℝ)
    (hm : m ∈ S) (ha : 0 < a m)
    (ha_nonneg : ∀ k, k ∈ S.erase m → 0 ≤ a k)
    (hx_upper : ∀ k, k ∈ S.erase m → x k ≤ B)
    (hnonneg : 0 ≤ ∑ k ∈ S, a k * x k) :
    x m ≥ - ((∑ k ∈ S.erase m, a k) * B) / a m := by
  have h :=
    finite_weighted_sum_single_lower_bound_of_upper_bounds
      S a x (fun _ => B) hm ha ha_nonneg hx_upper hnonneg
  simpa [Finset.sum_mul] using h

/-- Detector lower-bound corollary for any finite logarithmic-derivative
combination already known to be nonnegative. -/
lemma log_deriv_zeta_finset_single_lower_bound_of_nonneg
    (σ : ℝ) (t : ℝ) (S : Finset ℕ) (a : ℕ → ℝ) {m : ℕ}
    (hm : m ∈ S) (ha : 0 < a m)
    (hnonneg :
      0 ≤
        ∑ k ∈ S, a k *
          (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
            riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re) :
    (-deriv riemannZeta ((σ : ℂ) + (m : ℂ) * I * t) /
      riemannZeta ((σ : ℂ) + (m : ℂ) * I * t)).re ≥
      - (∑ k ∈ S.erase m, a k *
          (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
            riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re) / a m :=
  finite_weighted_sum_single_lower_bound S a
    (fun k =>
      (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
        riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re)
    hm ha hnonneg

/-- Automatic detector lower bound: the finite detector nonnegativity itself is
generated from the nonnegative trigonometric polynomial hypothesis. -/
lemma log_deriv_zeta_finset_single_lower_bound_auto
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ)
    (S : Finset ℕ) (a : ℕ → ℝ) {m : ℕ}
    (hm : m ∈ S) (ha : 0 < a m)
    (hpoly : ∀ θ : ℝ, 0 ≤ ∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ)) :
    (-deriv riemannZeta ((σ : ℂ) + (m : ℂ) * I * t) /
      riemannZeta ((σ : ℂ) + (m : ℂ) * I * t)).re ≥
      - (∑ k ∈ S.erase m, a k *
          (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
            riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re) / a m :=
  log_deriv_zeta_finset_single_lower_bound_of_nonneg σ t S a hm ha
    (log_deriv_zeta_nonneg_finset_combination_auto σ hσ t S a hpoly)

/-- Detector lower-bound corollary after bounding every shifted term except the
selected positive-coefficient term. -/
lemma log_deriv_zeta_finset_single_lower_bound_of_shift_upper_bounds
    (σ : ℝ) (t : ℝ) (S : Finset ℕ) (a B : ℕ → ℝ) {m : ℕ}
    (hm : m ∈ S) (ha : 0 < a m)
    (ha_nonneg : ∀ k, k ∈ S.erase m → 0 ≤ a k)
    (hupper : ∀ k, k ∈ S.erase m →
      (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
        riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re ≤ B k)
    (hnonneg :
      0 ≤
        ∑ k ∈ S, a k *
          (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
            riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re) :
    (-deriv riemannZeta ((σ : ℂ) + (m : ℂ) * I * t) /
      riemannZeta ((σ : ℂ) + (m : ℂ) * I * t)).re ≥
      - (∑ k ∈ S.erase m, a k * B k) / a m :=
  finite_weighted_sum_single_lower_bound_of_upper_bounds S a
    (fun k =>
      (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
        riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re)
    B hm ha ha_nonneg hupper hnonneg

/-- Detector lower-bound corollary after bounding every shifted term except the
selected positive-coefficient term by one common bound. -/
lemma log_deriv_zeta_finset_single_lower_bound_of_uniform_shift_upper_bound
    (σ : ℝ) (t : ℝ) (S : Finset ℕ) (a : ℕ → ℝ) {m : ℕ} (B : ℝ)
    (hm : m ∈ S) (ha : 0 < a m)
    (ha_nonneg : ∀ k, k ∈ S.erase m → 0 ≤ a k)
    (hupper : ∀ k, k ∈ S.erase m →
      (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
        riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re ≤ B)
    (hnonneg :
      0 ≤
        ∑ k ∈ S, a k *
          (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
            riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re) :
    (-deriv riemannZeta ((σ : ℂ) + (m : ℂ) * I * t) /
      riemannZeta ((σ : ℂ) + (m : ℂ) * I * t)).re ≥
      - ((∑ k ∈ S.erase m, a k) * B) / a m :=
  finite_weighted_sum_single_lower_bound_of_uniform_upper_bound S a
    (fun k =>
      (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
        riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re)
    B hm ha ha_nonneg hupper hnonneg

/-- Automatic detector lower bound from shifted upper bounds and a nonnegative
trigonometric-polynomial certificate. -/
lemma log_deriv_zeta_finset_single_lower_bound_auto_of_shift_upper_bounds
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ)
    (S : Finset ℕ) (a B : ℕ → ℝ) {m : ℕ}
    (hm : m ∈ S) (ha : 0 < a m)
    (ha_nonneg : ∀ k, k ∈ S.erase m → 0 ≤ a k)
    (hupper : ∀ k, k ∈ S.erase m →
      (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
        riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re ≤ B k)
    (hpoly : ∀ θ : ℝ, 0 ≤ ∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ)) :
    (-deriv riemannZeta ((σ : ℂ) + (m : ℂ) * I * t) /
      riemannZeta ((σ : ℂ) + (m : ℂ) * I * t)).re ≥
      - (∑ k ∈ S.erase m, a k * B k) / a m :=
  log_deriv_zeta_finset_single_lower_bound_of_shift_upper_bounds
    σ t S a B hm ha ha_nonneg hupper
    (log_deriv_zeta_nonneg_finset_combination_auto σ hσ t S a hpoly)

/-- Automatic detector lower bound from one common shifted upper bound and a
nonnegative trigonometric-polynomial certificate. -/
lemma log_deriv_zeta_finset_single_lower_bound_auto_of_uniform_shift_upper_bound
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ)
    (S : Finset ℕ) (a : ℕ → ℝ) {m : ℕ} (B : ℝ)
    (hm : m ∈ S) (ha : 0 < a m)
    (ha_nonneg : ∀ k, k ∈ S.erase m → 0 ≤ a k)
    (hupper : ∀ k, k ∈ S.erase m →
      (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
        riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re ≤ B)
    (hpoly : ∀ θ : ℝ, 0 ≤ ∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ)) :
    (-deriv riemannZeta ((σ : ℂ) + (m : ℂ) * I * t) /
      riemannZeta ((σ : ℂ) + (m : ℂ) * I * t)).re ≥
      - ((∑ k ∈ S.erase m, a k) * B) / a m :=
  log_deriv_zeta_finset_single_lower_bound_of_uniform_shift_upper_bound
    σ t S a B hm ha ha_nonneg hupper
    (log_deriv_zeta_nonneg_finset_combination_auto σ hσ t S a hpoly)

/-- A simple square certificate for pointwise nonnegativity of a finite cosine
polynomial.  This is a first certificate hook; more general complex-exponential
sum-of-squares certificates can refine this interface later. -/
lemma trigPolynomial_nonneg_of_sq_certificate
    (S K : Finset ℕ) (a c : ℕ → ℝ)
    (hcert : ∀ θ : ℝ,
      (∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ)) =
        (∑ k ∈ K, c k * Real.cos ((k : ℝ) * θ)) ^ 2) :
    ∀ θ : ℝ, 0 ≤ ∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ) := by
  intro θ
  rw [hcert θ]
  exact sq_nonneg _

/-- Automatic finite detector from a square certificate for the detector
cosine polynomial. -/
lemma log_deriv_zeta_nonneg_finset_combination_auto_of_sq_certificate
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ)
    (S K : Finset ℕ) (a c : ℕ → ℝ)
    (hcert : ∀ θ : ℝ,
      (∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ)) =
        (∑ k ∈ K, c k * Real.cos ((k : ℝ) * θ)) ^ 2) :
    0 ≤
      ∑ k ∈ S, a k *
        (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
          riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re :=
  log_deriv_zeta_nonneg_finset_combination_auto σ hσ t S a
    (trigPolynomial_nonneg_of_sq_certificate S K a c hcert)

/-- Complex-exponential absolute-square certificate for pointwise
nonnegativity of a finite cosine polynomial.  This is the certificate shape
closest to high-degree trigonometric detectors written as
`|sum c_k exp(i k theta)|^2`. -/
lemma trigPolynomial_nonneg_of_complex_exp_abs_sq_certificate
    (S K : Finset ℕ) (a : ℕ → ℝ) (c : ℕ → ℂ)
    (hcert : ∀ θ : ℝ,
      (∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ)) =
        ‖∑ k ∈ K, c k * Complex.exp ((k : ℂ) * I * (θ : ℂ))‖ ^ 2) :
    ∀ θ : ℝ, 0 ≤ ∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ) := by
  intro θ
  rw [hcert θ]
  exact sq_nonneg _

/-- Automatic finite detector from a complex-exponential absolute-square
certificate for the detector cosine polynomial. -/
lemma log_deriv_zeta_nonneg_finset_combination_auto_of_complex_exp_abs_sq_certificate
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ)
    (S K : Finset ℕ) (a : ℕ → ℝ) (c : ℕ → ℂ)
    (hcert : ∀ θ : ℝ,
      (∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ)) =
        ‖∑ k ∈ K, c k * Complex.exp ((k : ℂ) * I * (θ : ℂ))‖ ^ 2) :
    0 ≤
      ∑ k ∈ S, a k *
        (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
          riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re :=
  log_deriv_zeta_nonneg_finset_combination_auto σ hσ t S a
    (trigPolynomial_nonneg_of_complex_exp_abs_sq_certificate S K a c hcert)

/-- Compact predicate for a complex-exponential absolute-square certificate of
a finite cosine polynomial. -/
abbrev ComplexExpAbsSqCertificate
    (S K : Finset ℕ) (a : ℕ → ℝ) (c : ℕ → ℂ) : Prop :=
  ∀ θ : ℝ,
    (∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ)) =
      ‖∑ k ∈ K, c k * Complex.exp ((k : ℂ) * I * (θ : ℂ))‖ ^ 2

/-- Predicate-based version of
`trigPolynomial_nonneg_of_complex_exp_abs_sq_certificate`. -/
lemma trigPolynomial_nonneg_of_complex_exp_abs_sq_certificate'
    (S K : Finset ℕ) (a : ℕ → ℝ) (c : ℕ → ℂ)
    (hcert : ComplexExpAbsSqCertificate S K a c) :
    ∀ θ : ℝ, 0 ≤ ∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ) :=
  trigPolynomial_nonneg_of_complex_exp_abs_sq_certificate S K a c hcert

/-- Predicate-based automatic finite detector from a complex-exponential
absolute-square certificate. -/
lemma log_deriv_zeta_nonneg_finset_combination_auto_of_complex_exp_abs_sq_certificate'
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ)
    (S K : Finset ℕ) (a : ℕ → ℝ) (c : ℕ → ℂ)
    (hcert : ComplexExpAbsSqCertificate S K a c) :
    0 ≤
      ∑ k ∈ S, a k *
        (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
          riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re :=
  log_deriv_zeta_nonneg_finset_combination_auto_of_complex_exp_abs_sq_certificate
    σ hσ t S K a c hcert

/-- Scaled complex-exponential absolute-square certificate.

This avoids introducing square roots into detector tables written as
`scale * P(theta) = ||sum c_k exp(i k theta)||^2`. -/
abbrev ScaledComplexExpAbsSqCertificate
    (scale : ℝ) (S K : Finset ℕ) (a : ℕ → ℝ) (c : ℕ → ℂ) : Prop :=
  ∀ θ : ℝ,
    scale * (∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ)) =
      ‖∑ k ∈ K, c k * Complex.exp ((k : ℂ) * I * (θ : ℂ))‖ ^ 2

/-- A positive scaled absolute-square certificate implies pointwise
nonnegativity of the finite cosine polynomial. -/
lemma trigPolynomial_nonneg_of_scaled_complex_exp_abs_sq_certificate
    (scale : ℝ) (S K : Finset ℕ) (a : ℕ → ℝ) (c : ℕ → ℂ)
    (hscale : 0 < scale)
    (hcert : ScaledComplexExpAbsSqCertificate scale S K a c) :
    ∀ θ : ℝ, 0 ≤ ∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ) := by
  intro θ
  have hnonneg :
      0 ≤ scale * (∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ)) := by
    rw [hcert θ]
    exact sq_nonneg _
  have hnonneg' :
      0 ≤ (∑ k ∈ S, a k * Real.cos ((k : ℝ) * θ)) * scale := by
    simpa [mul_comm] using hnonneg
  exact nonneg_of_mul_nonneg_left hnonneg' hscale

/-- Automatic finite detector from a positive scaled complex-exponential
absolute-square certificate. -/
lemma log_deriv_zeta_nonneg_finset_combination_auto_of_scaled_complex_exp_abs_sq_certificate
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ)
    (scale : ℝ) (S K : Finset ℕ) (a : ℕ → ℝ) (c : ℕ → ℂ)
    (hscale : 0 < scale)
    (hcert : ScaledComplexExpAbsSqCertificate scale S K a c) :
    0 ≤
      ∑ k ∈ S, a k *
        (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
          riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re :=
  log_deriv_zeta_nonneg_finset_combination_auto σ hσ t S a
    (trigPolynomial_nonneg_of_scaled_complex_exp_abs_sq_certificate
      scale S K a c hscale hcert)

/-- Selected-term lower bound directly from a positive scaled
complex-exponential absolute-square certificate. -/
lemma log_deriv_zeta_finset_single_lower_bound_of_scaled_complex_exp_abs_sq_certificate
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ)
    (scale : ℝ) (S K : Finset ℕ) (a : ℕ → ℝ) (c : ℕ → ℂ)
    {m : ℕ} (hm : m ∈ S) (ha : 0 < a m)
    (hscale : 0 < scale)
    (hcert : ScaledComplexExpAbsSqCertificate scale S K a c) :
    (-deriv riemannZeta ((σ : ℂ) + (m : ℂ) * I * t) /
      riemannZeta ((σ : ℂ) + (m : ℂ) * I * t)).re ≥
      - (∑ k ∈ S.erase m, a k *
          (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
            riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re) / a m :=
  log_deriv_zeta_finset_single_lower_bound_of_nonneg σ t S a hm ha
    (log_deriv_zeta_nonneg_finset_combination_auto_of_scaled_complex_exp_abs_sq_certificate
      σ hσ t scale S K a c hscale hcert)

/-- Selected-term lower bound from a positive scaled complex-exponential
absolute-square certificate, after absorbing supplied upper bounds for all
remaining shifted terms. -/
lemma
    log_deriv_zeta_finset_single_lower_bound_of_shift_upper_bounds_of_scaled_complex_exp_abs_sq_certificate
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ)
    (scale : ℝ) (S K : Finset ℕ) (a B : ℕ → ℝ) (c : ℕ → ℂ)
    {m : ℕ} (hm : m ∈ S) (ha : 0 < a m)
    (ha_nonneg : ∀ k, k ∈ S.erase m → 0 ≤ a k)
    (hupper : ∀ k, k ∈ S.erase m →
      (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
        riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re ≤ B k)
    (hscale : 0 < scale)
    (hcert : ScaledComplexExpAbsSqCertificate scale S K a c) :
    (-deriv riemannZeta ((σ : ℂ) + (m : ℂ) * I * t) /
      riemannZeta ((σ : ℂ) + (m : ℂ) * I * t)).re ≥
      - (∑ k ∈ S.erase m, a k * B k) / a m :=
  log_deriv_zeta_finset_single_lower_bound_of_shift_upper_bounds
    σ t S a B hm ha ha_nonneg hupper
    (log_deriv_zeta_nonneg_finset_combination_auto_of_scaled_complex_exp_abs_sq_certificate
      σ hσ t scale S K a c hscale hcert)

/-- Uniform shifted-upper-bound version of the selected-term lower bound from a
positive scaled complex-exponential absolute-square certificate. -/
lemma
    log_deriv_zeta_finset_single_lower_bound_of_uniform_shift_upper_bound_of_scaled_complex_exp_abs_sq_certificate
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ)
    (scale : ℝ) (S K : Finset ℕ) (a : ℕ → ℝ) (c : ℕ → ℂ)
    {m : ℕ} (B : ℝ) (hm : m ∈ S) (ha : 0 < a m)
    (ha_nonneg : ∀ k, k ∈ S.erase m → 0 ≤ a k)
    (hupper : ∀ k, k ∈ S.erase m →
      (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
        riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re ≤ B)
    (hscale : 0 < scale)
    (hcert : ScaledComplexExpAbsSqCertificate scale S K a c) :
    (-deriv riemannZeta ((σ : ℂ) + (m : ℂ) * I * t) /
      riemannZeta ((σ : ℂ) + (m : ℂ) * I * t)).re ≥
      - ((∑ k ∈ S.erase m, a k) * B) / a m :=
  log_deriv_zeta_finset_single_lower_bound_of_uniform_shift_upper_bound
    σ t S a B hm ha ha_nonneg hupper
    (log_deriv_zeta_nonneg_finset_combination_auto_of_scaled_complex_exp_abs_sq_certificate
      σ hσ t scale S K a c hscale hcert)

/-- Conjugating the finite-detector unit exponential changes the sign of the
phase. -/
lemma star_complex_exp_nat_mul_I_mul_real (k : ℕ) (θ : ℝ) :
    star (Complex.exp ((k : ℂ) * I * (θ : ℂ))) =
      Complex.exp (-((k : ℂ) * I * (θ : ℂ))) := by
  calc
    star (Complex.exp ((k : ℂ) * I * (θ : ℂ)))
        = Complex.exp (star ((k : ℂ) * I * (θ : ℂ))) := by
            simpa using (Complex.exp_conj ((k : ℂ) * I * (θ : ℂ))).symm
    _ = Complex.exp (-((k : ℂ) * I * (θ : ℂ))) := by
      congr 1
      simp

/-- The real part of a paired finite-detector unit exponential is the cosine of
the frequency difference. -/
lemma complex_exp_nat_mul_I_mul_real_pair_re (i j : ℕ) (θ : ℝ) :
    (Complex.exp ((i : ℂ) * I * (θ : ℂ)) *
      star (Complex.exp ((j : ℂ) * I * (θ : ℂ)))).re =
      Real.cos (((i : ℝ) - (j : ℝ)) * θ) := by
  rw [show star (Complex.exp ((j : ℂ) * I * (θ : ℂ))) =
      Complex.exp (star ((j : ℂ) * I * (θ : ℂ))) by
        simpa using (Complex.exp_conj ((j : ℂ) * I * (θ : ℂ))).symm]
  have harg :
      (i : ℂ) * I * (θ : ℂ) + star ((j : ℂ) * I * (θ : ℂ)) =
        (((i : ℝ) - (j : ℝ)) * θ : ℂ) * I := by
    simp
    ring
  rw [← Complex.exp_add, harg]
  simpa [sub_mul] using Complex.exp_ofReal_mul_I_re (((i : ℝ) - (j : ℝ)) * θ)

/-- Square norm of a finite complex sum as a double sum of pairwise real
parts. -/
lemma norm_sq_sum_eq_double_sum_re (K : Finset ℕ) (z : ℕ → ℂ) :
    ‖∑ k ∈ K, z k‖ ^ 2 =
      ∑ j ∈ K, ∑ i ∈ K, (star (z i) * z j).re := by
  rw [Complex.sq_norm]
  have hnorm :
      (Complex.normSq (∑ k ∈ K, z k) : ℂ) =
        star (∑ k ∈ K, z k) * (∑ k ∈ K, z k) := by
    simpa using (Complex.normSq_eq_conj_mul_self (z := ∑ k ∈ K, z k))
  calc
    Complex.normSq (∑ k ∈ K, z k)
        = (star (∑ k ∈ K, z k) * (∑ k ∈ K, z k)).re := by
          simpa using congrArg Complex.re hnorm
    _ = (∑ j ∈ K, ∑ i ∈ K, star (z i) * z j).re := by
      simp [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ j ∈ K, ∑ i ∈ K, (star (z i) * z j).re := by
      simp

/-- Square norm of a finite real-coefficient exponential sum as the standard
double Fourier cosine sum. -/
lemma norm_sq_sum_real_coeff_complex_exp_eq_double_sum
    (K : Finset ℕ) (c : ℕ → ℝ) (θ : ℝ) :
    ‖∑ k ∈ K, (c k : ℂ) * Complex.exp ((k : ℂ) * I * (θ : ℂ))‖ ^ 2 =
      ∑ j ∈ K, ∑ i ∈ K,
        c i * c j * Real.cos (((j : ℝ) - (i : ℝ)) * θ) := by
  rw [norm_sq_sum_eq_double_sum_re K
    (fun k => (c k : ℂ) * Complex.exp ((k : ℂ) * I * (θ : ℂ)))]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  have hpair := complex_exp_nat_mul_I_mul_real_pair_re j i θ
  calc
    (star ((c i : ℂ) * Complex.exp ((i : ℂ) * I * (θ : ℂ))) *
        ((c j : ℂ) * Complex.exp ((j : ℂ) * I * (θ : ℂ)))).re
        = (((c i * c j : ℝ) : ℂ) *
            (Complex.exp ((j : ℂ) * I * (θ : ℂ)) *
              star (Complex.exp ((i : ℂ) * I * (θ : ℂ))))).re := by
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ = (c i * c j) *
          (Complex.exp ((j : ℂ) * I * (θ : ℂ)) *
            star (Complex.exp ((i : ℂ) * I * (θ : ℂ)))).re := by
          simp
    _ = c i * c j * Real.cos (((j : ℝ) - (i : ℝ)) * θ) := by
          rw [hpair]

/-! ### Bellotti-Trudgian-Yang detector coefficient table

The following constants encode the integer coefficient table for the
Bellotti-Trudgian-Yang detector shape
`scale * P(theta) = ||sum_{0 <= k <= 16} c_k exp(i k theta)||^2`.
This records the table and checks the quoted low-degree and aggregate
coefficients; the full convolution identity remains a later finite-sum step.
-/

/-- Denominator scale in the Bellotti-Trudgian-Yang trigonometric detector. -/
def btyDetectorScale : ℝ := 14912370

lemma btyDetectorScale_pos : 0 < btyDetectorScale := by
  norm_num [btyDetectorScale]

/-- Exponential coefficient support `{0, ..., 16}` for the BTY detector. -/
def btyExpSupport : Finset ℕ := Finset.range 17

/-- Cosine coefficient support `{0, ..., 16}` for the BTY detector. -/
def btyDetectorSupport : Finset ℕ := Finset.range 17

/-- Integer coefficients `c_k` in the BTY exponential square. -/
def btyRawCoeff : ℕ → ℤ
  | 0 => 4
  | 1 => -8
  | 2 => 2
  | 3 => 20
  | 4 => -9
  | 5 => -34
  | 6 => 27
  | 7 => 91
  | 8 => -27
  | 9 => -201
  | 10 => 32
  | 11 => 895
  | 12 => 1949
  | 13 => 2389
  | 14 => 1896
  | 15 => 949
  | 16 => 239
  | _ => 0

/-- Complex-valued version of the BTY exponential coefficients. -/
def btyExpCoeff (k : ℕ) : ℂ :=
  (btyRawCoeff k : ℂ)

/-- Cosine coefficients obtained from the BTY exponential-square convolution. -/
noncomputable def btyDetectorCoeff (k : ℕ) : ℝ :=
  if k = 0 then
    (∑ j ∈ Finset.range 17, ((btyRawCoeff j : ℝ) ^ 2)) / btyDetectorScale
  else
    (2 * ∑ j ∈ Finset.range (17 - k),
      (btyRawCoeff j : ℝ) * (btyRawCoeff (j + k) : ℝ)) / btyDetectorScale

/-- BTY's quoted constant coefficient `a_0 = 1`. -/
lemma btyDetectorCoeff_zero : btyDetectorCoeff 0 = 1 := by
  norm_num [btyDetectorCoeff, btyRawCoeff, btyDetectorScale]

/-- BTY's quoted first cosine coefficient `a_1 = 865534 / 497079`. -/
lemma btyDetectorCoeff_one : btyDetectorCoeff 1 = (865534 : ℝ) / 497079 := by
  norm_num [btyDetectorCoeff, btyRawCoeff, btyDetectorScale]

/-- Positivity of the first BTY cosine coefficient. -/
lemma btyDetectorCoeff_one_pos : 0 < btyDetectorCoeff 1 := by
  rw [btyDetectorCoeff_one]
  norm_num

/-- BTY's quoted coefficient sum `sum_{1 <= k <= 16} a_k = 2919857 / 828465`. -/
lemma btyDetectorCoeff_sum_one_to_K :
    (∑ k ∈ Finset.Icc 1 16, btyDetectorCoeff k) =
      (2919857 : ℝ) / 828465 := by
  have hIcc :
      Finset.Icc 1 16 =
        ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} :
          Finset ℕ) := by
    decide
  rw [hIcc]
  norm_num [btyDetectorCoeff, btyRawCoeff, btyDetectorScale]

/-- Sum of all BTY detector coefficients except the selected `k = 1` term. -/
lemma btyDetectorCoeff_sum_support_erase_one :
    (∑ k ∈ btyDetectorSupport.erase 1, btyDetectorCoeff k) =
      (6917296 : ℝ) / 2485395 := by
  have herase :
      btyDetectorSupport.erase 1 =
        ({0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} :
          Finset ℕ) := by
    decide
  rw [herase]
  norm_num [btyDetectorCoeff, btyRawCoeff, btyDetectorScale]

/-- Sum of the BTY detector coefficients except the selected `k = 1` term and
the central `k = 0` term. -/
lemma btyDetectorCoeff_sum_support_erase_one_erase_zero :
    (∑ k ∈ (btyDetectorSupport.erase 1).erase 0, btyDetectorCoeff k) =
      (4431901 : ℝ) / 2485395 := by
  have herase :
      (btyDetectorSupport.erase 1).erase 0 =
        ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} :
          Finset ℕ) := by
    decide
  rw [herase]
  norm_num [btyDetectorCoeff, btyRawCoeff, btyDetectorScale]

/-- Evaluate the mixed BTY coefficient sum with a separate central `k = 0`
bound and one common bound for all remaining nonzero detector frequencies. -/
lemma btyDetectorCoeff_mixed_center_sum (B0 bound : ℝ) :
    (∑ k ∈ btyDetectorSupport.erase 1, btyDetectorCoeff k *
      (if k = 0 then B0 else bound)) =
      B0 + ((4431901 : ℝ) / 2485395) * bound := by
  have herase :
      btyDetectorSupport.erase 1 =
        ({0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} :
          Finset ℕ) := by
    decide
  rw [herase]
  norm_num [btyDetectorCoeff, btyRawCoeff, btyDetectorScale]
  ring

/-- The BTY detector has no cosine coefficients beyond degree `16`. -/
lemma btyDetectorCoeff_eq_zero_of_seventeen_le {k : ℕ} (hk : 17 ≤ k) :
    btyDetectorCoeff k = 0 := by
  have hk_ne : k ≠ 0 := by omega
  have hsub : 17 - k = 0 := Nat.sub_eq_zero_of_le hk
  simp [btyDetectorCoeff, hk_ne, hsub]

/-- The first shifted term belongs to the BTY detector support. -/
lemma one_mem_btyDetectorSupport : 1 ∈ btyDetectorSupport := by
  simp [btyDetectorSupport]

/-- Every coefficient in the BTY detector support is nonnegative. -/
lemma btyDetectorCoeff_nonneg_of_mem_support {k : ℕ}
    (hk : k ∈ btyDetectorSupport) :
    0 ≤ btyDetectorCoeff k := by
  rw [btyDetectorSupport] at hk
  fin_cases hk <;> norm_num [btyDetectorCoeff, btyRawCoeff, btyDetectorScale]

/-- Every coefficient in the BTY detector support is strictly positive. -/
lemma btyDetectorCoeff_pos_of_mem_support {k : ℕ}
    (hk : k ∈ btyDetectorSupport) :
    0 < btyDetectorCoeff k := by
  rw [btyDetectorSupport] at hk
  fin_cases hk <;> norm_num [btyDetectorCoeff, btyRawCoeff, btyDetectorScale]

set_option maxHeartbeats 800000 in
/-- The BTY cosine coefficients regroup the exponential-square double sum. -/
lemma bty_scaled_detector_sum_eq_double_sum (θ : ℝ) :
    btyDetectorScale *
        (∑ k ∈ btyDetectorSupport,
          btyDetectorCoeff k * Real.cos ((k : ℝ) * θ)) =
      ∑ j ∈ btyExpSupport, ∑ i ∈ btyExpSupport,
        (btyRawCoeff i : ℝ) *
          (btyRawCoeff j : ℝ) *
            Real.cos (((j : ℝ) - (i : ℝ)) * θ) := by
  have hsupport :
      btyDetectorSupport =
        ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} :
          Finset ℕ) := by
    decide
  have hexp :
      btyExpSupport =
        ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} :
          Finset ℕ) := by
    decide
  rw [hsupport, hexp]
  norm_num [btyDetectorScale, btyDetectorSupport, btyExpSupport,
    btyDetectorCoeff, btyRawCoeff]
  ring_nf

/-- Full scaled complex-exponential absolute-square certificate for the BTY
degree-16 detector. -/
lemma btyScaledComplexExpAbsSqCertificate :
    ScaledComplexExpAbsSqCertificate
      btyDetectorScale btyDetectorSupport btyExpSupport
      btyDetectorCoeff btyExpCoeff := by
  intro θ
  calc
    btyDetectorScale *
        (∑ k ∈ btyDetectorSupport,
          btyDetectorCoeff k * Real.cos ((k : ℝ) * θ))
        =
      ∑ j ∈ btyExpSupport, ∑ i ∈ btyExpSupport,
        (btyRawCoeff i : ℝ) *
          (btyRawCoeff j : ℝ) *
            Real.cos (((j : ℝ) - (i : ℝ)) * θ) :=
      bty_scaled_detector_sum_eq_double_sum θ
    _ = ‖∑ k ∈ btyExpSupport,
          ((btyRawCoeff k : ℝ) : ℂ) *
            Complex.exp ((k : ℂ) * I * (θ : ℂ))‖ ^ 2 :=
      (norm_sq_sum_real_coeff_complex_exp_eq_double_sum
        btyExpSupport (fun k => (btyRawCoeff k : ℝ)) θ).symm
    _ = ‖∑ k ∈ btyExpSupport,
          btyExpCoeff k *
            Complex.exp ((k : ℂ) * I * (θ : ℂ))‖ ^ 2 := by
      simp [btyExpCoeff]

/-- Pointwise nonnegativity of the BTY degree-16 cosine detector.

This is the reusable detector fact extracted from the full scaled
complex-exponential absolute-square certificate. -/
lemma btyDetectorPolynomial_nonneg (θ : ℝ) :
    0 ≤ ∑ k ∈ btyDetectorSupport,
      btyDetectorCoeff k * Real.cos ((k : ℝ) * θ) :=
  trigPolynomial_nonneg_of_scaled_complex_exp_abs_sq_certificate
    btyDetectorScale btyDetectorSupport btyExpSupport
    btyDetectorCoeff btyExpCoeff
    btyDetectorScale_pos btyScaledComplexExpAbsSqCertificate θ

/-- Automatic logarithmic-derivative detector inequality from the full BTY
scaled certificate. -/
lemma log_deriv_zeta_nonneg_bty_detector_from_scaled_certificate
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    0 ≤
      ∑ k ∈ btyDetectorSupport, btyDetectorCoeff k *
        (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
          riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re :=
  log_deriv_zeta_nonneg_finset_combination_auto
    σ hσ t btyDetectorSupport btyDetectorCoeff
    btyDetectorPolynomial_nonneg

/-- Lower bound for the first shifted logarithmic-derivative term obtained from
the degree-16 BTY detector. -/
lemma log_deriv_zeta_bty_first_shift_lower_bound
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    (-deriv riemannZeta ((σ : ℂ) + (1 : ℂ) * I * t) /
        riemannZeta ((σ : ℂ) + (1 : ℂ) * I * t)).re ≥
      - (∑ k ∈ btyDetectorSupport.erase 1, btyDetectorCoeff k *
          (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
            riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re) /
        btyDetectorCoeff 1 := by
  let x : ℕ → ℝ := fun k =>
    (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
      riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re
  have hbound := finset_weighted_nonneg_term_lower_bound
    btyDetectorSupport btyDetectorCoeff x one_mem_btyDetectorSupport
    btyDetectorCoeff_one_pos
    (log_deriv_zeta_nonneg_bty_detector_from_scaled_certificate σ hσ t)
  simpa [x] using hbound

/-- Algebraic lower-bound corollary for the `k=1` term of the BTY detector. -/
lemma log_deriv_zeta_bty_detector_one_lower_bound
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
      riemannZeta ((σ : ℂ) + I * t)).re ≥
      - (∑ k ∈ btyDetectorSupport.erase 1, btyDetectorCoeff k *
          (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
            riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re) / btyDetectorCoeff 1 := by
  have hmem : 1 ∈ btyDetectorSupport := by
    norm_num [btyDetectorSupport]
  simpa [one_mul] using
    log_deriv_zeta_finset_single_lower_bound_of_nonneg
      σ t btyDetectorSupport btyDetectorCoeff hmem btyDetectorCoeff_one_pos
      (log_deriv_zeta_nonneg_bty_detector_from_scaled_certificate σ hσ t)

/-- If all BTY shifted terms except `k=1` have supplied upper bounds, then the
`k=1` logarithmic-derivative term has the corresponding weighted lower bound. -/
lemma log_deriv_zeta_bty_detector_one_lower_bound_of_shift_upper_bounds
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ) (B : ℕ → ℝ)
    (hupper : ∀ k, k ∈ btyDetectorSupport.erase 1 →
      (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
        riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re ≤ B k) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
      riemannZeta ((σ : ℂ) + I * t)).re ≥
      - (∑ k ∈ btyDetectorSupport.erase 1, btyDetectorCoeff k * B k) /
        btyDetectorCoeff 1 := by
  have hmem : 1 ∈ btyDetectorSupport := by
    norm_num [btyDetectorSupport]
  have hcoeff_nonneg :
      ∀ k, k ∈ btyDetectorSupport.erase 1 → 0 ≤ btyDetectorCoeff k := by
    intro k hk
    exact btyDetectorCoeff_nonneg_of_mem_support (Finset.mem_of_mem_erase hk)
  simpa [one_mul] using
    log_deriv_zeta_finset_single_lower_bound_of_shift_upper_bounds
      σ t btyDetectorSupport btyDetectorCoeff B hmem btyDetectorCoeff_one_pos
      hcoeff_nonneg hupper
      (log_deriv_zeta_nonneg_bty_detector_from_scaled_certificate σ hσ t)

/-- Uniform shifted-term version of the BTY `k = 1` lower bound.  This is the
shape needed when later analytic estimates supply one common upper bound for all
remaining shifted logarithmic-derivative terms. -/
lemma log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_shift_upper_bound
    (σ : ℝ) (hσ : 1 < σ) (t B : ℝ)
    (hupper : ∀ k, k ∈ btyDetectorSupport.erase 1 →
      (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
        riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re ≤ B) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
      riemannZeta ((σ : ℂ) + I * t)).re ≥
      - (((6917296 : ℝ) / 2485395) * B) / btyDetectorCoeff 1 := by
  have h :=
    log_deriv_zeta_bty_detector_one_lower_bound_of_shift_upper_bounds
      σ hσ t (fun _ => B) hupper
  have hsum :
      (∑ k ∈ btyDetectorSupport.erase 1, btyDetectorCoeff k * B) =
        ((6917296 : ℝ) / 2485395) * B := by
    rw [← Finset.sum_mul, btyDetectorCoeff_sum_support_erase_one]
  simpa [hsum] using h

/-- Uniform shifted-term version of the BTY `k = 1` lower bound with the
coefficient penalty simplified to one explicit rational constant. -/
lemma log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_shift_upper_bound_simplified
    (σ : ℝ) (hσ : 1 < σ) (t B : ℝ)
    (hupper : ∀ k, k ∈ btyDetectorSupport.erase 1 →
      (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
        riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re ≤ B) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
      riemannZeta ((σ : ℂ) + I * t)).re ≥
      - ((3458648 : ℝ) / 2163835) * B := by
  have h :=
    log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_shift_upper_bound
      σ hσ t B hupper
  have hconst :
      - (((6917296 : ℝ) / 2485395) * B) / btyDetectorCoeff 1 =
        - ((3458648 : ℝ) / 2163835) * B := by
    rw [btyDetectorCoeff_one]
    ring_nf
  simpa [hconst] using h

/-- Minimal concrete complex-exponential absolute-square certificate:
`1 = ‖exp(0)‖^2`.  This is a template for later finite coefficient-table
certificates. -/
lemma complexExpAbsSqCertificate_const_one :
    ComplexExpAbsSqCertificate ({0} : Finset ℕ) ({0} : Finset ℕ)
      (fun _ => (1 : ℝ)) (fun _ => (1 : ℂ)) := by
  intro θ
  simp

/-- The automatic detector theorem applied to the constant-one
complex-exponential certificate. -/
lemma log_deriv_zeta_nonneg_const_one_detector_from_complex_exp_certificate
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    0 ≤
      ∑ k ∈ ({0} : Finset ℕ), (1 : ℝ) *
        (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
          riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re :=
  log_deriv_zeta_nonneg_finset_combination_auto_of_complex_exp_abs_sq_certificate'
    σ hσ t ({0} : Finset ℕ) ({0} : Finset ℕ)
    (fun _ => (1 : ℝ)) (fun _ => (1 : ℂ))
    complexExpAbsSqCertificate_const_one

/-- Coefficients for the toy detector polynomial `2 + 2 cos theta`. -/
def twoAddTwoCosDetectorCoeff (k : ℕ) : ℝ :=
  if k = 0 then 2 else if k = 1 then 2 else 0

/-- Coefficients for the toy exponential sum `1 + exp(i theta)`. -/
def onePlusExpCoeff (k : ℕ) : ℂ :=
  if k = 0 then 1 else if k = 1 then 1 else 0

/-- Concrete nontrivial complex-exponential certificate:
`2 + 2 cos theta = ‖1 + exp(i theta)‖^2`. -/
lemma complexExpAbsSqCertificate_two_add_two_cos :
    ComplexExpAbsSqCertificate ({0, 1} : Finset ℕ) ({0, 1} : Finset ℕ)
      twoAddTwoCosDetectorCoeff onePlusExpCoeff := by
  intro θ
  simp [twoAddTwoCosDetectorCoeff, onePlusExpCoeff]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add]
  have hexp : Complex.exp (I * (θ : ℂ)) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
    have hmul : I * (θ : ℂ) = (θ : ℂ) * I := by ring
    rw [hmul, Complex.exp_ofReal_mul_I]
  rw [hexp]
  simp [Complex.normSq_apply]
  have hcosre : (Complex.cos (θ : ℂ)).re = Real.cos θ := by
    have hcos : Complex.cos (θ : ℂ) = (Real.cos θ : ℂ) := by
      simp
    exact hcos ▸ rfl
  have hsinre : (Complex.sin (θ : ℂ)).re = Real.sin θ := by
    have hsin : Complex.sin (θ : ℂ) = (Real.sin θ : ℂ) := by
      simp
    exact hsin ▸ rfl
  rw [hcosre, hsinre]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The automatic detector theorem applied to the concrete certificate
`2 + 2 cos theta = ‖1 + exp(i theta)‖^2`. -/
lemma log_deriv_zeta_nonneg_two_add_two_cos_detector_from_complex_exp_certificate
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    0 ≤
      ∑ k ∈ ({0, 1} : Finset ℕ), twoAddTwoCosDetectorCoeff k *
        (-deriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t) /
          riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)).re :=
  log_deriv_zeta_nonneg_finset_combination_auto_of_complex_exp_abs_sq_certificate'
    σ hσ t ({0, 1} : Finset ℕ) ({0, 1} : Finset ℕ)
    twoAddTwoCosDetectorCoeff onePlusExpCoeff
    complexExpAbsSqCertificate_two_add_two_cos

/-- The existing `3-4-1` theorem as the base detector instance. -/
lemma log_deriv_zeta_nonneg_three_four_one_from_finset
    (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    0 ≤
      3 * (- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      + 4 * (- deriv riemannZeta ((σ : ℂ) + I * t) /
          riemannZeta ((σ : ℂ) + I * t)).re
      + (- deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re :=
  log_deriv_zeta_nonneg_combination σ hσ t

/-- Algebraic lower-bound corollary of the 3-4-1 inequality. -/
lemma log_deriv_zeta_lower_bound (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    (- deriv riemannZeta ((σ : ℂ) + I * t) / riemannZeta ((σ : ℂ) + I * t)).re ≥
      -(3 / 4 : ℝ) * (- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      - (1 / 4 : ℝ) *
        (- deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re := by
  have h := log_deriv_zeta_nonneg_combination σ hσ t
  linarith

/-- Definition-level bridge from Mathlib's `logDeriv ζ` notation to the
classical quotient `ζ'/ζ`. -/
lemma logDeriv_riemannZeta_eq_deriv_div (s : ℂ) :
    logDeriv riemannZeta s = deriv riemannZeta s / riemannZeta s :=
  rfl

/-- Negated quotient form of `logDeriv_riemannZeta_eq_deriv_div`, matching the
notation used in the 3-4-1 inequality. -/
lemma neg_logDeriv_riemannZeta_eq_neg_deriv_div (s : ℂ) :
    -logDeriv riemannZeta s = -deriv riemannZeta s / riemannZeta s := by
  simp [logDeriv_riemannZeta_eq_deriv_div, neg_div]

/-- Reverse direction of the negated logarithmic-derivative bridge. -/
lemma neg_deriv_div_riemannZeta_eq_neg_logDeriv (s : ℂ) :
    -deriv riemannZeta s / riemannZeta s = -logDeriv riemannZeta s :=
  (neg_logDeriv_riemannZeta_eq_neg_deriv_div s).symm

/-- Real-part bridge from `logDeriv ζ` to `ζ'/ζ`. -/
lemma logDeriv_riemannZeta_re_eq_deriv_div_re (s : ℂ) :
    (logDeriv riemannZeta s).re =
      (deriv riemannZeta s / riemannZeta s).re := by
  rw [logDeriv_riemannZeta_eq_deriv_div]

/-- Real-part bridge for the negated logarithmic derivative, matching
`-ζ'/ζ`. -/
lemma neg_logDeriv_riemannZeta_re_eq_neg_deriv_div_re (s : ℂ) :
    (-logDeriv riemannZeta s).re =
      (-deriv riemannZeta s / riemannZeta s).re := by
  rw [neg_logDeriv_riemannZeta_eq_neg_deriv_div]

/-- Reverse real-part bridge for the negated quotient. -/
lemma neg_deriv_div_riemannZeta_re_eq_neg_logDeriv_re (s : ℂ) :
    (-deriv riemannZeta s / riemannZeta s).re =
      (-logDeriv riemannZeta s).re :=
  (neg_logDeriv_riemannZeta_re_eq_neg_deriv_div_re s).symm

/-- Norm bridge from `logDeriv ζ` to `ζ'/ζ`. -/
lemma norm_logDeriv_riemannZeta_eq_norm_deriv_div (s : ℂ) :
    ‖logDeriv riemannZeta s‖ =
      ‖deriv riemannZeta s / riemannZeta s‖ := by
  rw [logDeriv_riemannZeta_eq_deriv_div]

/-- Norm bridge for the negated quotient form `-ζ'/ζ`. -/
lemma norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv (s : ℂ) :
    ‖-deriv riemannZeta s / riemannZeta s‖ =
      ‖logDeriv riemannZeta s‖ := by
  rw [neg_deriv_div_riemannZeta_eq_neg_logDeriv, norm_neg]

/-- Uniform norm-bound version of the BTY `k = 1` lower bound.

This is the handoff used when a later Jensen/Borel step supplies one common
norm bound for all remaining BTY frequencies. -/
lemma log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_vertical_norm_bound
    (σ : ℝ) (hσ : 1 < σ) (t B : ℝ)
    (hupper : ∀ k, k ∈ btyDetectorSupport.erase 1 →
      ‖logDeriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)‖ ≤ B) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
      riemannZeta ((σ : ℂ) + I * t)).re ≥
      - ((3458648 : ℝ) / 2163835) * B := by
  refine
    log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_shift_upper_bound_simplified
      σ hσ t B ?_
  intro k hk
  let z : ℂ := (σ : ℂ) + (k : ℂ) * I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta z‖ :=
        norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
    _ ≤ B := hupper k hk

/-- Uniform logarithmic norm-bound version of the BTY `k = 1` lower bound. -/
lemma log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_vertical_log_bound
    (σ : ℝ) (hσ : 1 < σ) (t B L0 : ℝ)
    (hupper : ∀ k, k ∈ btyDetectorSupport.erase 1 →
      ‖logDeriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)‖ ≤ B * L0) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
      riemannZeta ((σ : ℂ) + I * t)).re ≥
      - ((3458648 : ℝ) / 2163835) * (B * L0) :=
  log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_vertical_norm_bound
    σ hσ t (B * L0) hupper

/-- Convert a one-variable vertical logarithmic-derivative bound into the
finite-family bound required by the BTY detector.

The only height bookkeeping left to the caller is the finite log-scale
comparison `hlog` for the detector frequencies. -/
lemma btyDetector_uniform_vertical_log_bound_of_global_log_abs_add_three_bound
    (σ t B L0 : ℝ) (hB : 0 ≤ B)
    (hglobal : ∀ u : ℝ,
      ‖logDeriv riemannZeta ((σ : ℂ) + I * u)‖ ≤
        B * Real.log (|u| + 3))
    (hlog : ∀ k, k ∈ btyDetectorSupport.erase 1 →
      Real.log (|(k : ℝ) * t| + 3) ≤ L0) :
    ∀ k, k ∈ btyDetectorSupport.erase 1 →
      ‖logDeriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)‖ ≤ B * L0 := by
  intro k hk
  have hglobal_k := hglobal ((k : ℝ) * t)
  calc
    ‖logDeriv riemannZeta ((σ : ℂ) + (k : ℂ) * I * t)‖
        ≤ B * Real.log (|(k : ℝ) * t| + 3) := by
          simpa [Complex.ofReal_mul, mul_assoc, mul_comm, mul_left_comm]
            using hglobal_k
    _ ≤ B * L0 := mul_le_mul_of_nonneg_left (hlog k hk) hB

/-- BTY lower bound from a one-variable vertical logarithmic-derivative bound.

This packages the remaining high-height input in the classical form
`‖logDeriv ζ(σ+iu)‖ <= B log(|u|+3)`, plus a finite detector-frequency
height comparison. -/
lemma log_deriv_zeta_bty_detector_one_lower_bound_of_global_vertical_log_abs_add_three_bound
    (σ : ℝ) (hσ : 1 < σ) (t B L0 : ℝ) (hB : 0 ≤ B)
    (hglobal : ∀ u : ℝ,
      ‖logDeriv riemannZeta ((σ : ℂ) + I * u)‖ ≤
        B * Real.log (|u| + 3))
    (hlog : ∀ k, k ∈ btyDetectorSupport.erase 1 →
      Real.log (|(k : ℝ) * t| + 3) ≤ L0) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
      riemannZeta ((σ : ℂ) + I * t)).re ≥
      - ((3458648 : ℝ) / 2163835) * (B * L0) :=
  log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_vertical_log_bound
    σ hσ t B L0
    (btyDetector_uniform_vertical_log_bound_of_global_log_abs_add_three_bound
      σ t B L0 hB hglobal hlog)

/-- Automatic finite height comparison for the BTY support.

The support is contained in `{0, ..., 16}`, so every detector frequency is
absorbed by the coarse common scale `log(17 * (|t| + 3))`. -/
lemma btyDetector_log_abs_mul_add_three_le_log_seventeen_mul_abs_add_three
    (t : ℝ) {k : ℕ} (hk : k ∈ btyDetectorSupport.erase 1) :
    Real.log (|(k : ℝ) * t| + 3) ≤ Real.log (17 * (|t| + 3)) := by
  have hk_mem : k ∈ btyDetectorSupport := Finset.mem_of_mem_erase hk
  have hk_lt : k < 17 := by
    simpa [btyDetectorSupport] using hk_mem
  have hk_nonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk_le : (k : ℝ) ≤ 16 := by
    exact_mod_cast Nat.le_of_lt_succ hk_lt
  have ht_nonneg : 0 ≤ |t| := abs_nonneg t
  have hleft_pos : 0 < |(k : ℝ) * t| + 3 := by
    nlinarith [abs_nonneg ((k : ℝ) * t)]
  have hle : |(k : ℝ) * t| + 3 ≤ 17 * (|t| + 3) := by
    rw [abs_mul, abs_of_nonneg hk_nonneg]
    nlinarith
  exact Real.log_le_log hleft_pos hle

/-- BTY lower bound from a one-variable vertical logarithmic-derivative bound,
with the finite detector-frequency height comparison discharged automatically.
-/
lemma log_deriv_zeta_bty_detector_one_lower_bound_of_global_vertical_log_abs_add_three_bound_auto
    (σ : ℝ) (hσ : 1 < σ) (t B : ℝ) (hB : 0 ≤ B)
    (hglobal : ∀ u : ℝ,
      ‖logDeriv riemannZeta ((σ : ℂ) + I * u)‖ ≤
        B * Real.log (|u| + 3)) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
      riemannZeta ((σ : ℂ) + I * t)).re ≥
      - ((3458648 : ℝ) / 2163835) *
        (B * Real.log (17 * (|t| + 3))) :=
  log_deriv_zeta_bty_detector_one_lower_bound_of_global_vertical_log_abs_add_three_bound
    σ hσ t B (Real.log (17 * (|t| + 3))) hB hglobal
    (fun k hk =>
      btyDetector_log_abs_mul_add_three_le_log_seventeen_mul_abs_add_three
        t (k := k) hk)

/-- Fixed-margin BTY lower bound from the existing vertical logarithmic
derivative estimate for `Re(s) >= 1 + ε`.

This is not the classical zero-free-region scale, but it closes the
fixed-margin detector handoff without leaving any finite-support bookkeeping
hypotheses. -/
lemma exists_log_deriv_zeta_bty_detector_one_lower_bound_of_one_add_le
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 + ε ≤ σ →
      (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re ≥
        - ((3458648 : ℝ) / 2163835) *
          (C * Real.log (17 * (|t| + 3))) := by
  rcases exists_norm_logDeriv_riemannZeta_sigma_it_le_log_abs_add_three_of_one_add_le
      hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro σ t hσ
  have hσ_gt : 1 < σ := by nlinarith [hε, hσ]
  exact
    log_deriv_zeta_bty_detector_one_lower_bound_of_global_vertical_log_abs_add_three_bound_auto
      σ hσ_gt t C hC (fun u => hbound σ u hσ)

/-- Fixed-margin real-part bound for the shifted `σ + it` term in the
3-4-1 inequality. -/
lemma exists_re_neg_deriv_div_riemannZeta_sigma_it_le_log_abs_add_three_of_one_add_le
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 + ε ≤ σ →
      (-deriv riemannZeta ((σ : ℂ) + I * t) /
          riemannZeta ((σ : ℂ) + I * t)).re ≤
        C * Real.log (|t| + 3) := by
  rcases exists_norm_logDeriv_riemannZeta_sigma_it_le_log_abs_add_three_of_one_add_le
      hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro σ t hσ
  let z : ℂ := (σ : ℂ) + I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta z‖ :=
        norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
    _ ≤ C * Real.log (|t| + 3) := hbound σ t hσ

/-- Fixed-margin real-part bound for the shifted `σ + 2it` term in the
3-4-1 inequality. -/
lemma exists_re_neg_deriv_div_riemannZeta_sigma_two_it_le_log_abs_add_three_of_one_add_le
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 + ε ≤ σ →
      (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
        C * Real.log (|t| + 3) := by
  rcases exists_norm_logDeriv_riemannZeta_sigma_two_it_le_log_abs_add_three_of_one_add_le
      hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro σ t hσ
  let z : ℂ := (σ : ℂ) + 2 * I * t
  calc
    (-deriv riemannZeta z / riemannZeta z).re
        ≤ ‖-deriv riemannZeta z / riemannZeta z‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta z‖ :=
        norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv z
    _ ≤ C * Real.log (|t| + 3) := hbound σ t hσ

/-- A single fixed-margin logarithmic bound for all three real-part terms
appearing in the 3-4-1 combination.

This is deliberately a fixed-margin result: the hypothesis is `1+ε ≤ σ`.
The classical zero-free region still needs the corresponding estimates for the
moving choice `σ = 1 + a / log |t|`. -/
lemma exists_re_neg_deriv_div_riemannZeta_fixed_margin_three_four_one_bounds
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 + ε ≤ σ →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤
          C * Real.log (|t| + 3) ∧
      (-deriv riemannZeta ((σ : ℂ) + I * t) /
          riemannZeta ((σ : ℂ) + I * t)).re ≤
          C * Real.log (|t| + 3) ∧
      (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re ≤
          C * Real.log (|t| + 3) := by
  rcases exists_re_neg_deriv_div_riemannZeta_sigma_it_le_log_abs_add_three_of_one_add_le
      hε with ⟨C₁, hC₁, hbound₁⟩
  rcases exists_re_neg_deriv_div_riemannZeta_sigma_two_it_le_log_abs_add_three_of_one_add_le
      hε with ⟨C₂, hC₂, hbound₂⟩
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  intro σ t hσ
  have hlog_nonneg : 0 ≤ Real.log (|t| + 3) := by
    exact Real.log_nonneg (by nlinarith [abs_nonneg t] : (1 : ℝ) ≤ |t| + 3)
  have hlog3_le : Real.log (3 : ℝ) ≤ Real.log (|t| + 3) := by
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 3)
    nlinarith [abs_nonneg t]
  have hC₁_le : C₁ ≤ C₁ + C₂ := by linarith
  have hC₂_le : C₂ ≤ C₁ + C₂ := by linarith
  have hC₁_log_le :
      C₁ * Real.log (|t| + 3) ≤ (C₁ + C₂) * Real.log (|t| + 3) :=
    mul_le_mul_of_nonneg_right hC₁_le hlog_nonneg
  have hC₂_log_le :
      C₂ * Real.log (|t| + 3) ≤ (C₁ + C₂) * Real.log (|t| + 3) :=
    mul_le_mul_of_nonneg_right hC₂_le hlog_nonneg
  constructor
  · have hzero := hbound₁ σ 0 hσ
    have hzero' :
        (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤
          C₁ * Real.log (3 : ℝ) := by
      simpa using hzero
    calc
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
          ≤ C₁ * Real.log (3 : ℝ) := hzero'
      _ ≤ C₁ * Real.log (|t| + 3) :=
          mul_le_mul_of_nonneg_left hlog3_le hC₁
      _ ≤ (C₁ + C₂) * Real.log (|t| + 3) := hC₁_log_le
  constructor
  · calc
      (-deriv riemannZeta ((σ : ℂ) + I * t) /
          riemannZeta ((σ : ℂ) + I * t)).re
          ≤ C₁ * Real.log (|t| + 3) := hbound₁ σ t hσ
      _ ≤ (C₁ + C₂) * Real.log (|t| + 3) := hC₁_log_le
  · calc
      (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re
          ≤ C₂ * Real.log (|t| + 3) := hbound₂ σ t hσ
      _ ≤ (C₁ + C₂) * Real.log (|t| + 3) := hC₂_log_le

/-- Fixed-margin logarithmic upper bound for the full 3-4-1 combination,
paired with its proved nonnegativity. -/
lemma exists_three_four_one_combination_le_log_abs_add_three_of_one_add_le
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 + ε ≤ σ →
      0 ≤
        3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
        + 4 * (-deriv riemannZeta ((σ : ℂ) + I * t) /
            riemannZeta ((σ : ℂ) + I * t)).re
        + (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
            riemannZeta ((σ : ℂ) + 2 * I * t)).re ∧
      3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
        + 4 * (-deriv riemannZeta ((σ : ℂ) + I * t) /
            riemannZeta ((σ : ℂ) + I * t)).re
        + (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
            riemannZeta ((σ : ℂ) + 2 * I * t)).re
          ≤ C * Real.log (|t| + 3) := by
  rcases exists_re_neg_deriv_div_riemannZeta_fixed_margin_three_four_one_bounds
      hε with ⟨C₀, hC₀, hbounds⟩
  refine ⟨8 * C₀, mul_nonneg (by norm_num) hC₀, ?_⟩
  intro σ t hσ
  have hσ_gt : 1 < σ := by linarith
  rcases hbounds σ t hσ with ⟨h0, h1, h2⟩
  constructor
  · exact log_deriv_zeta_nonneg_combination σ hσ_gt t
  · have hupper :
        3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
          + 4 * (-deriv riemannZeta ((σ : ℂ) + I * t) /
              riemannZeta ((σ : ℂ) + I * t)).re
          + (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
              riemannZeta ((σ : ℂ) + 2 * I * t)).re
            ≤ 3 * (C₀ * Real.log (|t| + 3))
              + 4 * (C₀ * Real.log (|t| + 3))
              + C₀ * Real.log (|t| + 3) := by
      nlinarith
    calc
      3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
          + 4 * (-deriv riemannZeta ((σ : ℂ) + I * t) /
              riemannZeta ((σ : ℂ) + I * t)).re
          + (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
              riemannZeta ((σ : ℂ) + 2 * I * t)).re
          ≤ 3 * (C₀ * Real.log (|t| + 3))
              + 4 * (C₀ * Real.log (|t| + 3))
              + C₀ * Real.log (|t| + 3) := hupper
      _ = (8 * C₀) * Real.log (|t| + 3) := by ring

/-- ζ is nonzero in a full neighborhood of `1`.

Although `riemannZeta` has a junk value at `1` in Mathlib, the residue statement
gives nonvanishing on a punctured neighborhood, and `riemannZeta_one_ne_zero`
handles the point itself. -/
private lemma eventually_riemannZeta_ne_zero_nhds_one :
    ∀ᶠ s : ℂ in 𝓝 (1 : ℂ), riemannZeta s ≠ 0 := by
  have hpunct : ∀ᶠ s : ℂ in 𝓝[≠] (1 : ℂ), (s - 1) * riemannZeta s ≠ 0 := by
    have hopen : IsOpen ({z : ℂ | z ≠ 0}) := isOpen_compl_singleton
    exact riemannZeta_residue_one.eventually (hopen.mem_nhds one_ne_zero)
  rw [eventually_nhdsWithin_iff] at hpunct
  filter_upwards [hpunct] with s hs
  by_cases hs1 : s = 1
  · simp [hs1, riemannZeta_one_ne_zero]
  · exact fun hz ↦ hs hs1 (by simp [hz])

/-- The nonvanishing locus of ζ is open. -/
private lemma isOpen_setOf_riemannZeta_ne_zero : IsOpen {s : ℂ | riemannZeta s ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  intro s hs
  by_cases hs1 : s = 1
  · simpa [hs1] using eventually_riemannZeta_ne_zero_nhds_one
  · exact (differentiableAt_riemannZeta hs1).continuousAt.preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds hs)

/-- Compact zero-free region next to the line `Re(s) = 1`.

For fixed height `T`, compactness of the vertical segment
`{s | s.re = 1 ∧ |s.im| ≤ T}` and openness of the nonvanishing locus give a
uniform closed thickening inside the nonvanishing locus. Points with `re ≥ 1`
are handled directly by `riemannZeta_ne_zero_of_one_le_re`; points with
`1 - d ≤ re < 1` lie in that thickening by vertical projection. -/
theorem classical_zero_free_region_compact (T : ℝ) (_hT : T ≥ 2) :
    ∃ d > 0, ∀ s : ℂ, |s.im| ≤ T → s.re ≥ 1 - d → riemannZeta s ≠ 0 := by
  let verticalSegment : Set ℂ := ({1} : Set ℝ) ×ℂ Set.Icc (-T) T
  have hK : IsCompact verticalSegment := by
    simpa [verticalSegment] using
      (isCompact_singleton.reProdIm (isCompact_Icc : IsCompact (Set.Icc (-T) T)))
  have hKsub : verticalSegment ⊆ {s : ℂ | riemannZeta s ≠ 0} := by
    intro z hz
    change z ∈ ({1} : Set ℝ) ×ℂ Set.Icc (-T) T at hz
    rw [mem_reProdIm] at hz
    have hzre : z.re = 1 := by simpa using hz.1
    exact riemannZeta_ne_zero_of_one_le_re (by linarith)
  obtain ⟨d, hdpos, hdsub⟩ :=
    hK.exists_cthickening_subset_open isOpen_setOf_riemannZeta_ne_zero hKsub
  refine ⟨d, hdpos, ?_⟩
  intro s him hsre
  by_cases hge : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hge
  · have hlt : s.re < 1 := lt_of_not_ge hge
    let k : ℂ := ⟨1, s.im⟩
    have hk : k ∈ verticalSegment := by
      change k ∈ ({1} : Set ℝ) ×ℂ Set.Icc (-T) T
      rw [mem_reProdIm]
      constructor
      · simp [k]
      · simpa [k] using (abs_le.mp him)
    have hdist : dist s k ≤ d := by
      have hdist' : dist s k ≤ |s.re - 1| := by
        calc
          dist s k = ‖s - k‖ := dist_eq_norm s k
          _ ≤ |(s - k).re| + |(s - k).im| := norm_le_abs_re_add_abs_im _
          _ = |s.re - 1| := by simp [k]
      have habs : |s.re - 1| ≤ d := by
        rw [abs_of_nonpos (by linarith)]
        linarith
      exact hdist'.trans habs
    exact hdsub (Metric.mem_cthickening_of_dist_le s k d verticalSegment hk hdist)

lemma classical_zero_free_region_compact_at_two :
    ∃ d > 0, ∀ s : ℂ, |s.im| ≤ 2 →
      s.re ≥ 1 - d → riemannZeta s ≠ 0 :=
  classical_zero_free_region_compact 2 (by norm_num)

lemma classical_zero_free_region_compact_re_im (T : ℝ) (hT : T ≥ 2) :
    ∃ d > 0, ∀ β t : ℝ, |t| ≤ T →
      β ≥ 1 - d → riemannZeta ((β : ℂ) + I * t) ≠ 0 := by
  rcases classical_zero_free_region_compact T hT with ⟨d, hd_pos, hcompact⟩
  refine ⟨d, hd_pos, ?_⟩
  intro β t ht hβ
  have hheight : |((β : ℂ) + I * t).im| ≤ T := by
    simpa using ht
  have hre : ((β : ℂ) + I * t).re ≥ 1 - d := by
    simpa using hβ
  exact hcompact ((β : ℂ) + I * t) hheight hre

lemma classical_zero_free_region_compact_band_re_im (T : ℝ) (hT : T ≥ 2) :
    ∃ d > 0, ∀ β t : ℝ, 2 ≤ |t| → |t| ≤ T →
      β ≥ 1 - d → riemannZeta ((β : ℂ) + I * t) ≠ 0 := by
  rcases classical_zero_free_region_compact_re_im T hT with ⟨d, hd_pos, hcompact⟩
  refine ⟨d, hd_pos, ?_⟩
  intro β t _ht_lower ht_upper hβ
  exact hcompact β t ht_upper hβ

/-- 经典零点自由区域：ζ(s) ≠ 0 对于 Re(s) ≥ 1 - c/log|t| (|t| ≥ 2)。
    这还需要把 Hadamard 因子分解或 Borel-Carathéodory 等复分析工具
    专门应用到 ζ 的增长估计和对数导数估计上。 -/
def classical_zero_free_region : Prop :=
    ∃ c > 0, ∀ s : ℂ, |s.im| ≥ 2 → s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0

/-- Coordinate form of the classical zero-free-region target. -/
lemma classical_zero_free_region_iff_re_im :
    classical_zero_free_region ↔
      ∃ c > 0, ∀ β t : ℝ, 2 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + I * t) ≠ 0 := by
  constructor
  · intro hclassical
    rcases hclassical with ⟨c, hc_pos, hregion⟩
    refine ⟨c, hc_pos, ?_⟩
    intro β t ht hβ
    have hheight : |((β : ℂ) + I * t).im| ≥ 2 := by
      simpa using ht
    have hre :
        ((β : ℂ) + I * t).re ≥ 1 - c / Real.log |((β : ℂ) + I * t).im| := by
      simpa using hβ
    exact hregion ((β : ℂ) + I * t) hheight hre
  · intro hcoord
    rcases hcoord with ⟨c, hc_pos, hregion⟩
    refine ⟨c, hc_pos, ?_⟩
    intro s hsheight hsre
    have hs_decomp : ((s.re : ℂ) + I * s.im) = s := by
      apply Complex.ext <;> simp
    simpa [hs_decomp] using hregion s.re s.im hsheight hsre

lemma classical_zero_free_region_to_re_im
    (hclassical : classical_zero_free_region) :
    ∃ c > 0, ∀ β t : ℝ, 2 ≤ |t| →
      β ≥ 1 - c / Real.log |t| →
      riemannZeta ((β : ℂ) + I * t) ≠ 0 :=
  classical_zero_free_region_iff_re_im.mp hclassical

lemma classical_zero_free_region_of_re_im
    (hcoord :
      ∃ c > 0, ∀ β t : ℝ, 2 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + I * t) ≠ 0) :
    classical_zero_free_region :=
  classical_zero_free_region_iff_re_im.mpr hcoord

/-- `log |t|` is positive throughout the classical zero-free-region range. -/
lemma log_abs_pos_of_two_le {t : ℝ} (ht : 2 ≤ |t|) : 0 < Real.log |t| :=
  Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) ht)

/-- The classical `c / log |t|` width is positive in its height range. -/
lemma classical_width_pos_of_two_le {c t : ℝ} (hc : 0 < c) (ht : 2 ≤ |t|) :
    0 < c / Real.log |t| :=
  div_pos hc (log_abs_pos_of_two_le ht)

/-- The classical `c / log |t|` width is monotone in the width constant. -/
lemma classical_width_mono_const {csmall clarge t : ℝ}
    (hc : csmall ≤ clarge) (ht : 2 ≤ |t|) :
    csmall / Real.log |t| ≤ clarge / Real.log |t| :=
  div_le_div_of_nonneg_right hc (log_abs_pos_of_two_le ht).le

/-- The standard high-height choice `σ = 1 + a / log |t|` lies to the right of
the pole line when `a > 0`. -/
lemma sigmaOf_log_gt_one {T0 a t : ℝ} (hT0 : 2 ≤ T0) (ha : 0 < a)
    (ht : T0 ≤ |t|) :
    1 < 1 + a / Real.log |t| := by
  have hlog_pos : 0 < Real.log |t| := log_abs_pos_of_two_le (hT0.trans ht)
  have hwidth_pos : 0 < a / Real.log |t| := div_pos ha hlog_pos
  linarith

/-- If `a ≤ log 2`, then the standard high-height choice
`σ = 1 + a / log |t|` remains at most `2` throughout any range
`T0 ≤ |t|` with `T0 ≥ 2`. -/
lemma sigmaOf_log_le_two {T0 a t : ℝ} (hT0 : 2 ≤ T0)
    (ha_le : a ≤ Real.log 2) (ht : T0 ≤ |t|) :
    1 + a / Real.log |t| ≤ 2 := by
  have ht2 : 2 ≤ |t| := hT0.trans ht
  have hlog_pos : 0 < Real.log |t| := log_abs_pos_of_two_le ht2
  have hlog_mono : Real.log (2 : ℝ) ≤ Real.log |t| :=
    Real.log_le_log (by norm_num) ht2
  have ha_le_log : a ≤ Real.log |t| := le_trans ha_le hlog_mono
  have hdiv_le : a / Real.log |t| ≤ 1 := by
    exact (div_le_iff₀ hlog_pos).mpr (by simpa using ha_le_log)
  linarith

/-- The standard high-height choice `σ = 1 + a / log |t|` stays strictly to
the right of every `β < 1`.  This is the `hσ_sub_pos` real-variable input
used by the 3-4-1 contradiction. -/
lemma sigmaOf_log_sub_pos {T0 a β t : ℝ} (hT0 : 2 ≤ T0) (ha : 0 < a)
    (ht : T0 ≤ |t|) (hβ_lt : β < 1) :
    0 < (1 + a / Real.log |t|) - β := by
  have hσ_gt : 1 < 1 + a / Real.log |t| :=
    sigmaOf_log_gt_one hT0 ha ht
  linarith

/-- A local right-neighborhood condition for the standard choice
`σ = 1 + a / log |t|`.

If `a ≤ d log 2`, then `σ ≤ 1 + d` in every height range above `2`.
This is the bridge needed to use local pole estimates whose hypotheses are
phrased as `σ ≤ 1 + d`. -/
lemma sigmaOf_log_le_one_add {T0 a d t : ℝ} (hT0 : 2 ≤ T0)
    (ha_le : a ≤ d * Real.log 2) (hd : 0 ≤ d) (ht : T0 ≤ |t|) :
    1 + a / Real.log |t| ≤ 1 + d := by
  have ht2 : 2 ≤ |t| := hT0.trans ht
  have hlog_pos : 0 < Real.log |t| := log_abs_pos_of_two_le ht2
  have hlog_mono : Real.log (2 : ℝ) ≤ Real.log |t| :=
    Real.log_le_log (by norm_num) ht2
  have ha_le_dlog : a ≤ d * Real.log |t| :=
    le_trans ha_le (mul_le_mul_of_nonneg_left hlog_mono hd)
  have hdiv_le : a / Real.log |t| ≤ d := by
    exact (div_le_iff₀ hlog_pos).mpr ha_le_dlog
  linarith

/-- Pure real-variable negativity margin for the standard high-height choice
`σ = 1 + a / log |t|`.

If the zero term is bounded by `-1 / (σ - β) + Czero log |t|`, the real-axis
term by `Creal log |t| / a`, and the `σ + 2it` term by `Ctwo log |t|`, then
the 3-4-1 upper bound is strictly negative whenever
`3*Creal/a + 4*Czero + Ctwo < 4/(a+c)` and
`β ≥ 1 - c / log |t|`. -/
lemma three_four_one_sigmaOf_log_margin
    {T0 a c Creal Czero Ctwo β t : ℝ}
    (hT0 : 2 ≤ T0) (ha : 0 < a) (hc : 0 < c)
    (ht : T0 ≤ |t|) (hβ_lt : β < 1)
    (hβ : β ≥ 1 - c / Real.log |t|)
    (hconst : 3 * Creal / a + 4 * Czero + Ctwo < 4 / (a + c)) :
    3 * (Creal * Real.log |t| / a)
      + 4 * (-1 / ((1 + a / Real.log |t|) - β) +
          Czero * Real.log |t|)
      + Ctwo * Real.log |t| < 0 := by
  have hlog_pos : 0 < Real.log |t| :=
    log_abs_pos_of_two_le (hT0.trans ht)
  have hden_pos : 0 < (1 + a / Real.log |t|) - β :=
    sigmaOf_log_sub_pos hT0 ha ht hβ_lt
  have hac_pos : 0 < a + c := add_pos ha hc
  have hβ_mul : Real.log |t| - c ≤ β * Real.log |t| := by
    have hmul := mul_le_mul_of_nonneg_right hβ hlog_pos.le
    field_simp [hlog_pos.ne'] at hmul
    simpa [mul_comm] using hmul
  have hden_le : (1 + a / Real.log |t|) - β ≤ (a + c) / Real.log |t| := by
    field_simp [hlog_pos.ne']
    nlinarith [hβ_mul]
  have hinv :
      -1 / ((1 + a / Real.log |t|) - β) ≤
        -Real.log |t| / (a + c) := by
    have hrec :
        1 / ((a + c) / Real.log |t|) ≤
          1 / ((1 + a / Real.log |t|) - β) :=
      one_div_le_one_div_of_le hden_pos hden_le
    have heq :
        1 / ((a + c) / Real.log |t|) = Real.log |t| / (a + c) := by
      field_simp [hlog_pos.ne', hac_pos.ne']
    rw [heq] at hrec
    have hneg := neg_le_neg hrec
    simpa [neg_div] using hneg
  have hupper :
      3 * (Creal * Real.log |t| / a)
        + 4 * (-1 / ((1 + a / Real.log |t|) - β) +
            Czero * Real.log |t|)
        + Ctwo * Real.log |t| ≤
      3 * (Creal * Real.log |t| / a)
        + 4 * (-Real.log |t| / (a + c) +
            Czero * Real.log |t|)
        + Ctwo * Real.log |t| := by
    nlinarith
  have hconst_neg :
      (3 * Creal / a + 4 * Czero + Ctwo - 4 / (a + c)) *
        Real.log |t| < 0 := by
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hconst) hlog_pos
  have hright :
      3 * (Creal * Real.log |t| / a)
        + 4 * (-Real.log |t| / (a + c) +
            Czero * Real.log |t|)
        + Ctwo * Real.log |t| < 0 := by
    have heq :
        3 * (Creal * Real.log |t| / a)
          + 4 * (-Real.log |t| / (a + c) +
              Czero * Real.log |t|)
          + Ctwo * Real.log |t| =
        (3 * Creal / a + 4 * Czero + Ctwo - 4 / (a + c)) *
          Real.log |t| := by
      field_simp [ha.ne', hac_pos.ne']
      ring
    rw [heq]
    exact hconst_neg
  exact lt_of_le_of_lt hupper hright

/-- If the `σ + 2it` estimate still has the same `1/a` pole-loss as the
real-axis estimate, the standard 3-4-1 margin cannot close.

This records the precise obstruction for the weak bound obtained from the
half-plane L-series triangle inequality: even before adding any nonnegative
regular-part contribution, coefficients `Creal ≥ 1` and `Ctwo ≥ 1` force the
left side of the required constant inequality to be at least `4/a`, whereas
`4/(a+c) < 4/a` for every positive strip width `c`. -/
lemma sigmaOf_log_weak_two_t_margin_impossible
    {a c Creal Czero Ctwo : ℝ}
    (ha : 0 < a) (hc : 0 < c)
    (hCreal : 1 ≤ Creal) (hCzero : 0 ≤ Czero) (hCtwo : 1 ≤ Ctwo) :
    ¬ (3 * Creal / a + 4 * Czero + Ctwo / a < 4 / (a + c)) := by
  intro hmargin
  have hac_pos : 0 < a + c := add_pos ha hc
  have hright_lt : 4 / (a + c) < 4 / a := by
    exact div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 4) ha
      (by linarith)
  have hleft_ge : 4 / a ≤ 3 * Creal / a + 4 * Czero + Ctwo / a := by
    have h3 : 3 / a ≤ 3 * Creal / a := by
      exact div_le_div_of_nonneg_right (by nlinarith : 3 ≤ 3 * Creal) ha.le
    have htwo : 1 / a ≤ Ctwo / a := by
      exact div_le_div_of_nonneg_right hCtwo ha.le
    have hzero : 0 ≤ 4 * Czero := by nlinarith
    have hsplit : 4 / a = 3 / a + 1 / a := by ring
    linarith
  linarith

/-- Existential form of `sigmaOf_log_weak_two_t_margin_impossible`.

If both the real-axis and weak `σ + 2it` coefficients are at least one, no
positive choice of the standard constants `a,c` can satisfy the 3-4-1 margin
with a `Ctwo/a` third term. -/
lemma no_sigmaOf_log_margin_constants_with_weak_two_t
    {Creal Czero Ctwo : ℝ}
    (hCreal : 1 ≤ Creal) (hCzero : 0 ≤ Czero) (hCtwo : 1 ≤ Ctwo) :
    ¬ ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      3 * Creal / a + 4 * Czero + Ctwo / a < 4 / (a + c) := by
  rintro ⟨a, c, ha, hc, hmargin⟩
  exact sigmaOf_log_weak_two_t_margin_impossible
    ha hc hCreal hCzero hCtwo hmargin

/-- Same obstruction when both shifted terms are controlled only at the weak
`Cshift/a` scale.

This is the constant-level boundary for the shared weak moving-strip package:
if the `σ+it` and `σ+2it` terms both carry the same `1/a` loss, then their
combined coefficient already overwhelms the `4/(a+c)` margin available from the
zero-repulsion term. -/
lemma sigmaOf_log_weak_shift_pair_margin_impossible
    {a c Creal Cshift : ℝ}
    (ha : 0 < a) (hc : 0 < c)
    (hCreal : 1 ≤ Creal) (hCshift : 1 ≤ Cshift) :
    ¬ (3 * Creal / a + 5 * (Cshift / a) < 4 / (a + c)) := by
  intro hmargin
  have hright_lt : 4 / (a + c) < 4 / a := by
    exact div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 4) ha
      (by linarith)
  have hleft_ge : 4 / a ≤ 3 * Creal / a + 5 * (Cshift / a) := by
    have h3 : 3 / a ≤ 3 * Creal / a := by
      exact div_le_div_of_nonneg_right (by nlinarith : 3 ≤ 3 * Creal) ha.le
    have h1_shift : 1 / a ≤ Cshift / a := by
      exact div_le_div_of_nonneg_right hCshift ha.le
    have hshift_nonneg : 0 ≤ Cshift / a :=
      div_nonneg (by linarith) ha.le
    have hshift_five : Cshift / a ≤ 5 * (Cshift / a) := by
      nlinarith
    have hsplit : 4 / a = 3 / a + 1 / a := by ring
    linarith
  linarith

/-- Existential form of
`sigmaOf_log_weak_shift_pair_margin_impossible`. -/
lemma no_sigmaOf_log_margin_constants_with_weak_shift_pair
    {Creal Cshift : ℝ}
    (hCreal : 1 ≤ Creal) (hCshift : 1 ≤ Cshift) :
    ¬ ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      3 * Creal / a + 5 * (Cshift / a) < 4 / (a + c) := by
  rintro ⟨a, c, ha, hc, hmargin⟩
  exact sigmaOf_log_weak_shift_pair_margin_impossible
    ha hc hCreal hCshift hmargin

/-- Pure real-variable choice of the small constants in the standard
`σ = 1 + a / log |t|` setup.

For any real-axis coefficient `C < 4/3` and any nonnegative shifted-remainder
constant `K`, one can choose positive `a` and `c`, with `a` small enough to
fit the local pole-neighborhood constraints, so that the 3-4-1 margin
inequality `3*C/a + K < 4/(a+c)` holds. -/
lemma exists_sigmaOf_log_margin_constants
    {C K d : ℝ} (hC_pos : 1 < C) (hC_lt : C < 4 / 3)
    (hK : 0 ≤ K) (hd : 0 < d) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      a ≤ Real.log 2 ∧ a ≤ d * Real.log 2 ∧
      3 * C / a + K < 4 / (a + c) := by
  let delta : ℝ := 4 - 3 * C
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    nlinarith
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hdlog_pos : 0 < d * Real.log (2 : ℝ) :=
    mul_pos hd hlog2_pos
  have hK1_pos : 0 < K + 1 := by linarith
  let A : ℝ := delta / (4 * (K + 1))
  have hA_pos : 0 < A := by
    dsimp [A]
    exact div_pos hdelta_pos (mul_pos (by norm_num) hK1_pos)
  let a : ℝ := min (Real.log (2 : ℝ)) (min (d * Real.log (2 : ℝ)) A)
  have ha_pos : 0 < a := by
    dsimp [a]
    exact lt_min hlog2_pos (lt_min hdlog_pos hA_pos)
  have ha_le_log2 : a ≤ Real.log (2 : ℝ) := by
    dsimp [a]
    exact min_le_left _ _
  have ha_le_dlog : a ≤ d * Real.log (2 : ℝ) := by
    dsimp [a]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have ha_le_A : a ≤ A := by
    dsimp [a]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  let c : ℝ := a * delta / 8
  have hc_pos : 0 < c := by
    dsimp [c]
    exact div_pos (mul_pos ha_pos hdelta_pos) (by norm_num)
  have hKa_le : K * a ≤ delta / 4 := by
    have hKa_le_A : K * a ≤ K * A :=
      mul_le_mul_of_nonneg_left ha_le_A hK
    have hKA_le : K * A ≤ delta / 4 := by
      have hK_le_K1 : K ≤ K + 1 := by linarith
      have hfrac_le : K / (K + 1) ≤ 1 :=
        (div_le_one hK1_pos).mpr hK_le_K1
      calc
        K * A = delta / 4 * (K / (K + 1)) := by
          dsimp [A]
          field_simp [hK1_pos.ne']
        _ ≤ delta / 4 * 1 :=
            mul_le_mul_of_nonneg_left hfrac_le (by positivity)
        _ = delta / 4 := by ring
    exact le_trans hKa_le_A hKA_le
  have hleft_bound : 3 * C + K * a ≤ 4 - 3 * delta / 4 := by
    dsimp [delta] at hdelta_pos ⊢
    nlinarith [hKa_le]
  have hfac_pos : 0 < 1 + delta / 8 := by positivity
  have hright_lower : 4 - delta / 2 ≤ 4 / (1 + delta / 8) := by
    rw [le_div_iff₀ hfac_pos]
    nlinarith [sq_nonneg delta]
  have hright_eq : 4 * a / (a + c) = 4 / (1 + delta / 8) := by
    dsimp [c]
    field_simp [ha_pos.ne', hfac_pos.ne']
  have hmain_num : 3 * C + K * a < 4 * a / (a + c) := by
    rw [hright_eq]
    have hstrict : 4 - 3 * delta / 4 < 4 - delta / 2 := by
      nlinarith [hdelta_pos]
    exact lt_of_le_of_lt hleft_bound (lt_of_lt_of_le hstrict hright_lower)
  have htarget : 3 * C / a + K < 4 / (a + c) := by
    have hmul :
        a * (3 * C / a + K) < a * (4 / (a + c)) := by
      calc
        a * (3 * C / a + K) = 3 * C + K * a := by
          field_simp [ha_pos.ne']
        _ < 4 * a / (a + c) := hmain_num
        _ = a * (4 / (a + c)) := by ring
    exact lt_of_mul_lt_mul_left hmul ha_pos.le
  exact ⟨a, c, ha_pos, hc_pos, ha_le_log2, ha_le_dlog, htarget⟩

/-- Specialized constant choice for the usual shifted-estimate shape.

If the real-axis coefficient satisfies `1 < C < 4/3` and the two remaining
shifted-estimate coefficients are nonnegative, then one can choose positive
`a,c`, with `a` small enough for the local pole-neighborhood constraints, so
that the exact margin used by `three_four_one_sigmaOf_log_margin` holds. -/
lemma exists_sigmaOf_log_margin_constants_for_shift_bounds
    {C Czero Ctwo d : ℝ} (hC_pos : 1 < C) (hC_lt : C < 4 / 3)
    (hCzero : 0 ≤ Czero) (hCtwo : 0 ≤ Ctwo) (hd : 0 < d) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      a ≤ Real.log 2 ∧ a ≤ d * Real.log 2 ∧
      3 * C / a + 4 * Czero + Ctwo < 4 / (a + c) := by
  have hK : 0 ≤ 4 * Czero + Ctwo := by nlinarith
  rcases exists_sigmaOf_log_margin_constants (C := C)
      (K := 4 * Czero + Ctwo) (d := d) hC_pos hC_lt hK hd with
    ⟨a, c, ha_pos, hc_pos, ha_le_log2, ha_le_dlog, hmargin⟩
  exact ⟨a, c, ha_pos, hc_pos, ha_le_log2, ha_le_dlog, by
    simpa [add_assoc] using hmargin⟩

/-- Same-constant specialization of the standard margin constant choice.

This is the real-variable constant package used by the same-coefficient
shifted-estimate closures, where both remaining logarithmic estimates are
bounded by the same nonnegative coefficient `B`. -/
lemma exists_sigmaOf_log_margin_constants_same_const
    {C B d : ℝ} (hC_pos : 1 < C) (hC_lt : C < 4 / 3)
    (hB : 0 ≤ B) (hd : 0 < d) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      a ≤ Real.log 2 ∧ a ≤ d * Real.log 2 ∧
      3 * C / a + 5 * B < 4 / (a + c) := by
  rcases exists_sigmaOf_log_margin_constants_for_shift_bounds
      (C := C) (Czero := B) (Ctwo := B) (d := d)
      hC_pos hC_lt hB hB hd with
    ⟨a, c, ha_pos, hc_pos, ha_le_log2, ha_le_dlog, hmargin⟩
  have hmargin' : 3 * C / a + 5 * B < 4 / (a + c) := by
    have heq : 3 * C / a + 4 * B + B = 3 * C / a + 5 * B := by ring
    rwa [heq] at hmargin
  exact ⟨a, c, ha_pos, hc_pos, ha_le_log2, ha_le_dlog, hmargin'⟩

/-- Above height `3`, `log |t|` is already larger than `1`. -/
lemma log_abs_gt_one_of_three_le {t : ℝ} (ht : 3 ≤ |t|) :
    1 < Real.log |t| := by
  have ht_pos : 0 < |t| := by linarith
  have hexp_lt_three : Real.exp 1 < (3 : ℝ) := by
    calc
      Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ < (3 : ℝ) := by norm_num
  exact (Real.lt_log_iff_exp_lt ht_pos).mpr (lt_of_lt_of_le hexp_lt_three ht)

/-- Above height `3`, the log-log factor in the Vinogradov-Korobov width is positive. -/
lemma log_log_abs_pos_of_three_le {t : ℝ} (ht : 3 ≤ |t|) :
    0 < Real.log (Real.log |t|) :=
  Real.log_pos (log_abs_gt_one_of_three_le ht)

/-- The vertical region used by local zero-free-region estimates: real part in
`[a,b]` and imaginary height at least `H`. -/
def verticalRegion (a b H : ℝ) : Set ℂ :=
  {z : ℂ | z.re ∈ Set.Icc a b ∧ H ≤ |z.im|}

lemma mem_verticalRegion {z : ℂ} {a b H : ℝ} :
    z ∈ verticalRegion a b H ↔ z.re ∈ Set.Icc a b ∧ H ≤ |z.im| :=
  Iff.rfl

/-- A positive-height vertical region excludes the pole `1`. -/
lemma one_not_mem_verticalRegion_of_pos_height {a b H : ℝ} (hH : 0 < H) :
    (1 : ℂ) ∉ verticalRegion a b H := by
  intro h
  have hheight : H ≤ |(1 : ℂ).im| := h.2
  simpa using lt_of_lt_of_le hH hheight

/-- Any point in a positive-height vertical region is different from the pole
`1`. -/
lemma ne_one_of_mem_verticalRegion_of_pos_height {z : ℂ} {a b H : ℝ}
    (hz : z ∈ verticalRegion a b H) (hH : 0 < H) :
    z ≠ 1 := by
  intro hz1
  exact one_not_mem_verticalRegion_of_pos_height (a := a) (b := b) hH
    (by simpa [hz1] using hz)

/-- ζ is differentiable on every positive-height vertical region, since such a
region avoids the pole at `1`. -/
lemma differentiableOn_riemannZeta_verticalRegion_of_pos_height
    {a b H : ℝ} (hH : 0 < H) :
    DifferentiableOn ℂ riemannZeta (verticalRegion a b H) := by
  intro z hz
  exact (differentiableAt_riemannZeta
    (ne_one_of_mem_verticalRegion_of_pos_height hz hH)).differentiableWithinAt

lemma re_im_decomp (s : ℂ) : ((s.re : ℂ) + I * s.im) = s := by
  apply Complex.ext <;> simp

/-- The real-coordinate displacement is bounded by the complex norm. -/
lemma abs_re_sub_le_norm_sub (z c : ℂ) : |z.re - c.re| ≤ ‖z - c‖ := by
  simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - c)

/-- The imaginary-coordinate displacement is bounded by the complex norm. -/
lemma abs_im_sub_le_norm_sub (z c : ℂ) : |z.im - c.im| ≤ ‖z - c‖ := by
  have h := Complex.abs_re_le_norm (I * (z - c))
  simpa [Complex.mul_re, Complex.norm_I, Complex.norm_mul, Complex.sub_im,
    abs_sub_comm z.im c.im] using h

/-- Real-coordinate bounds for a point in a closed complex ball. -/
lemma closedBall_re_bounds {z c : ℂ} {R : ℝ}
    (hz : z ∈ Metric.closedBall c R) :
    c.re - R ≤ z.re ∧ z.re ≤ c.re + R := by
  have hdist : ‖z - c‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hre : |z.re - c.re| ≤ R :=
    le_trans (abs_re_sub_le_norm_sub z c) hdist
  constructor <;> linarith [abs_le.mp hre]

/-- Real-coordinate bounds for a point in an open complex ball. -/
lemma ball_re_bounds {z c : ℂ} {R : ℝ}
    (hz : z ∈ Metric.ball c R) :
    c.re - R ≤ z.re ∧ z.re ≤ c.re + R := by
  exact closedBall_re_bounds
    (Metric.ball_subset_closedBall hz)

/-- Imaginary height lower bound for a point in a closed complex ball. -/
lemma closedBall_abs_im_lower {z c : ℂ} {R : ℝ}
    (hz : z ∈ Metric.closedBall c R) :
    |c.im| - R ≤ |z.im| := by
  have hdist : ‖z - c‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have him : |z.im - c.im| ≤ R :=
    le_trans (abs_im_sub_le_norm_sub z c) hdist
  have htri : |c.im| ≤ |z.im| + |z.im - c.im| := by
    calc
      |c.im| = |z.im - (z.im - c.im)| := by ring_nf
      _ ≤ |z.im| + |z.im - c.im| := by
        simpa [abs_sub_comm c.im z.im] using abs_sub_le z.im 0 (z.im - c.im)
  linarith

/-- Imaginary height lower bound for a point in an open complex ball. -/
lemma ball_abs_im_lower {z c : ℂ} {R : ℝ}
    (hz : z ∈ Metric.ball c R) :
    |c.im| - R ≤ |z.im| := by
  exact closedBall_abs_im_lower
    (Metric.ball_subset_closedBall hz)

/-- If the center of a closed ball is high enough, every point in the ball
stays above the requested imaginary-height threshold. -/
lemma closedBall_abs_im_ge_of_add_le {z c : ℂ} {R H : ℝ}
    (hz : z ∈ Metric.closedBall c R) (hH : H + R ≤ |c.im|) :
    H ≤ |z.im| := by
  have h := closedBall_abs_im_lower (z := z) (c := c) (R := R) hz
  linarith

/-- If the center of an open ball is high enough, every point in the ball
stays above the requested imaginary-height threshold. -/
lemma ball_abs_im_ge_of_add_le {z c : ℂ} {R H : ℝ}
    (hz : z ∈ Metric.ball c R) (hH : H + R ≤ |c.im|) :
    H ≤ |z.im| := by
  exact closedBall_abs_im_ge_of_add_le
    (Metric.ball_subset_closedBall hz) hH

/-- Real-coordinate bounds in a closed ball centered at `σ + I*t`. -/
lemma closedBall_sigma_it_re_bounds {z : ℂ} {σ t R : ℝ}
    (hz : z ∈ Metric.closedBall ((σ : ℂ) + I * t) R) :
    σ - R ≤ z.re ∧ z.re ≤ σ + R := by
  have h := closedBall_re_bounds (z := z) (c := (σ : ℂ) + I * t) (R := R) hz
  simpa using h

/-- Real-coordinate bounds in an open ball centered at `σ + I*t`. -/
lemma ball_sigma_it_re_bounds {z : ℂ} {σ t R : ℝ}
    (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R) :
    σ - R ≤ z.re ∧ z.re ≤ σ + R := by
  exact closedBall_sigma_it_re_bounds
    (Metric.ball_subset_closedBall hz)

/-- Height transfer in a closed ball centered at `σ + I*t`. -/
lemma closedBall_sigma_it_abs_im_ge_of_add_le {z : ℂ} {σ t R H : ℝ}
    (hz : z ∈ Metric.closedBall ((σ : ℂ) + I * t) R)
    (hH : H + R ≤ |t|) :
    H ≤ |z.im| := by
  exact closedBall_abs_im_ge_of_add_le
    (z := z) (c := (σ : ℂ) + I * t) (R := R) (H := H) hz
    (by simpa using hH)

/-- A closed disk centered at `σ + I*t` stays in the closed right half-plane
when its center is at least `R` to the right of the line `Re = 1`. -/
lemma closedBall_sigma_it_one_le_re_of_add_le {z : ℂ} {σ t R : ℝ}
    (hz : z ∈ Metric.closedBall ((σ : ℂ) + I * t) R)
    (hσ : 1 + R ≤ σ) :
    1 ≤ z.re := by
  have h := closedBall_sigma_it_re_bounds
    (z := z) (σ := σ) (t := t) (R := R) hz
  linarith

/-- A closed disk centered at high imaginary height avoids the pole `1`.
This is the pointwise form used when converting disk hypotheses into
right-half-plane logarithmic-derivative hypotheses. -/
lemma closedBall_sigma_it_ne_one_of_height_add_le {z : ℂ} {σ t R H : ℝ}
    (hz : z ∈ Metric.closedBall ((σ : ℂ) + I * t) R)
    (hHpos : 0 < H) (hH : H + R ≤ |t|) :
    z ≠ 1 := by
  have him : H ≤ |z.im| :=
    closedBall_sigma_it_abs_im_ge_of_add_le
      (z := z) (σ := σ) (t := t) (R := R) (H := H) hz hH
  intro hz1
  have hzero : H ≤ |(1 : ℂ).im| := by
    simpa [hz1] using him
  have hzero' : H ≤ 0 := by
    simpa using hzero
  linarith

/-- Height transfer in an open ball centered at `σ + I*t`. -/
lemma ball_sigma_it_abs_im_ge_of_add_le {z : ℂ} {σ t R H : ℝ}
    (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R)
    (hH : H + R ≤ |t|) :
    H ≤ |z.im| := by
  exact closedBall_sigma_it_abs_im_ge_of_add_le
    (Metric.ball_subset_closedBall hz) hH

/-- A closed disk centered at `σ + I*t` stays in a prescribed real strip when
the center is at least `R` away from both real-coordinate boundaries. -/
lemma closedBall_sigma_it_re_mem_Icc {z : ℂ} {σ t R a b : ℝ}
    (hz : z ∈ Metric.closedBall ((σ : ℂ) + I * t) R)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) :
    z.re ∈ Set.Icc a b := by
  have h := closedBall_sigma_it_re_bounds
    (z := z) (σ := σ) (t := t) (R := R) hz
  exact ⟨by linarith, by linarith⟩

/-- An open disk centered at `σ + I*t` stays in a prescribed real strip when
the center is at least `R` away from both real-coordinate boundaries. -/
lemma ball_sigma_it_re_mem_Icc {z : ℂ} {σ t R a b : ℝ}
    (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) :
    z.re ∈ Set.Icc a b :=
  closedBall_sigma_it_re_mem_Icc (Metric.ball_subset_closedBall hz) ha hb

/-- A closed disk centered at `σ + I*t` stays in a vertical region: real part in
`[a,b]` and imaginary height at least `H`. -/
lemma closedBall_sigma_it_mem_verticalRegion {z : ℂ} {σ t R a b H : ℝ}
    (hz : z ∈ Metric.closedBall ((σ : ℂ) + I * t) R)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|) :
    z.re ∈ Set.Icc a b ∧ H ≤ |z.im| :=
  ⟨closedBall_sigma_it_re_mem_Icc hz ha hb,
    closedBall_sigma_it_abs_im_ge_of_add_le hz hH⟩

/-- An open disk centered at `σ + I*t` stays in a vertical region: real part in
`[a,b]` and imaginary height at least `H`. -/
lemma ball_sigma_it_mem_verticalRegion {z : ℂ} {σ t R a b H : ℝ}
    (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|) :
    z.re ∈ Set.Icc a b ∧ H ≤ |z.im| :=
  closedBall_sigma_it_mem_verticalRegion
    (Metric.ball_subset_closedBall hz) ha hb hH

/-- Closed-disk inclusion into a vertical region around a `σ + I*t` center. -/
lemma closedBall_sigma_it_subset_verticalRegion {σ t R a b H : ℝ}
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|) :
    Metric.closedBall ((σ : ℂ) + I * t) R ⊆ verticalRegion a b H := by
  intro z hz
  exact closedBall_sigma_it_mem_verticalRegion hz ha hb hH

/-- Open-disk inclusion into a vertical region around a `σ + I*t` center. -/
lemma ball_sigma_it_subset_verticalRegion {σ t R a b H : ℝ}
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|) :
    Metric.ball ((σ : ℂ) + I * t) R ⊆ verticalRegion a b H := by
  intro z hz
  exact ball_sigma_it_mem_verticalRegion hz ha hb hH

/-- Translating a zero-centered closed disk by `σ + I*t` maps it into the
vertical region whenever the translated disk has the required strip and height
margins. -/
lemma mapsTo_add_closedBall_zero_sigma_it_verticalRegion {σ t R a b H : ℝ}
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|) :
    Set.MapsTo (fun w : ℂ => ((σ : ℂ) + I * t) + w)
      (Metric.closedBall 0 R) (verticalRegion a b H) := by
  intro w hw
  have hz : ((σ : ℂ) + I * t) + w ∈
      Metric.closedBall ((σ : ℂ) + I * t) R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  exact closedBall_sigma_it_subset_verticalRegion ha hb hH hz

/-- Translating a zero-centered open disk by `σ + I*t` maps it into the
vertical region whenever the translated disk has the required strip and height
margins. -/
lemma mapsTo_add_ball_zero_sigma_it_verticalRegion {σ t R a b H : ℝ}
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|) :
    Set.MapsTo (fun w : ℂ => ((σ : ℂ) + I * t) + w)
      (Metric.ball 0 R) (verticalRegion a b H) := by
  intro w hw
  have hz : ((σ : ℂ) + I * t) + w ∈
      Metric.ball ((σ : ℂ) + I * t) R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  exact ball_sigma_it_subset_verticalRegion ha hb hH hz

/-- A function differentiable on a vertical region is differentiable on any
open local disk contained in that region. -/
lemma differentiableOn_ball_sigma_it_of_differentiableOn_verticalRegion
    {f : ℂ → ℂ} {σ t R a b H : ℝ}
    (hf : DifferentiableOn ℂ f (verticalRegion a b H))
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|) :
    DifferentiableOn ℂ f (Metric.ball ((σ : ℂ) + I * t) R) :=
  hf.mono (ball_sigma_it_subset_verticalRegion ha hb hH)

/-- A function meromorphic on a vertical region is meromorphic on any closed
local disk contained in that region. -/
lemma meromorphicOn_closedBall_sigma_it_of_meromorphicOn_verticalRegion
    {f : ℂ → ℂ} {σ t R a b H : ℝ}
    (hf : MeromorphicOn f (verticalRegion a b H))
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|) :
    MeromorphicOn f (Metric.closedBall ((σ : ℂ) + I * t) R) := by
  intro z hz
  exact hf z (closedBall_sigma_it_subset_verticalRegion ha hb hH hz)

/-- Local namespace entry point for Mathlib's Borel-Carathéodory theorem in the
vanishing-at-zero form. This is one of the complex-analytic tools used in
standard proofs of quantitative zero-free regions; the remaining gap is the
zeta-specific growth/log-derivative input needed to apply it to `riemannZeta`. -/
lemma borelCaratheodory_zero
    {f : ℂ → ℂ} {M R : ℝ} {z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hf₁ : Set.MapsTo f (Metric.ball 0 R) {w | w.re ≤ M})
    (hR : 0 < R) (hz : z ∈ Metric.ball 0 R)
    (hf₂ : f 0 = 0) :
    ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) :=
  Complex.borelCaratheodory_zero hM hf hf₁ hR hz hf₂

/-- Local namespace entry point for Mathlib's general Borel-Carathéodory
theorem. -/
lemma borelCaratheodory
    {f : ℂ → ℂ} {M R : ℝ} {z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hf₁ : Set.MapsTo f (Metric.ball 0 R) {w | w.re ≤ M})
    (hR : 0 < R) (hz : z ∈ Metric.ball 0 R) :
    ‖f z‖ ≤
      2 * M * ‖z‖ / (R - ‖z‖) +
        ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) :=
  Complex.borelCaratheodory hM hf hf₁ hR hz

/-- Centered Borel-Carathéodory theorem in the vanishing-at-center form.

This is the disk-centered version needed when applying the theorem around
points such as `1 + I*t` rather than around `0`. -/
lemma borelCaratheodory_zero_centered
    {f : ℂ → ℂ} {M R : ℝ} {c z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball c R))
    (hf₁ : Set.MapsTo f (Metric.ball c R) {w | w.re ≤ M})
    (hR : 0 < R) (hz : z ∈ Metric.ball c R)
    (hf₂ : f c = 0) :
    ‖f z‖ ≤ 2 * M * ‖z - c‖ / (R - ‖z - c‖) := by
  let g : ℂ → ℂ := fun w => f (c + w)
  have hz0 : z - c ∈ Metric.ball 0 R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hgdiff : DifferentiableOn ℂ g (Metric.ball 0 R) := by
    intro w hw
    have hwc : c + w ∈ Metric.ball c R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hfd : DifferentiableAt ℂ f (c + w) :=
      hf.differentiableAt (Metric.isOpen_ball.mem_nhds hwc)
    exact (hfd.comp w (differentiableAt_id.const_add c)).differentiableWithinAt
  have hgmaps : Set.MapsTo g (Metric.ball 0 R) {w | w.re ≤ M} := by
    intro w hw
    have hwc : c + w ∈ Metric.ball c R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    exact hf₁ hwc
  have hgzero : g 0 = 0 := by simpa [g] using hf₂
  have h := borelCaratheodory_zero
    (f := g) hM hgdiff hgmaps hR hz0 hgzero
  simpa [g, add_sub_cancel_right] using h

/-- Centered Borel-Carathéodory theorem.

This translation wrapper avoids redoing the change of variables from a disk
centered at `c` to a disk centered at `0` in every future zeta-specific
application. -/
lemma borelCaratheodory_centered
    {f : ℂ → ℂ} {M R : ℝ} {c z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball c R))
    (hf₁ : Set.MapsTo f (Metric.ball c R) {w | w.re ≤ M})
    (hR : 0 < R) (hz : z ∈ Metric.ball c R) :
    ‖f z‖ ≤
      2 * M * ‖z - c‖ / (R - ‖z - c‖) +
        ‖f c‖ * (R + ‖z - c‖) / (R - ‖z - c‖) := by
  let g : ℂ → ℂ := fun w => f (c + w)
  have hz0 : z - c ∈ Metric.ball 0 R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hgdiff : DifferentiableOn ℂ g (Metric.ball 0 R) := by
    intro w hw
    have hwc : c + w ∈ Metric.ball c R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hfd : DifferentiableAt ℂ f (c + w) :=
      hf.differentiableAt (Metric.isOpen_ball.mem_nhds hwc)
    exact (hfd.comp w (differentiableAt_id.const_add c)).differentiableWithinAt
  have hgmaps : Set.MapsTo g (Metric.ball 0 R) {w | w.re ≤ M} := by
    intro w hw
    have hwc : c + w ∈ Metric.ball c R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    exact hf₁ hwc
  have h := borelCaratheodory
    (f := g) hM hgdiff hgmaps hR hz0
  simpa [g, add_sub_cancel_right] using h

/-- Half-radius corollary of centered Borel-Carathéodory.

Inside the disk of radius `R/2`, the standard rational factors are bounded by
absolute constants.  This is the form usually needed when local analytic
estimates reserve half of the disk radius for geometry. -/
lemma borelCaratheodory_centered_half_radius_bound
    {f : ℂ → ℂ} {M R : ℝ} {c z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball c R))
    (hf₁ : Set.MapsTo f (Metric.ball c R) {w | w.re ≤ M})
    (hR : 0 < R) (hz_half : ‖z - c‖ ≤ R / 2) :
    ‖f z‖ ≤ 2 * M + 3 * ‖f c‖ := by
  have hz_norm_nonneg : 0 ≤ ‖z - c‖ := norm_nonneg _
  have hz_lt : ‖z - c‖ < R := by linarith
  have hz_ball : z ∈ Metric.ball c R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz_lt
  have hbc := borelCaratheodory_centered hM hf hf₁ hR hz_ball
  have hden_pos : 0 < R - ‖z - c‖ := by linarith
  have hratio1 : ‖z - c‖ / (R - ‖z - c‖) ≤ 1 := by
    rw [div_le_one hden_pos]
    linarith
  have hratio2 : (R + ‖z - c‖) / (R - ‖z - c‖) ≤ 3 := by
    rw [div_le_iff₀ hden_pos]
    linarith
  have hterm1 :
      2 * M * ‖z - c‖ / (R - ‖z - c‖) ≤ 2 * M := by
    calc
      2 * M * ‖z - c‖ / (R - ‖z - c‖)
          = (2 * M) * (‖z - c‖ / (R - ‖z - c‖)) := by ring
      _ ≤ (2 * M) * 1 :=
          mul_le_mul_of_nonneg_left hratio1 (by nlinarith [hM.le])
      _ = 2 * M := by ring
  have hterm2 :
      ‖f c‖ * (R + ‖z - c‖) / (R - ‖z - c‖) ≤ 3 * ‖f c‖ := by
    calc
      ‖f c‖ * (R + ‖z - c‖) / (R - ‖z - c‖)
          = ‖f c‖ * ((R + ‖z - c‖) / (R - ‖z - c‖)) := by ring
      _ ≤ ‖f c‖ * 3 :=
          mul_le_mul_of_nonneg_left hratio2 (norm_nonneg _)
      _ = 3 * ‖f c‖ := by ring
  linarith

/-- Centered Borel-Carathéodory oscillation estimate.

This form bounds the change `f z - f c` directly from a real-part bound on the
same centered function.  It is the most convenient form for later regular-part
estimates where the value at the center is subtracted before applying
Borel-Carathéodory. -/
lemma borelCaratheodory_sub_centered
    {f : ℂ → ℂ} {M R : ℝ} {c z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball c R))
    (hf₁ : Set.MapsTo (fun w => f w - f c) (Metric.ball c R)
      {w | w.re ≤ M})
    (hR : 0 < R) (hz : z ∈ Metric.ball c R) :
    ‖f z - f c‖ ≤ 2 * M * ‖z - c‖ / (R - ‖z - c‖) := by
  have hgdiff : DifferentiableOn ℂ (fun w => f w - f c) (Metric.ball c R) := by
    intro w hw
    exact (hf w hw).sub (differentiableWithinAt_const (f c))
  have hgzero : (fun w => f w - f c) c = 0 := by simp
  exact borelCaratheodory_zero_centered hM hgdiff hf₁ hR hz hgzero

/-- Half-radius corollary of the centered oscillation Borel-Carathéodory
estimate.

On the half-radius subdisk, the factor `||z-c||/(R-||z-c||)` is at most `1`,
so the oscillation estimate has the clean bound `2*M`. -/
lemma borelCaratheodory_sub_centered_half_radius_bound
    {f : ℂ → ℂ} {M R : ℝ} {c z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball c R))
    (hf₁ : Set.MapsTo (fun w => f w - f c) (Metric.ball c R)
      {w | w.re ≤ M})
    (hR : 0 < R) (hz_half : ‖z - c‖ ≤ R / 2) :
    ‖f z - f c‖ ≤ 2 * M := by
  have hz_norm_nonneg : 0 ≤ ‖z - c‖ := norm_nonneg _
  have hz_lt : ‖z - c‖ < R := by linarith
  have hz_ball : z ∈ Metric.ball c R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz_lt
  have hbc := borelCaratheodory_sub_centered hM hf hf₁ hR hz_ball
  have hden_pos : 0 < R - ‖z - c‖ := by linarith
  have hratio : ‖z - c‖ / (R - ‖z - c‖) ≤ 1 := by
    rw [div_le_one hden_pos]
    linarith
  have hterm :
      2 * M * ‖z - c‖ / (R - ‖z - c‖) ≤ 2 * M := by
    calc
      2 * M * ‖z - c‖ / (R - ‖z - c‖)
          = (2 * M) * (‖z - c‖ / (R - ‖z - c‖)) := by ring
      _ ≤ (2 * M) * 1 :=
          mul_le_mul_of_nonneg_left hratio (by nlinarith [hM.le])
      _ = 2 * M := by ring
  exact le_trans hbc hterm

/-- Borel-Carathéodory on a disk centered at `σ + I*t`, with differentiability
and real-part control supplied on an ambient vertical region. -/
lemma borelCaratheodory_centered_verticalRegion
    {f : ℂ → ℂ} {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (verticalRegion a b H))
    (hf₁ : Set.MapsTo f (verticalRegion a b H) {w | w.re ≤ M})
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R) :
    ‖f z‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
          (R - ‖z - ((σ : ℂ) + I * t)‖) +
        ‖f ((σ : ℂ) + I * t)‖ *
          (R + ‖z - ((σ : ℂ) + I * t)‖) /
          (R - ‖z - ((σ : ℂ) + I * t)‖) := by
  have hfdisk :
      DifferentiableOn ℂ f (Metric.ball ((σ : ℂ) + I * t) R) :=
    differentiableOn_ball_sigma_it_of_differentiableOn_verticalRegion
      hf ha hb hH
  have hmaps :
      Set.MapsTo f (Metric.ball ((σ : ℂ) + I * t) R)
        {w | w.re ≤ M} := by
    intro w hw
    exact hf₁ (ball_sigma_it_subset_verticalRegion ha hb hH hw)
  exact borelCaratheodory_centered hM hfdisk hmaps hR hz

/-- Oscillation form of Borel-Carathéodory on a disk centered at `σ + I*t`,
with differentiability and real-part control supplied on an ambient vertical
region. -/
lemma borelCaratheodory_sub_centered_verticalRegion
    {f : ℂ → ℂ} {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (verticalRegion a b H))
    (hf₁ : Set.MapsTo
      (fun w => f w - f ((σ : ℂ) + I * t))
      (verticalRegion a b H) {w | w.re ≤ M})
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R) :
    ‖f z - f ((σ : ℂ) + I * t)‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
        (R - ‖z - ((σ : ℂ) + I * t)‖) := by
  have hfdisk :
      DifferentiableOn ℂ f (Metric.ball ((σ : ℂ) + I * t) R) :=
    differentiableOn_ball_sigma_it_of_differentiableOn_verticalRegion
      hf ha hb hH
  have hmaps :
      Set.MapsTo (fun w => f w - f ((σ : ℂ) + I * t))
        (Metric.ball ((σ : ℂ) + I * t) R) {w | w.re ≤ M} := by
    intro w hw
    exact hf₁ (ball_sigma_it_subset_verticalRegion ha hb hH hw)
  exact borelCaratheodory_sub_centered hM hfdisk hmaps hR hz

/-- Half-radius Borel-Carathéodory on a disk centered at `σ + I*t`, with
differentiability and real-part control supplied on an ambient vertical
region. -/
lemma borelCaratheodory_centered_verticalRegion_half_radius_bound
    {f : ℂ → ℂ} {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (verticalRegion a b H))
    (hf₁ : Set.MapsTo f (verticalRegion a b H) {w | w.re ≤ M})
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖f z‖ ≤
      2 * M + 3 * ‖f ((σ : ℂ) + I * t)‖ := by
  have hfdisk :
      DifferentiableOn ℂ f (Metric.ball ((σ : ℂ) + I * t) R) :=
    differentiableOn_ball_sigma_it_of_differentiableOn_verticalRegion
      hf ha hb hH
  have hmaps :
      Set.MapsTo f (Metric.ball ((σ : ℂ) + I * t) R)
        {w | w.re ≤ M} := by
    intro w hw
    exact hf₁ (ball_sigma_it_subset_verticalRegion ha hb hH hw)
  exact borelCaratheodory_centered_half_radius_bound
    hM hfdisk hmaps hR hz_half

/-- Half-radius oscillation Borel-Carathéodory on a disk centered at
`σ + I*t`, with differentiability and real-part control supplied on an ambient
vertical region. -/
lemma borelCaratheodory_sub_centered_verticalRegion_half_radius_bound
    {f : ℂ → ℂ} {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (verticalRegion a b H))
    (hf₁ : Set.MapsTo
      (fun w => f w - f ((σ : ℂ) + I * t))
      (verticalRegion a b H) {w | w.re ≤ M})
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖f z - f ((σ : ℂ) + I * t)‖ ≤ 2 * M := by
  have hfdisk :
      DifferentiableOn ℂ f (Metric.ball ((σ : ℂ) + I * t) R) :=
    differentiableOn_ball_sigma_it_of_differentiableOn_verticalRegion
      hf ha hb hH
  have hmaps :
      Set.MapsTo (fun w => f w - f ((σ : ℂ) + I * t))
        (Metric.ball ((σ : ℂ) + I * t) R) {w | w.re ≤ M} := by
    intro w hw
    exact hf₁ (ball_sigma_it_subset_verticalRegion ha hb hH hw)
  exact borelCaratheodory_sub_centered_half_radius_bound
    hM hfdisk hmaps hR hz_half

/-- Borel-Carathéodory specialized to ζ on a disk centered at `σ + I*t`.

The only zeta-specific hypothesis left is an ambient real-part bound on ζ over
the vertical region.  This is the exact shape needed before supplying a future
growth estimate. -/
lemma borelCaratheodory_riemannZeta_verticalRegion
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hHpos : 0 < H)
    (hζ : Set.MapsTo riemannZeta (verticalRegion a b H) {w | w.re ≤ M})
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R) :
    ‖riemannZeta z‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
          (R - ‖z - ((σ : ℂ) + I * t)‖) +
        ‖riemannZeta ((σ : ℂ) + I * t)‖ *
          (R + ‖z - ((σ : ℂ) + I * t)‖) /
          (R - ‖z - ((σ : ℂ) + I * t)‖) :=
  borelCaratheodory_centered_verticalRegion hM
    (differentiableOn_riemannZeta_verticalRegion_of_pos_height hHpos)
    hζ ha hb hH hR hz

/-- Oscillation form of Borel-Carathéodory specialized to ζ on a disk centered
at `σ + I*t`.

The remaining input is an ambient real-part bound for the centered function
`ζ(w) - ζ(σ+it)`, matching the regular-part estimates used in classical
zero-free-region proofs. -/
lemma borelCaratheodory_sub_riemannZeta_verticalRegion
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hHpos : 0 < H)
    (hζ : Set.MapsTo
      (fun w => riemannZeta w - riemannZeta ((σ : ℂ) + I * t))
      (verticalRegion a b H) {w | w.re ≤ M})
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R) :
    ‖riemannZeta z - riemannZeta ((σ : ℂ) + I * t)‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
        (R - ‖z - ((σ : ℂ) + I * t)‖) :=
  borelCaratheodory_sub_centered_verticalRegion hM
    (differentiableOn_riemannZeta_verticalRegion_of_pos_height hHpos)
    hζ ha hb hH hR hz

/-- Half-radius Borel-Carathéodory specialized to ζ on a disk centered at
`σ + I*t`. -/
lemma borelCaratheodory_riemannZeta_verticalRegion_half_radius_bound
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hHpos : 0 < H)
    (hζ : Set.MapsTo riemannZeta (verticalRegion a b H) {w | w.re ≤ M})
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖riemannZeta z‖ ≤
      2 * M + 3 * ‖riemannZeta ((σ : ℂ) + I * t)‖ :=
  borelCaratheodory_centered_verticalRegion_half_radius_bound hM
    (differentiableOn_riemannZeta_verticalRegion_of_pos_height hHpos)
    hζ ha hb hH hR hz_half

/-- Half-radius oscillation Borel-Carathéodory specialized to ζ on a disk
centered at `σ + I*t`. -/
lemma borelCaratheodory_sub_riemannZeta_verticalRegion_half_radius_bound
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hHpos : 0 < H)
    (hζ : Set.MapsTo
      (fun w => riemannZeta w - riemannZeta ((σ : ℂ) + I * t))
      (verticalRegion a b H) {w | w.re ≤ M})
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖riemannZeta z - riemannZeta ((σ : ℂ) + I * t)‖ ≤ 2 * M :=
  borelCaratheodory_sub_centered_verticalRegion_half_radius_bound hM
    (differentiableOn_riemannZeta_verticalRegion_of_pos_height hHpos)
    hζ ha hb hH hR hz_half

/-- Convert a pointwise real-part estimate for ζ on an ambient vertical region
to the `Set.MapsTo` input expected by the Borel-Carathéodory wrappers. -/
lemma mapsTo_riemannZeta_verticalRegion_of_re_le
    {a b H M : ℝ}
    (hζ : ∀ z : ℂ, z ∈ verticalRegion a b H →
      (riemannZeta z).re ≤ M) :
    Set.MapsTo riemannZeta (verticalRegion a b H) {w | w.re ≤ M} := by
  intro z hz
  exact hζ z hz

/-- Convert a pointwise real-part estimate for centered ζ to the `Set.MapsTo`
input expected by the oscillation Borel-Carathéodory wrapper. -/
lemma mapsTo_sub_riemannZeta_verticalRegion_of_re_le
    {σ t a b H M : ℝ}
    (hζ : ∀ z : ℂ, z ∈ verticalRegion a b H →
      (riemannZeta z - riemannZeta ((σ : ℂ) + I * t)).re ≤ M) :
    Set.MapsTo
      (fun z => riemannZeta z - riemannZeta ((σ : ℂ) + I * t))
      (verticalRegion a b H) {w | w.re ≤ M} := by
  intro z hz
  exact hζ z hz

/-- Pointwise-estimate form of Borel-Carathéodory specialized to ζ on a disk
centered at `σ + I*t`. -/
lemma borelCaratheodory_riemannZeta_verticalRegion_of_re_le
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hHpos : 0 < H)
    (hζ : ∀ w : ℂ, w ∈ verticalRegion a b H → (riemannZeta w).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R) :
    ‖riemannZeta z‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
          (R - ‖z - ((σ : ℂ) + I * t)‖) +
        ‖riemannZeta ((σ : ℂ) + I * t)‖ *
          (R + ‖z - ((σ : ℂ) + I * t)‖) /
          (R - ‖z - ((σ : ℂ) + I * t)‖) :=
  borelCaratheodory_riemannZeta_verticalRegion hM hHpos
    (mapsTo_riemannZeta_verticalRegion_of_re_le hζ)
    ha hb hH hR hz

/-- Pointwise-estimate form of the oscillation Borel-Carathéodory wrapper
specialized to ζ on a disk centered at `σ + I*t`. -/
lemma borelCaratheodory_sub_riemannZeta_verticalRegion_of_re_le
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hHpos : 0 < H)
    (hζ : ∀ w : ℂ, w ∈ verticalRegion a b H →
      (riemannZeta w - riemannZeta ((σ : ℂ) + I * t)).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R) :
    ‖riemannZeta z - riemannZeta ((σ : ℂ) + I * t)‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
        (R - ‖z - ((σ : ℂ) + I * t)‖) :=
  borelCaratheodory_sub_riemannZeta_verticalRegion hM hHpos
    (mapsTo_sub_riemannZeta_verticalRegion_of_re_le hζ)
    ha hb hH hR hz

/-- Pointwise-estimate half-radius Borel-Carathéodory specialized to ζ on a
disk centered at `σ + I*t`. -/
lemma borelCaratheodory_riemannZeta_verticalRegion_of_re_le_half_radius
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hHpos : 0 < H)
    (hζ : ∀ w : ℂ, w ∈ verticalRegion a b H → (riemannZeta w).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖riemannZeta z‖ ≤
      2 * M + 3 * ‖riemannZeta ((σ : ℂ) + I * t)‖ :=
  borelCaratheodory_riemannZeta_verticalRegion_half_radius_bound hM hHpos
    (mapsTo_riemannZeta_verticalRegion_of_re_le hζ)
    ha hb hH hR hz_half

/-- Pointwise-estimate half-radius oscillation Borel-Carathéodory specialized
to ζ on a disk centered at `σ + I*t`. -/
lemma borelCaratheodory_sub_riemannZeta_verticalRegion_of_re_le_half_radius
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hHpos : 0 < H)
    (hζ : ∀ w : ℂ, w ∈ verticalRegion a b H →
      (riemannZeta w - riemannZeta ((σ : ℂ) + I * t)).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R)
    (hz_half : ‖z - ((σ : ℂ) + I * t)‖ ≤ R / 2) :
    ‖riemannZeta z - riemannZeta ((σ : ℂ) + I * t)‖ ≤ 2 * M :=
  borelCaratheodory_sub_riemannZeta_verticalRegion_half_radius_bound hM hHpos
    (mapsTo_sub_riemannZeta_verticalRegion_of_re_le hζ)
    ha hb hH hR hz_half

/-- Conditional Borel-Carathéodory bound for the logarithmic derivative of ζ on
a disk centered at `σ + I*t`.

This wrapper deliberately keeps differentiability of `logDeriv riemannZeta` as
an explicit hypothesis: proving that hypothesis is part of the remaining
zeta-specific analytic input, while this lemma supplies the reusable local
Borel-Carathéodory bookkeeping. -/
lemma borelCaratheodory_logDeriv_riemannZeta_verticalRegion
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M)
    (hlogdiff :
      DifferentiableOn ℂ (logDeriv riemannZeta) (verticalRegion a b H))
    (hlog : Set.MapsTo (logDeriv riemannZeta)
      (verticalRegion a b H) {w | w.re ≤ M})
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R) :
    ‖logDeriv riemannZeta z‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
          (R - ‖z - ((σ : ℂ) + I * t)‖) +
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ *
          (R + ‖z - ((σ : ℂ) + I * t)‖) /
          (R - ‖z - ((σ : ℂ) + I * t)‖) :=
  borelCaratheodory_centered_verticalRegion hM
    hlogdiff hlog ha hb hH hR hz

/-- Conditional oscillation form of Borel-Carathéodory for the logarithmic
derivative of ζ on a disk centered at `σ + I*t`. -/
lemma borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M)
    (hlogdiff :
      DifferentiableOn ℂ (logDeriv riemannZeta) (verticalRegion a b H))
    (hlog : Set.MapsTo
      (fun w =>
        logDeriv riemannZeta w -
          logDeriv riemannZeta ((σ : ℂ) + I * t))
      (verticalRegion a b H) {w | w.re ≤ M})
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R) :
    ‖logDeriv riemannZeta z -
        logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
        (R - ‖z - ((σ : ℂ) + I * t)‖) :=
  borelCaratheodory_sub_centered_verticalRegion hM
    hlogdiff hlog ha hb hH hR hz

/-- Convert a pointwise real-part estimate for `logDeriv ζ` on an ambient
vertical region to the `Set.MapsTo` input expected by the
Borel-Carathéodory wrappers. -/
lemma mapsTo_logDeriv_riemannZeta_verticalRegion_of_re_le
    {a b H M : ℝ}
    (hlog : ∀ z : ℂ, z ∈ verticalRegion a b H →
      (logDeriv riemannZeta z).re ≤ M) :
    Set.MapsTo (logDeriv riemannZeta)
      (verticalRegion a b H) {w | w.re ≤ M} := by
  intro z hz
  exact hlog z hz

/-- Convert a pointwise real-part estimate for the centered logarithmic
derivative to the `Set.MapsTo` input expected by the oscillation
Borel-Carathéodory wrapper. -/
lemma mapsTo_sub_logDeriv_riemannZeta_verticalRegion_of_re_le
    {σ t a b H M : ℝ}
    (hlog : ∀ z : ℂ, z ∈ verticalRegion a b H →
      (logDeriv riemannZeta z -
        logDeriv riemannZeta ((σ : ℂ) + I * t)).re ≤ M) :
    Set.MapsTo
      (fun z =>
        logDeriv riemannZeta z -
          logDeriv riemannZeta ((σ : ℂ) + I * t))
      (verticalRegion a b H) {w | w.re ≤ M} := by
  intro z hz
  exact hlog z hz

/-- Pointwise-estimate form of the conditional Borel-Carathéodory bound for
`logDeriv ζ` on a disk centered at `σ + I*t`. -/
lemma borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_re_le
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M)
    (hlogdiff :
      DifferentiableOn ℂ (logDeriv riemannZeta) (verticalRegion a b H))
    (hlog : ∀ w : ℂ, w ∈ verticalRegion a b H →
      (logDeriv riemannZeta w).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R) :
    ‖logDeriv riemannZeta z‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
          (R - ‖z - ((σ : ℂ) + I * t)‖) +
        ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ *
          (R + ‖z - ((σ : ℂ) + I * t)‖) /
          (R - ‖z - ((σ : ℂ) + I * t)‖) :=
  borelCaratheodory_logDeriv_riemannZeta_verticalRegion hM hlogdiff
    (mapsTo_logDeriv_riemannZeta_verticalRegion_of_re_le hlog)
    ha hb hH hR hz

/-- Pointwise-estimate form of the conditional oscillation
Borel-Carathéodory bound for `logDeriv ζ` on a disk centered at `σ + I*t`. -/
lemma borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_re_le
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M)
    (hlogdiff :
      DifferentiableOn ℂ (logDeriv riemannZeta) (verticalRegion a b H))
    (hlog : ∀ w : ℂ, w ∈ verticalRegion a b H →
      (logDeriv riemannZeta w -
        logDeriv riemannZeta ((σ : ℂ) + I * t)).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + I * t) R) :
    ‖logDeriv riemannZeta z -
        logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤
      2 * M * ‖z - ((σ : ℂ) + I * t)‖ /
        (R - ‖z - ((σ : ℂ) + I * t)‖) :=
  borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion hM hlogdiff
    (mapsTo_sub_logDeriv_riemannZeta_verticalRegion_of_re_le hlog)
    ha hb hH hR hz

section JensenWrapper

open MeromorphicAt MeromorphicOn Metric Real

/-- Local namespace entry point for Mathlib's Jensen formula.  The theorem is
available in Mathlib; applying it to `riemannZeta` still requires the
zeta-specific meromorphic setup and growth estimates. -/
lemma jensen_circleAverage_log_norm
    {c : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hR : R ≠ 0) (hf : MeromorphicOn f (closedBall c |R|)) :
    circleAverage (Real.log ‖f ·‖) c R
      = ∑ᶠ u, divisor f (closedBall c |R|) u * Real.log (R * ‖c - u‖⁻¹)
        + divisor f (closedBall c |R|) c * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt f c‖ :=
  MeromorphicOn.circleAverage_log_norm hR hf

/-- Jensen formula on a disk centered at `σ + I*t`, with meromorphicity
supplied on an ambient vertical region. -/
lemma jensen_circleAverage_log_norm_verticalRegion
    {f : ℂ → ℂ} {R σ t a b H : ℝ}
    (hR : R ≠ 0) (hf : MeromorphicOn f (verticalRegion a b H))
    (ha : a + |R| ≤ σ) (hb : σ + |R| ≤ b) (hH : H + |R| ≤ |t|) :
    circleAverage (Real.log ‖f ·‖) ((σ : ℂ) + I * t) R
      = ∑ᶠ u,
          divisor f (closedBall ((σ : ℂ) + I * t) |R|) u *
            Real.log (R * ‖((σ : ℂ) + I * t) - u‖⁻¹)
        + divisor f (closedBall ((σ : ℂ) + I * t) |R|)
            ((σ : ℂ) + I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt f ((σ : ℂ) + I * t)‖ := by
  exact jensen_circleAverage_log_norm hR
    (meromorphicOn_closedBall_sigma_it_of_meromorphicOn_verticalRegion
      (f := f) (σ := σ) (t := t) (R := |R|) (a := a) (b := b) (H := H)
      hf ha hb hH)

end JensenWrapper

/-- Local namespace entry point for Mathlib's Phragmén-Lindelöf principle in a
vertical strip. -/
lemma phragmenLindelof_vertical_strip
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {a b C : ℝ} {z : ℂ}
    (hfd : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hB : ∃ c < Real.pi / (b - a), ∃ B,
      f =O[Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z => Real.exp (B * Real.exp (c * |z.im|)))
    (hle_a : ∀ z : ℂ, Complex.re z = a → ‖f z‖ ≤ C)
    (hle_b : ∀ z : ℂ, Complex.re z = b → ‖f z‖ ≤ C)
    (hza : a ≤ Complex.re z) (hzb : Complex.re z ≤ b) :
    ‖f z‖ ≤ C :=
  PhragmenLindelof.vertical_strip hfd hB hle_a hle_b hza hzb

/-- Local namespace entry point for Mathlib's Hadamard three-lines theorem in
the bounded-boundary form. -/
lemma hadamardThreeLines_norm_le_interp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {z : ℂ} {A B l u : ℝ}
    (hul : l < u)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip l u)
    (hd : DiffContOnCl ℂ f (Complex.HadamardThreeLines.verticalStrip l u))
    (hB : BddAbove
      ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip l u))
    (ha : ∀ z ∈ Complex.re ⁻¹' {l}, ‖f z‖ ≤ A)
    (hb : ∀ z ∈ Complex.re ⁻¹' {u}, ‖f z‖ ≤ B) :
    ‖f z‖ ≤
      A ^ (1 - (z.re - l) / (u - l)) *
        B ^ ((z.re - l) / (u - l)) :=
  Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    hul hz hd hB ha hb

/-- A source-level 3-4-1 contradiction criterion for high-height zero-free
regions.

The analytic inputs are isolated as three upper bounds for the logarithmic
derivative at `σ`, `σ + it`, and `σ + 2it`.  The final hypothesis is the
real-variable margin showing that those upper bounds make the de la Vallée
Poussin 3-4-1 combination strictly negative for any zero in the proposed
strip.  The proved `log_deriv_zeta_nonneg_combination` then gives the
contradiction. -/
lemma three_four_one_zero_free_high_height_of_log_deriv_bounds
    {T0 c : ℝ} {σOf realBound twoBound : ℝ → ℝ}
    {zeroBound : ℝ → ℝ → ℝ}
    (_hT0 : 2 ≤ T0) (hc_pos : 0 < c)
    (hσ_gt : ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t)
    (hσ_le : ∀ t : ℝ, T0 ≤ |t| → σOf t ≤ 2)
    (hσ_sub_pos : ∀ β t : ℝ, T0 ≤ |t| → β < 1 →
      β ≥ 1 - c / Real.log |t| → 0 < σOf t - β)
    (hreal :
      ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
        (-deriv riemannZeta (σOf t : ℂ) / riemannZeta (σOf t : ℂ)).re ≤
          realBound t)
    (hzero :
      ∀ β t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 → β < 1 →
        β ≥ 1 - c / Real.log |t| → 0 < σOf t - β →
        riemannZeta ((β : ℂ) + I * t) = 0 →
        (-deriv riemannZeta ((σOf t : ℂ) + I * t) /
          riemannZeta ((σOf t : ℂ) + I * t)).re ≤ zeroBound β t)
    (htwo :
      ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
        (-deriv riemannZeta ((σOf t : ℂ) + 2 * I * t) /
          riemannZeta ((σOf t : ℂ) + 2 * I * t)).re ≤ twoBound t)
    (hmargin :
      ∀ β t : ℝ, T0 ≤ |t| → β < 1 →
        β ≥ 1 - c / Real.log |t| →
        3 * realBound t + 4 * zeroBound β t + twoBound t < 0) :
    ∃ c' > 0, ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - c' / Real.log |s.im| → riemannZeta s ≠ 0 := by
  refine ⟨c, hc_pos, ?_⟩
  intro s hsheight hsre hs_zero
  have hs_lt_one : s.re < 1 := by
    by_contra hs_not_lt
    exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hs_not_lt)) hs_zero
  have hσ_gt' : 1 < σOf s.im := hσ_gt s.im hsheight
  have hσ_le' : σOf s.im ≤ 2 := hσ_le s.im hsheight
  have hσ_sub' : 0 < σOf s.im - s.re :=
    hσ_sub_pos s.re s.im hsheight hs_lt_one hsre
  have hs_zero_re_im : riemannZeta ((s.re : ℂ) + I * s.im) = 0 := by
    simpa [re_im_decomp s] using hs_zero
  have hnonneg :=
    log_deriv_zeta_nonneg_combination (σOf s.im) hσ_gt' s.im
  have hreal' :=
    hreal s.im hsheight hσ_gt' hσ_le'
  have hzero' :=
    hzero s.re s.im hsheight hσ_gt' hσ_le' hs_lt_one hsre hσ_sub' hs_zero_re_im
  have htwo' :=
    htwo s.im hsheight hσ_gt' hσ_le'
  have hupper :
      3 * (-deriv riemannZeta (σOf s.im : ℂ) /
            riemannZeta (σOf s.im : ℂ)).re
        + 4 * (-deriv riemannZeta ((σOf s.im : ℂ) + I * s.im) /
            riemannZeta ((σOf s.im : ℂ) + I * s.im)).re
        + (-deriv riemannZeta ((σOf s.im : ℂ) + 2 * I * s.im) /
            riemannZeta ((σOf s.im : ℂ) + 2 * I * s.im)).re
        ≤ 3 * realBound s.im + 4 * zeroBound s.re s.im + twoBound s.im := by
    nlinarith
  have hneg :=
    hmargin s.re s.im hsheight hs_lt_one hsre
  linarith

lemma compact_log_width_le_of_two_le {c d t : ℝ}
    (hc : c ≤ d * Real.log 2) (hd : 0 ≤ d) (ht : 2 ≤ |t|) :
    c / Real.log |t| ≤ d := by
  have hlog_pos : 0 < Real.log |t| := log_abs_pos_of_two_le ht
  have hlog_mono : Real.log (2 : ℝ) ≤ Real.log |t| :=
    Real.log_le_log (by norm_num) ht
  have hc_le_dlog : c ≤ d * Real.log |t| :=
    le_trans hc (mul_le_mul_of_nonneg_left hlog_mono hd)
  exact (div_le_iff₀ hlog_pos).mpr hc_le_dlog

/-- Monotonicity for zero-free strips stated with an arbitrary width function:
if a larger-width strip is zero-free, then every smaller-width strip is also
zero-free. -/
lemma zero_free_region_mono_width
    {T0 : ℝ} {width_small width_large : ℝ → ℝ}
    (hlarge : ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - width_large |s.im| → riemannZeta s ≠ 0)
    (hwidth : ∀ t : ℝ, T0 ≤ |t| → width_small |t| ≤ width_large |t|) :
    ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - width_small |s.im| → riemannZeta s ≠ 0 := by
  intro s hsheight hsre
  refine hlarge s hsheight ?_
  have hwidth' := hwidth s.im hsheight
  linarith

/-- Coordinate form of `zero_free_region_mono_width`. -/
lemma zero_free_region_mono_width_re_im
    {T0 : ℝ} {width_small width_large : ℝ → ℝ}
    (hlarge : ∀ β t : ℝ, T0 ≤ |t| →
      β ≥ 1 - width_large |t| → riemannZeta ((β : ℂ) + I * t) ≠ 0)
    (hwidth : ∀ t : ℝ, T0 ≤ |t| → width_small |t| ≤ width_large |t|) :
    ∀ β t : ℝ, T0 ≤ |t| →
      β ≥ 1 - width_small |t| → riemannZeta ((β : ℂ) + I * t) ≠ 0 := by
  intro β t htheight hβ
  refine hlarge β t htheight ?_
  have hwidth' := hwidth t htheight
  linarith

lemma classical_zero_free_region_high_height_mono_const
    {T0 csmall clarge : ℝ} (hT0 : 2 ≤ T0)
    (hc : csmall ≤ clarge)
    (hlarge : ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - clarge / Real.log |s.im| → riemannZeta s ≠ 0) :
    ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - csmall / Real.log |s.im| → riemannZeta s ≠ 0 :=
  zero_free_region_mono_width
    (width_small := fun t : ℝ => csmall / Real.log t)
    (width_large := fun t : ℝ => clarge / Real.log t)
    hlarge
    (fun _t ht => classical_width_mono_const hc (hT0.trans ht))

lemma classical_zero_free_region_high_height_mono_const_re_im
    {T0 csmall clarge : ℝ} (hT0 : 2 ≤ T0)
    (hc : csmall ≤ clarge)
    (hlarge : ∀ β t : ℝ, T0 ≤ |t| →
      β ≥ 1 - clarge / Real.log |t| →
      riemannZeta ((β : ℂ) + I * t) ≠ 0) :
    ∀ β t : ℝ, T0 ≤ |t| →
      β ≥ 1 - csmall / Real.log |t| →
      riemannZeta ((β : ℂ) + I * t) ≠ 0 :=
  zero_free_region_mono_width_re_im
    (width_small := fun t : ℝ => csmall / Real.log t)
    (width_large := fun t : ℝ => clarge / Real.log t)
    hlarge
    (fun _t ht => classical_width_mono_const hc (hT0.trans ht))

lemma classical_zero_free_region_high_height_mono_cutoff
    {T0 T1 c : ℝ} (hT : T0 ≤ T1)
    (hregion : ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0) :
    ∀ s : ℂ, T1 ≤ |s.im| →
      s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0 := by
  intro s hsT hsre
  exact hregion s (hT.trans hsT) hsre

lemma classical_zero_free_region_high_height_mono_cutoff_re_im
    {T0 T1 c : ℝ} (hT : T0 ≤ T1)
    (hregion : ∀ β t : ℝ, T0 ≤ |t| →
      β ≥ 1 - c / Real.log |t| →
      riemannZeta ((β : ℂ) + I * t) ≠ 0) :
    ∀ β t : ℝ, T1 ≤ |t| →
      β ≥ 1 - c / Real.log |t| →
      riemannZeta ((β : ℂ) + I * t) ≠ 0 := by
  intro β t ht hβ
  exact hregion β t (hT.trans ht) hβ

lemma classical_zero_free_region_high_height_exists_mono_cutoff
    {T0 T1 : ℝ} (hT : T0 ≤ T1)
    (hregion :
      ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
        s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0) :
    ∃ c > 0, ∀ s : ℂ, T1 ≤ |s.im| →
      s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0 := by
  rcases hregion with ⟨c, hc_pos, hregion⟩
  exact ⟨c, hc_pos, classical_zero_free_region_high_height_mono_cutoff hT hregion⟩

lemma classical_zero_free_region_high_height_exists_mono_cutoff_re_im
    {T0 T1 : ℝ} (hT : T0 ≤ T1)
    (hregion :
      ∃ c > 0, ∀ β t : ℝ, T0 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + I * t) ≠ 0) :
    ∃ c > 0, ∀ β t : ℝ, T1 ≤ |t| →
      β ≥ 1 - c / Real.log |t| →
      riemannZeta ((β : ℂ) + I * t) ≠ 0 := by
  rcases hregion with ⟨c, hc_pos, hregion⟩
  exact ⟨c, hc_pos,
    classical_zero_free_region_high_height_mono_cutoff_re_im hT hregion⟩

lemma classical_zero_free_region_on_one_line
    (hclassical : classical_zero_free_region) :
    ∀ s : ℂ, 2 ≤ |s.im| → s.re = 1 → riemannZeta s ≠ 0 := by
  rcases hclassical with ⟨c, hc_pos, hregion⟩
  intro s hs2 hsre
  refine hregion s hs2 ?_
  have hlog_pos : 0 < Real.log |s.im| := log_abs_pos_of_two_le hs2
  have hwidth_pos : 0 < c / Real.log |s.im| := div_pos hc_pos hlog_pos
  rw [hsre]
  linarith

/-- Patch a high-height quantitative zero-free region with the compact
zero-free strip at bounded height.

This is the final elementary assembly step in the classical zero-free-region
argument.  The deep input is isolated in `hhigh`; the proof here only combines
that input with `classical_zero_free_region_compact`. -/
lemma compact_patch_classical_zero_free_region
    (T0 : ℝ) (hT0 : 2 ≤ T0)
    (hhigh :
      ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
        s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0) :
    classical_zero_free_region := by
  rcases hhigh with ⟨chigh, hchigh_pos, hhigh_region⟩
  rcases classical_zero_free_region_compact T0 hT0 with ⟨d, hd_pos, hcompact⟩
  let c := min chigh (d * Real.log 2)
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc_pos : 0 < c := lt_min hchigh_pos (mul_pos hd_pos hlog2_pos)
  refine ⟨c, hc_pos, ?_⟩
  intro s hs2 hsre
  by_cases hlarge : T0 ≤ |s.im|
  · refine hhigh_region s hlarge ?_
    have hlog_pos : 0 < Real.log |s.im| := log_abs_pos_of_two_le hs2
    have hc_le : c ≤ chigh := min_le_left chigh (d * Real.log 2)
    have hdiv : c / Real.log |s.im| ≤ chigh / Real.log |s.im| :=
      div_le_div_of_nonneg_right hc_le hlog_pos.le
    linarith
  · refine hcompact s (le_of_not_ge hlarge) ?_
    have hlog_pos : 0 < Real.log |s.im| := log_abs_pos_of_two_le hs2
    have hlog_mono : Real.log (2 : ℝ) ≤ Real.log |s.im| :=
      Real.log_le_log (by norm_num) hs2
    have hc_le : c ≤ d * Real.log 2 := min_le_right chigh (d * Real.log 2)
    have hc_le_dlog : c ≤ d * Real.log |s.im| :=
      le_trans hc_le (mul_le_mul_of_nonneg_left hlog_mono hd_pos.le)
    have hfrac : c / Real.log |s.im| ≤ d := by
      exact (div_le_iff₀ hlog_pos).mpr hc_le_dlog
    linarith

/-- Full classical zero-free-region closure from the 3-4-1 high-height
logarithmic-derivative bounds.

The deep analytic work is still isolated in the three logarithmic-derivative
estimates and the real-variable margin.  This theorem performs the verified
assembly step: first use the 3-4-1 contradiction to obtain the high-height
strip, then patch the bounded-height range by compactness. -/
lemma classical_zero_free_region_of_log_deriv_bounds
    {T0 c : ℝ} {σOf realBound twoBound : ℝ → ℝ}
    {zeroBound : ℝ → ℝ → ℝ}
    (hT0 : 2 ≤ T0) (hc_pos : 0 < c)
    (hσ_gt : ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t)
    (hσ_le : ∀ t : ℝ, T0 ≤ |t| → σOf t ≤ 2)
    (hσ_sub_pos : ∀ β t : ℝ, T0 ≤ |t| → β < 1 →
      β ≥ 1 - c / Real.log |t| → 0 < σOf t - β)
    (hreal :
      ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
        (-deriv riemannZeta (σOf t : ℂ) / riemannZeta (σOf t : ℂ)).re ≤
          realBound t)
    (hzero :
      ∀ β t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 → β < 1 →
        β ≥ 1 - c / Real.log |t| → 0 < σOf t - β →
        riemannZeta ((β : ℂ) + I * t) = 0 →
        (-deriv riemannZeta ((σOf t : ℂ) + I * t) /
          riemannZeta ((σOf t : ℂ) + I * t)).re ≤ zeroBound β t)
    (htwo :
      ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
        (-deriv riemannZeta ((σOf t : ℂ) + 2 * I * t) /
          riemannZeta ((σOf t : ℂ) + 2 * I * t)).re ≤ twoBound t)
    (hmargin :
      ∀ β t : ℝ, T0 ≤ |t| → β < 1 →
        β ≥ 1 - c / Real.log |t| →
        3 * realBound t + 4 * zeroBound β t + twoBound t < 0) :
    classical_zero_free_region :=
  compact_patch_classical_zero_free_region T0 hT0
    (three_four_one_zero_free_high_height_of_log_deriv_bounds
      hT0 hc_pos hσ_gt hσ_le hσ_sub_pos hreal hzero htwo hmargin)

/-- General compact patching lemma for any high-height zero-free width.

If a deep argument proves zero-freeness above a height `T0` with some width
`width |Im s|`, and a classical `c / log |Im s|` width is eventually dominated
by that width, then the compact strip fills the bounded-height gap and yields
the classical target statement. -/
lemma compact_patch_classical_zero_free_region_of_width
    (T0 : ℝ) (hT0 : 2 ≤ T0) (width : ℝ → ℝ)
    (hregion : ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - width |s.im| → riemannZeta s ≠ 0)
    (hwidth : ∃ c > 0, ∀ t : ℝ, T0 ≤ |t| →
      c / Real.log |t| ≤ width |t|) :
    classical_zero_free_region := by
  rcases hwidth with ⟨cwidth, hcwidth_pos, hwidth_bound⟩
  rcases classical_zero_free_region_compact T0 hT0 with ⟨d, hd_pos, hcompact⟩
  let c := min cwidth (d * Real.log 2)
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc_pos : 0 < c := lt_min hcwidth_pos (mul_pos hd_pos hlog2_pos)
  refine ⟨c, hc_pos, ?_⟩
  intro s hs2 hsre
  by_cases hlarge : T0 ≤ |s.im|
  · refine hregion s hlarge ?_
    have hlog_pos : 0 < Real.log |s.im| := log_abs_pos_of_two_le hs2
    have hc_le : c ≤ cwidth := min_le_left cwidth (d * Real.log 2)
    have hdiv : c / Real.log |s.im| ≤ cwidth / Real.log |s.im| :=
      div_le_div_of_nonneg_right hc_le hlog_pos.le
    have hwidth' : cwidth / Real.log |s.im| ≤ width |s.im| :=
      hwidth_bound s.im hlarge
    linarith
  · refine hcompact s (le_of_not_ge hlarge) ?_
    have hlog_pos : 0 < Real.log |s.im| := log_abs_pos_of_two_le hs2
    have hlog_mono : Real.log (2 : ℝ) ≤ Real.log |s.im| :=
      Real.log_le_log (by norm_num) hs2
    have hc_le : c ≤ d * Real.log 2 := min_le_right cwidth (d * Real.log 2)
    have hc_le_dlog : c ≤ d * Real.log |s.im| :=
      le_trans hc_le (mul_le_mul_of_nonneg_left hlog_mono hd_pos.le)
    have hfrac : c / Real.log |s.im| ≤ d := by
      exact (div_le_iff₀ hlog_pos).mpr hc_le_dlog
    linarith

/-- Version of the width patch for high-height inputs stated in real and
imaginary coordinates.  This is the natural shape of many complex-analysis
zero-free estimates before they are packaged as statements about arbitrary
`s : ℂ`. -/
lemma compact_patch_classical_zero_free_region_of_width_re_im
    (T0 : ℝ) (hT0 : 2 ≤ T0) (width : ℝ → ℝ)
    (hregion : ∀ β t : ℝ, T0 ≤ |t| →
      β ≥ 1 - width |t| → riemannZeta ((β : ℂ) + I * t) ≠ 0)
    (hwidth : ∃ c > 0, ∀ t : ℝ, T0 ≤ |t| →
      c / Real.log |t| ≤ width |t|) :
    classical_zero_free_region := by
  refine compact_patch_classical_zero_free_region_of_width T0 hT0 width ?_ hwidth
  intro s hsheight hsre
  have hs_decomp : ((s.re : ℂ) + I * s.im) = s := by
    apply Complex.ext <;> simp
  simpa [hs_decomp] using hregion s.re s.im hsheight hsre

/-- A high-height `c / log |t|` zero-free theorem is the special case of the
general width patch with `width t = c / log t`. -/
lemma compact_patch_classical_zero_free_region_via_width
    (T0 : ℝ) (hT0 : 2 ≤ T0)
    (hhigh :
      ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
        s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0) :
    classical_zero_free_region := by
  rcases hhigh with ⟨chigh, hchigh_pos, hhigh_region⟩
  exact compact_patch_classical_zero_free_region_of_width T0 hT0
    (fun t : ℝ => chigh / Real.log t)
    hhigh_region
    ⟨chigh, hchigh_pos, by intro t _; rfl⟩

/-- Coordinate version of `compact_patch_classical_zero_free_region`. -/
lemma compact_patch_classical_zero_free_region_re_im
    (T0 : ℝ) (hT0 : 2 ≤ T0)
    (hhigh :
      ∃ c > 0, ∀ β t : ℝ, T0 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + I * t) ≠ 0) :
    classical_zero_free_region := by
  rcases hhigh with ⟨chigh, hchigh_pos, hhigh_region⟩
  exact compact_patch_classical_zero_free_region_of_width_re_im T0 hT0
    (fun t : ℝ => chigh / Real.log t)
    hhigh_region
    ⟨chigh, hchigh_pos, by intro t _; rfl⟩

/-- Specialize the compact patch to the height cutoff used by the
Vinogradov-Korobov target. -/
lemma compact_patch_classical_zero_free_region_at_three
    (hhigh :
      ∃ c > 0, ∀ s : ℂ, 3 ≤ |s.im| →
        s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0) :
    classical_zero_free_region :=
  compact_patch_classical_zero_free_region 3 (by norm_num) hhigh

lemma compact_patch_classical_zero_free_region_re_im_at_three
    (hhigh :
      ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + I * t) ≠ 0) :
    classical_zero_free_region :=
  compact_patch_classical_zero_free_region_re_im 3 (by norm_num) hhigh

/-- Any classical zero-free region immediately restricts to an arbitrary
high-height range.  This is the easy direction paired with
`compact_patch_classical_zero_free_region`. -/
lemma classical_zero_free_region_high_height
    (T0 : ℝ) (hT0 : 2 ≤ T0)
    (hclassical : classical_zero_free_region) :
    ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0 := by
  rcases hclassical with ⟨c, hc_pos, hregion⟩
  refine ⟨c, hc_pos, ?_⟩
  intro s hsT hsre
  exact hregion s (hT0.trans hsT) hsre

/-- The classical zero-free-region target is equivalent to proving the same
`c / log |t|` width only above any fixed height `T0 ≥ 2`.

The forward direction is restriction to high height; the reverse direction is
the compact patch next to `Re(s) = 1`. -/
lemma classical_zero_free_region_iff_high_height
    (T0 : ℝ) (hT0 : 2 ≤ T0) :
    classical_zero_free_region ↔
      ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
        s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0 := by
  constructor
  · exact classical_zero_free_region_high_height T0 hT0
  · exact compact_patch_classical_zero_free_region T0 hT0

/-- Height `3` specialization of the high-height interface, matching the
Vinogradov-Korobov target's cutoff. -/
lemma classical_zero_free_region_iff_high_height_at_three :
    classical_zero_free_region ↔
      ∃ c > 0, ∀ s : ℂ, 3 ≤ |s.im| →
        s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0 :=
  classical_zero_free_region_iff_high_height 3 (by norm_num)

lemma classical_zero_free_region_iff_high_height_re_im
    (T0 : ℝ) (hT0 : 2 ≤ T0) :
    classical_zero_free_region ↔
      ∃ c > 0, ∀ β t : ℝ, T0 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + I * t) ≠ 0 := by
  constructor
  · intro h
    rcases classical_zero_free_region_high_height T0 hT0 h with
      ⟨c, hc_pos, hregion⟩
    refine ⟨c, hc_pos, ?_⟩
    intro β t ht hβ
    have hheight : T0 ≤ |((β : ℂ) + I * t).im| := by
      simpa using ht
    have hre :
        ((β : ℂ) + I * t).re ≥ 1 - c / Real.log |((β : ℂ) + I * t).im| := by
      simpa using hβ
    exact hregion ((β : ℂ) + I * t) hheight hre
  · exact compact_patch_classical_zero_free_region_re_im T0 hT0

/-- Height `3` specialization of the coordinate high-height interface, matching
the Vinogradov-Korobov cutoff. -/
lemma classical_zero_free_region_iff_high_height_re_im_at_three :
    classical_zero_free_region ↔
      ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + I * t) ≠ 0 :=
  classical_zero_free_region_iff_high_height_re_im 3 (by norm_num)

lemma classical_zero_free_region_high_height_re_im
    (T0 : ℝ) (hT0 : 2 ≤ T0)
    (hclassical : classical_zero_free_region) :
    ∃ c > 0, ∀ β t : ℝ, T0 ≤ |t| →
      β ≥ 1 - c / Real.log |t| →
      riemannZeta ((β : ℂ) + I * t) ≠ 0 :=
  (classical_zero_free_region_iff_high_height_re_im T0 hT0).mp hclassical

lemma classical_zero_free_region_high_height_re_im_at_three
    (hclassical : classical_zero_free_region) :
    ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
      β ≥ 1 - c / Real.log |t| →
      riemannZeta ((β : ℂ) + I * t) ≠ 0 :=
  classical_zero_free_region_high_height_re_im 3 (by norm_num) hclassical

lemma classical_zero_free_region_of_high_height_re_im
    (T0 : ℝ) (hT0 : 2 ≤ T0)
    (hcoord :
      ∃ c > 0, ∀ β t : ℝ, T0 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + I * t) ≠ 0) :
    classical_zero_free_region :=
  (classical_zero_free_region_iff_high_height_re_im T0 hT0).mpr hcoord

lemma classical_zero_free_region_high_height_at_three
    (hclassical : classical_zero_free_region) :
    ∃ c > 0, ∀ s : ℂ, 3 ≤ |s.im| →
      s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0 :=
  classical_zero_free_region_high_height 3 (by norm_num) hclassical

/-- Vinogradov-Korobov 零点自由区域：目前最广的已知零自由区域。
    需要指数和估计，远超当前 Mathlib 范畴。 -/
def vinogradov_korobov_zero_free_region : Prop :=
    ∃ c > 0, ∀ s : ℂ, |s.im| ≥ 3 → s.re ≥ 1 - c / (Real.log |s.im|)^(2/3 : ℝ) * (Real.log (Real.log |s.im|))^(-1/3 : ℝ) → riemannZeta s ≠ 0

/-- Coordinate form of the Vinogradov-Korobov zero-free-region target. -/
lemma vinogradov_korobov_zero_free_region_iff_re_im :
    vinogradov_korobov_zero_free_region ↔
      ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
        β ≥
          1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
        riemannZeta ((β : ℂ) + I * t) ≠ 0 := by
  constructor
  · intro hvk
    rcases hvk with ⟨c, hc_pos, hregion⟩
    refine ⟨c, hc_pos, ?_⟩
    intro β t ht hβ
    have hheight : |((β : ℂ) + I * t).im| ≥ 3 := by
      simpa using ht
    have hre :
        ((β : ℂ) + I * t).re ≥
          1 - c / (Real.log |((β : ℂ) + I * t).im|) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log |((β : ℂ) + I * t).im|)) ^ (-1 / 3 : ℝ) := by
      simpa using hβ
    exact hregion ((β : ℂ) + I * t) hheight hre
  · intro hcoord
    rcases hcoord with ⟨c, hc_pos, hregion⟩
    refine ⟨c, hc_pos, ?_⟩
    intro s hsheight hsre
    have hs_decomp : ((s.re : ℂ) + I * s.im) = s := by
      apply Complex.ext <;> simp
    simpa [hs_decomp] using hregion s.re s.im hsheight hsre

lemma vinogradov_korobov_zero_free_region_to_re_im
    (hvk : vinogradov_korobov_zero_free_region) :
    ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
      β ≥
        1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
      riemannZeta ((β : ℂ) + I * t) ≠ 0 :=
  vinogradov_korobov_zero_free_region_iff_re_im.mp hvk

lemma vinogradov_korobov_zero_free_region_of_re_im
    (hcoord :
      ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
        β ≥
          1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
        riemannZeta ((β : ℂ) + I * t) ≠ 0) :
    vinogradov_korobov_zero_free_region :=
  vinogradov_korobov_zero_free_region_iff_re_im.mpr hcoord

lemma vinogradov_korobov_width_pos_of_three_le {c t : ℝ}
    (hc : 0 < c) (ht : 3 ≤ |t|) :
    0 <
      c / (Real.log |t|) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) := by
  have hlog_gt_one : 1 < Real.log |t| := log_abs_gt_one_of_three_le ht
  have hlog_pos : 0 < Real.log |t| := by linarith
  have hloglog_pos : 0 < Real.log (Real.log |t|) :=
    log_log_abs_pos_of_three_le ht
  exact mul_pos
    (div_pos hc (Real.rpow_pos_of_pos hlog_pos (2 / 3 : ℝ)))
    (Real.rpow_pos_of_pos hloglog_pos (-1 / 3 : ℝ))

/-- The Vinogradov-Korobov width is monotone in the width constant. -/
lemma vinogradov_korobov_width_mono_const {csmall clarge t : ℝ}
    (hc : csmall ≤ clarge) (ht : 3 ≤ |t|) :
    csmall / (Real.log |t|) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) ≤
      clarge / (Real.log |t|) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) := by
  have hlog_pos : 0 < Real.log |t| := by
    have h := log_abs_gt_one_of_three_le ht
    linarith
  have hden_pos : 0 < (Real.log |t|) ^ (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos hlog_pos (2 / 3 : ℝ)
  have hloglog_pos : 0 < Real.log (Real.log |t|) :=
    log_log_abs_pos_of_three_le ht
  have hfactor_nonneg :
      0 ≤ (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) :=
    (Real.rpow_pos_of_pos hloglog_pos (-1 / 3 : ℝ)).le
  have hbase :
      csmall / (Real.log |t|) ^ (2 / 3 : ℝ) ≤
        clarge / (Real.log |t|) ^ (2 / 3 : ℝ) :=
    div_le_div_of_nonneg_right hc hden_pos.le
  exact mul_le_mul_of_nonneg_right hbase hfactor_nonneg

lemma vinogradov_korobov_zero_free_region_high_height_mono_const
    {T0 csmall clarge : ℝ} (hT0 : 3 ≤ T0)
    (hc : csmall ≤ clarge)
    (hlarge : ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥
        1 - clarge / (Real.log |s.im|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |s.im|)) ^ (-1 / 3 : ℝ) →
      riemannZeta s ≠ 0) :
    ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥
        1 - csmall / (Real.log |s.im|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |s.im|)) ^ (-1 / 3 : ℝ) →
      riemannZeta s ≠ 0 :=
  zero_free_region_mono_width
    (width_small := fun t : ℝ =>
      csmall / (Real.log t) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log t)) ^ (-1 / 3 : ℝ))
    (width_large := fun t : ℝ =>
      clarge / (Real.log t) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log t)) ^ (-1 / 3 : ℝ))
    hlarge
    (fun _t ht => vinogradov_korobov_width_mono_const hc (hT0.trans ht))

lemma vinogradov_korobov_zero_free_region_high_height_mono_const_re_im
    {T0 csmall clarge : ℝ} (hT0 : 3 ≤ T0)
    (hc : csmall ≤ clarge)
    (hlarge : ∀ β t : ℝ, T0 ≤ |t| →
      β ≥
        1 - clarge / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
      riemannZeta ((β : ℂ) + I * t) ≠ 0) :
    ∀ β t : ℝ, T0 ≤ |t| →
      β ≥
        1 - csmall / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
      riemannZeta ((β : ℂ) + I * t) ≠ 0 :=
  zero_free_region_mono_width_re_im
    (width_small := fun t : ℝ =>
      csmall / (Real.log t) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log t)) ^ (-1 / 3 : ℝ))
    (width_large := fun t : ℝ =>
      clarge / (Real.log t) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log t)) ^ (-1 / 3 : ℝ))
    hlarge
    (fun _t ht => vinogradov_korobov_width_mono_const hc (hT0.trans ht))

lemma vinogradov_korobov_zero_free_region_high_height_mono_cutoff
    {T0 T1 c : ℝ} (hT : T0 ≤ T1)
    (hregion : ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥
        1 - c / (Real.log |s.im|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |s.im|)) ^ (-1 / 3 : ℝ) →
      riemannZeta s ≠ 0) :
    ∀ s : ℂ, T1 ≤ |s.im| →
      s.re ≥
        1 - c / (Real.log |s.im|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |s.im|)) ^ (-1 / 3 : ℝ) →
      riemannZeta s ≠ 0 := by
  intro s hsT hsre
  exact hregion s (hT.trans hsT) hsre

lemma vinogradov_korobov_zero_free_region_high_height_mono_cutoff_re_im
    {T0 T1 c : ℝ} (hT : T0 ≤ T1)
    (hregion : ∀ β t : ℝ, T0 ≤ |t| →
      β ≥
        1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
      riemannZeta ((β : ℂ) + I * t) ≠ 0) :
    ∀ β t : ℝ, T1 ≤ |t| →
      β ≥
        1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
      riemannZeta ((β : ℂ) + I * t) ≠ 0 := by
  intro β t ht hβ
  exact hregion β t (hT.trans ht) hβ

lemma vinogradov_korobov_zero_free_region_high_height_exists_mono_cutoff
    {T0 T1 : ℝ} (hT : T0 ≤ T1)
    (hregion :
      ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
        s.re ≥
          1 - c / (Real.log |s.im|) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log |s.im|)) ^ (-1 / 3 : ℝ) →
        riemannZeta s ≠ 0) :
    ∃ c > 0, ∀ s : ℂ, T1 ≤ |s.im| →
      s.re ≥
        1 - c / (Real.log |s.im|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |s.im|)) ^ (-1 / 3 : ℝ) →
      riemannZeta s ≠ 0 := by
  rcases hregion with ⟨c, hc_pos, hregion⟩
  exact ⟨c, hc_pos,
    vinogradov_korobov_zero_free_region_high_height_mono_cutoff hT hregion⟩

lemma vinogradov_korobov_zero_free_region_high_height_exists_mono_cutoff_re_im
    {T0 T1 : ℝ} (hT : T0 ≤ T1)
    (hregion :
      ∃ c > 0, ∀ β t : ℝ, T0 ≤ |t| →
        β ≥
          1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
        riemannZeta ((β : ℂ) + I * t) ≠ 0) :
    ∃ c > 0, ∀ β t : ℝ, T1 ≤ |t| →
      β ≥
        1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
      riemannZeta ((β : ℂ) + I * t) ≠ 0 := by
  rcases hregion with ⟨c, hc_pos, hregion⟩
  exact ⟨c, hc_pos,
    vinogradov_korobov_zero_free_region_high_height_mono_cutoff_re_im
      hT hregion⟩

lemma vinogradov_korobov_zero_free_region_high_height
    (T0 : ℝ) (hT0 : 3 ≤ T0)
    (hvk : vinogradov_korobov_zero_free_region) :
    ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥
        1 - c / (Real.log |s.im|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |s.im|)) ^ (-1 / 3 : ℝ) →
      riemannZeta s ≠ 0 := by
  rcases hvk with ⟨c, hc_pos, hregion⟩
  refine ⟨c, hc_pos, ?_⟩
  intro s hsT hsre
  exact hregion s (hT0.trans hsT) hsre

lemma vinogradov_korobov_zero_free_region_iff_high_height_at_three :
    vinogradov_korobov_zero_free_region ↔
      ∃ c > 0, ∀ s : ℂ, 3 ≤ |s.im| →
        s.re ≥
          1 - c / (Real.log |s.im|) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log |s.im|)) ^ (-1 / 3 : ℝ) →
        riemannZeta s ≠ 0 := by
  constructor
  · exact vinogradov_korobov_zero_free_region_high_height 3 (by norm_num)
  · intro h
    simpa [vinogradov_korobov_zero_free_region] using h

lemma vinogradov_korobov_zero_free_region_high_height_at_three
    (hvk : vinogradov_korobov_zero_free_region) :
    ∃ c > 0, ∀ s : ℂ, 3 ≤ |s.im| →
      s.re ≥
        1 - c / (Real.log |s.im|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |s.im|)) ^ (-1 / 3 : ℝ) →
      riemannZeta s ≠ 0 :=
  vinogradov_korobov_zero_free_region_high_height 3 (by norm_num) hvk

lemma vinogradov_korobov_zero_free_region_high_height_re_im
    (T0 : ℝ) (hT0 : 3 ≤ T0)
    (hvk : vinogradov_korobov_zero_free_region) :
    ∃ c > 0, ∀ β t : ℝ, T0 ≤ |t| →
      β ≥
        1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
      riemannZeta ((β : ℂ) + I * t) ≠ 0 := by
  rcases vinogradov_korobov_zero_free_region_high_height T0 hT0 hvk with
    ⟨c, hc_pos, hregion⟩
  refine ⟨c, hc_pos, ?_⟩
  intro β t ht hβ
  have hheight : T0 ≤ |((β : ℂ) + I * t).im| := by
    simpa using ht
  have hre :
      ((β : ℂ) + I * t).re ≥
        1 - c / (Real.log |((β : ℂ) + I * t).im|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |((β : ℂ) + I * t).im|)) ^ (-1 / 3 : ℝ) := by
    simpa using hβ
  exact hregion ((β : ℂ) + I * t) hheight hre

lemma vinogradov_korobov_zero_free_region_iff_high_height_re_im_at_three :
    vinogradov_korobov_zero_free_region ↔
      ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
        β ≥
          1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
        riemannZeta ((β : ℂ) + I * t) ≠ 0 := by
  constructor
  · exact vinogradov_korobov_zero_free_region_high_height_re_im 3 (by norm_num)
  · exact vinogradov_korobov_zero_free_region_of_re_im

lemma vinogradov_korobov_zero_free_region_high_height_re_im_at_three
    (hvk : vinogradov_korobov_zero_free_region) :
    ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
      β ≥
        1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
      riemannZeta ((β : ℂ) + I * t) ≠ 0 :=
  vinogradov_korobov_zero_free_region_high_height_re_im 3 (by norm_num) hvk

/-- Conditional bridge from the Vinogradov-Korobov target to the classical
zero-free region.

The analytic content remains in `hvk`; the remaining hypothesis `hcompare` is
only the real-variable width comparison saying that, above height `3`, some
`c' / log |t|` strip is contained in the Vinogradov-Korobov strip. -/
lemma classical_zero_free_region_of_vinogradov_korobov_with_comparison
    (hvk : vinogradov_korobov_zero_free_region)
    (hcompare : ∀ c > 0, ∃ c' > 0, ∀ t : ℝ, 3 ≤ |t| →
      c' / Real.log |t| ≤
        c / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ)) :
    classical_zero_free_region := by
  rcases hvk with ⟨cvk, hcvk_pos, hvk_region⟩
  exact compact_patch_classical_zero_free_region_of_width 3 (by norm_num)
    (fun t : ℝ =>
      cvk / (Real.log t) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log t)) ^ (-1 / 3 : ℝ))
    (fun s hsheight hsre => hvk_region s hsheight hsre)
    (hcompare cvk hcvk_pos)

/-- Pointwise real-variable width comparison behind the
Vinogradov-Korobov-to-classical bridge. -/
lemma classical_width_le_vinogradov_korobov_width {c t : ℝ}
    (hc : 0 ≤ c) (ht : 3 ≤ |t|) :
    c / Real.log |t| ≤
      c / (Real.log |t|) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) := by
  set x : ℝ := Real.log |t| with hx_def
  have ht_pos : 0 < |t| := by linarith
  have hexp_lt_three : Real.exp 1 < (3 : ℝ) := by
    calc
      Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ < (3 : ℝ) := by norm_num
  have hx_gt_one : 1 < x := by
    rw [hx_def]
    exact (Real.lt_log_iff_exp_lt ht_pos).mpr (lt_of_lt_of_le hexp_lt_three ht)
  have hx_pos : 0 < x := lt_trans (by norm_num) hx_gt_one
  have hlogx_pos : 0 < Real.log x := Real.log_pos hx_gt_one
  have hlogx_le_x : Real.log x ≤ x := Real.log_le_self hx_pos.le
  have hpow :
      x ^ (-1 / 3 : ℝ) ≤ (Real.log x) ^ (-1 / 3 : ℝ) := by
    exact Real.rpow_le_rpow_of_nonpos hlogx_pos hlogx_le_x (by norm_num)
  have hx_split :
      x ^ (-1 : ℝ) = x ^ (-(2 / 3 : ℝ)) * x ^ (-1 / 3 : ℝ) := by
    rw [← Real.rpow_add hx_pos]
    norm_num
  have hbase :
      x ^ (-1 : ℝ) ≤ x ^ (-(2 / 3 : ℝ)) * (Real.log x) ^ (-1 / 3 : ℝ) := by
    rw [hx_split]
    exact mul_le_mul_of_nonneg_left hpow
      (Real.rpow_nonneg hx_pos.le (-(2 / 3 : ℝ)))
  have hscaled :
      c * x ^ (-1 : ℝ) ≤
        c * (x ^ (-(2 / 3 : ℝ)) * (Real.log x) ^ (-1 / 3 : ℝ)) :=
    mul_le_mul_of_nonneg_left hbase hc
  calc
    c / Real.log |t| = c * x ^ (-1 : ℝ) := by
      rw [hx_def, div_eq_mul_inv, Real.rpow_neg hx_pos.le, Real.rpow_one]
    _ ≤ c * (x ^ (-(2 / 3 : ℝ)) * (Real.log x) ^ (-1 / 3 : ℝ)) := hscaled
    _ = c / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) := by
      rw [hx_def, div_eq_mul_inv, Real.rpow_neg hx_pos.le]
      ring

/-- Above height `3`, the Vinogradov-Korobov width dominates a classical
`c / log |t|` width.  The proof is purely real-variable: for
`x = log |t| > 1`, `log x ≤ x`, so the negative exponent `-1/3` reverses
the inequality. -/
lemma vinogradov_korobov_width_comparison :
    ∀ c > 0, ∃ c' > 0, ∀ t : ℝ, 3 ≤ |t| →
      c' / Real.log |t| ≤
        c / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) := by
  intro c hc
  exact ⟨c, hc, fun _t ht => classical_width_le_vinogradov_korobov_width hc.le ht⟩

/-- Coordinate-form Vinogradov-Korobov input implies the classical zero-free region.

Future analytic proofs often first produce a statement about real variables
`β` and `t`; this bridge packages that shape directly into the existing
compact patch plus width comparison. -/
lemma classical_zero_free_region_of_vinogradov_korobov_re_im
    (hvk : ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
      β ≥
        1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
      riemannZeta ((β : ℂ) + I * t) ≠ 0) :
    classical_zero_free_region := by
  rcases hvk with ⟨cvk, hcvk_pos, hvk_region⟩
  exact compact_patch_classical_zero_free_region_of_width_re_im 3 (by norm_num)
    (fun t : ℝ =>
      cvk / (Real.log t) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log t)) ^ (-1 / 3 : ℝ))
    hvk_region
    (vinogradov_korobov_width_comparison cvk hcvk_pos)

/-- A high-height Vinogradov-Korobov-width input above any cutoff `T0 ≥ 3`
implies the classical zero-free-region target.

This is useful when the analytic estimate is proved only eventually; the
bounded-height gap is filled by the compact strip, and the VK width dominates a
classical logarithmic width above `T0`. -/
lemma classical_zero_free_region_of_vinogradov_korobov_high_height
    (T0 : ℝ) (hT0 : 3 ≤ T0)
    (hvk : ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥
        1 - c / (Real.log |s.im|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |s.im|)) ^ (-1 / 3 : ℝ) →
      riemannZeta s ≠ 0) :
    classical_zero_free_region := by
  rcases hvk with ⟨cvk, hcvk_pos, hvk_region⟩
  exact compact_patch_classical_zero_free_region_of_width T0 (by linarith)
    (fun t : ℝ =>
      cvk / (Real.log t) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log t)) ^ (-1 / 3 : ℝ))
    hvk_region
    ⟨cvk, hcvk_pos, fun _t ht =>
      classical_width_le_vinogradov_korobov_width hcvk_pos.le (hT0.trans ht)⟩

/-- Coordinate high-height Vinogradov-Korobov-width input above any cutoff
`T0 ≥ 3` implies the classical zero-free-region target. -/
lemma classical_zero_free_region_of_vinogradov_korobov_high_height_re_im
    (T0 : ℝ) (hT0 : 3 ≤ T0)
    (hvk : ∃ c > 0, ∀ β t : ℝ, T0 ≤ |t| →
      β ≥
        1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
      riemannZeta ((β : ℂ) + I * t) ≠ 0) :
    classical_zero_free_region := by
  rcases hvk with ⟨cvk, hcvk_pos, hvk_region⟩
  exact compact_patch_classical_zero_free_region_of_width_re_im T0 (by linarith)
    (fun t : ℝ =>
      cvk / (Real.log t) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log t)) ^ (-1 / 3 : ℝ))
    hvk_region
    ⟨cvk, hcvk_pos, fun _t ht =>
      classical_width_le_vinogradov_korobov_width hcvk_pos.le (hT0.trans ht)⟩

/-- The Vinogradov-Korobov target supplies a high-height classical-width
zero-free region above height `3`.

This isolates the real-variable comparison from the compact patching step. -/
lemma vinogradov_korobov_high_height_classical_zero_free_region
    (hvk : vinogradov_korobov_zero_free_region) :
    ∃ c > 0, ∀ s : ℂ, 3 ≤ |s.im| →
      s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0 := by
  rcases hvk with ⟨cvk, hcvk_pos, hvk_region⟩
  rcases vinogradov_korobov_width_comparison cvk hcvk_pos with
    ⟨cclassical, hcclassical_pos, hwidth⟩
  refine ⟨cclassical, hcclassical_pos, ?_⟩
  intro s hsheight hsre
  refine hvk_region s hsheight ?_
  have hwidth' := hwidth s.im hsheight
  linarith

/-- Coordinate form of
`vinogradov_korobov_high_height_classical_zero_free_region`. -/
lemma vinogradov_korobov_high_height_classical_zero_free_region_re_im
    (hvk : vinogradov_korobov_zero_free_region) :
    ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
      β ≥ 1 - c / Real.log |t| →
      riemannZeta ((β : ℂ) + I * t) ≠ 0 := by
  rcases vinogradov_korobov_high_height_classical_zero_free_region hvk with
    ⟨c, hc_pos, hregion⟩
  refine ⟨c, hc_pos, ?_⟩
  intro β t ht hβ
  have hheight : 3 ≤ |((β : ℂ) + I * t).im| := by
    simpa using ht
  have hre :
      ((β : ℂ) + I * t).re ≥
        1 - c / Real.log |((β : ℂ) + I * t).im| := by
    simpa using hβ
  exact hregion ((β : ℂ) + I * t) hheight hre

/-- The Vinogradov-Korobov target implies the classical zero-free-region target.

This bridge contains no analytic proof of the Vinogradov-Korobov theorem; it
only discharges the real-variable width comparison and then reuses the compact
patching lemma at height `3`. -/
lemma classical_zero_free_region_of_vinogradov_korobov
    (hvk : vinogradov_korobov_zero_free_region) :
    classical_zero_free_region :=
  compact_patch_classical_zero_free_region_at_three
    (vinogradov_korobov_high_height_classical_zero_free_region hvk)

end ZeroFreeRegion
