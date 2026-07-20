/-
# RH 下 Li 配对零点项的逐项非负性

本文件补上正向方向「RH ⇒ Li 准则」除零点求和表示外的最后一块：
在 RH（`ρ.re = 1/2`）下，配对零点项的实部逐项非负。

## 数学内容

配对项可以写成「主项 + 其共轭」：

```text
liPairedTerm n ρ = [1 - (1-1/ρ)ⁿ] + [1 - (1-1/conjρ)ⁿ]
                 = ↑(2·Re(1 - (1-1/ρ)ⁿ))
```

（本文件 `liPairedTerm_eq_ofReal_two_mul_re`）。当 `ρ.re = 1/2` 时

```text
1 - 1/ρ = (ρ-1)/ρ，而 ‖ρ-1‖² = (ρ.re-1)² + ρ.im² = 1/4 + ρ.im² = ‖ρ‖²，
```

故 `‖1 - 1/ρ‖ = 1`（`norm_one_sub_inv_of_re_eq_half`）。于是
`Re((1-1/ρ)ⁿ) ≤ ‖(1-1/ρ)ⁿ‖ = 1`，从而

```text
(liPairedTerm n ρ).re = 2·(1 - Re((1-1/ρ)ⁿ)) ≥ 0
```

（`liPairedTerm_re_nonneg_of_re_eq_half`）。这正是经典恒等式
`1 - (1-1/ρ)ⁿ = 1 - e^{inθ}` 给出 `1 - cos(nθ) ≥ 0` 的形式化。

## 主要定理

- `liPairedTerm_re_nonneg_of_rh`：RH 下每个配对项实部非负（逐项）；
- `tsum_liPairedTerm_re_nonneg_of_rh`：RH 下（已证收敛的）配对零点级数
  的实部非负；
- `liCoefficient_re_nonneg_of_representation_of_rh`：**条件归约**——
  若 `li_zero_sum_representation_target` 成立，则 RH 蕴含
  `0 ≤ (liCoefficient n).re`。这把 `rh_implies_li_criterion_target`
  的剩余缺口精确地分离为：
  (i) 零点求和表示（卡点为 ξ'/ξ 部分分式，Hadamard 级）；
  (ii) 严格正性 `0 <`（还需「配对级数非零」：若和为零则每个
  `1 - cos(nθ_ρ) = 0`，即 `(1-1/ρ)ⁿ = 1` 对所有零点成立，但这只有
  至多 `n-1` 个解 `ρ`，与 Hardy 定理给出的无穷多零点矛盾）。

## 证明纪律

无 `sorry`/`admit`/新公理；公理审计见 `Test/XiFunctionAxiomAudit.lean`。
-/

import RiemannExplorer.LiZeroSumConvergence

open Complex ComplexConjugate
open scoped BigOperators

namespace RiemannExplorer

/-- 配对项是「主项 + 其共轭」：`liPairedTerm n ρ = ↑(2·Re(1-(1-1/ρ)ⁿ))`。 -/
theorem liPairedTerm_eq_ofReal_two_mul_re (n : ℕ) (ρ : ℂ) :
    liPairedTerm n ρ = ((2 * ((1 : ℂ) - (1 - 1 / ρ) ^ n).re : ℝ) : ℂ) := by
  unfold liPairedTerm
  have h1 : (1 : ℂ) - (1 - 1 / conj ρ) ^ n = conj ((1 : ℂ) - (1 - 1 / ρ) ^ n) := by
    simp [map_sub, map_one, map_pow, one_div]
  rw [h1]
  exact Complex.add_conj _

/-- 配对项是实数（无条件）。 -/
theorem liPairedTerm_im (n : ℕ) (ρ : ℂ) : (liPairedTerm n ρ).im = 0 := by
  rw [liPairedTerm_eq_ofReal_two_mul_re]
  exact Complex.ofReal_im _

/-- 配对项的实部：`2·(1 - Re((1-1/ρ)ⁿ))`（无条件）。 -/
theorem liPairedTerm_re (n : ℕ) (ρ : ℂ) :
    (liPairedTerm n ρ).re = 2 * (1 - (((1 : ℂ) - 1 / ρ) ^ n).re) := by
  rw [liPairedTerm_eq_ofReal_two_mul_re, Complex.ofReal_re, Complex.sub_re, Complex.one_re]

/-- 临界线上的恒等式：`ρ.re = 1/2` 时 `‖ρ - 1‖² = ‖ρ‖²`（按 normSq 展开）。 -/
theorem normSq_sub_one_eq_normSq_of_re_eq_half {ρ : ℂ} (h : ρ.re = 1 / 2) :
    Complex.normSq (ρ - 1) = Complex.normSq ρ := by
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, h]
  ring

/-- 临界线上的关键范数恒等式：`ρ.re = 1/2` 时 `‖1 - 1/ρ‖ = 1`。
因为 `1 - 1/ρ = (ρ-1)/ρ` 而 `‖ρ-1‖ = ‖ρ‖`。 -/
theorem norm_one_sub_inv_of_re_eq_half {ρ : ℂ} (h : ρ.re = 1 / 2) :
    ‖(1 : ℂ) - 1 / ρ‖ = 1 := by
  have hρ : ρ ≠ 0 := by
    intro hz
    rw [hz, Complex.zero_re] at h
    norm_num at h
  have h1 : (1 : ℂ) - 1 / ρ = (ρ - 1) / ρ := by field_simp
  rw [h1, norm_div]
  have h2 : ‖ρ - 1‖ = ‖ρ‖ := by
    rw [Complex.norm_def, Complex.norm_def, normSq_sub_one_eq_normSq_of_re_eq_half h]
  rw [h2]
  exact div_self (norm_pos_iff.mpr hρ).ne'

/-- **逐项非负性**：`ρ.re = 1/2` 时配对项实部非负。
这是 `1 - (1-1/ρ)ⁿ = 1 - e^{inθ}`、`Re = 1 - cos(nθ) ≥ 0` 的形式化。 -/
theorem liPairedTerm_re_nonneg_of_re_eq_half {ρ : ℂ} (h : ρ.re = 1 / 2) (n : ℕ) :
    0 ≤ (liPairedTerm n ρ).re := by
  rw [liPairedTerm_re]
  have hnorm : ‖((1 : ℂ) - 1 / ρ) ^ n‖ = 1 := by
    rw [norm_pow, norm_one_sub_inv_of_re_eq_half h, one_pow]
  have hre : (((1 : ℂ) - 1 / ρ) ^ n).re ≤ 1 :=
    (Complex.re_le_norm _).trans_eq hnorm
  linarith

/-- RH 下的逐项非负性：每个上半平面零点的配对项实部非负。 -/
theorem liPairedTerm_re_nonneg_of_rh (hRH : RiemannHypothesis.Statement) (n : ℕ)
    (ρ : UpperHalfPlaneNontrivialZero) : 0 ≤ (liPairedTerm n (ρ : ℂ)).re :=
  liPairedTerm_re_nonneg_of_re_eq_half (hRH _ ρ.2.1) n

/-- RH 下配对零点级数（收敛性已由 `summable_liPairedTerm` 给出）的实部非负。
注意 `tsum_nonneg` 不需要可和性前提（不可和时 `∑'` 按约定为零），
但本例中级数确实收敛。 -/
theorem tsum_liPairedTerm_re_nonneg_of_rh (hRH : RiemannHypothesis.Statement) (n : ℕ) :
    0 ≤ (∑' ρ : UpperHalfPlaneNontrivialZero, liPairedTerm n (ρ : ℂ)).re := by
  have hnn : ∀ ρ : UpperHalfPlaneNontrivialZero, 0 ≤ (liPairedTerm n (ρ : ℂ)).re :=
    liPairedTerm_re_nonneg_of_rh hRH n
  have heq : (fun ρ : UpperHalfPlaneNontrivialZero ↦ liPairedTerm n (ρ : ℂ)) =
      fun ρ : UpperHalfPlaneNontrivialZero ↦
        (((liPairedTerm n (ρ : ℂ)).re : ℝ) : ℂ) := by
    funext ρ
    refine Complex.ext ?_ ?_
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im]
      exact liPairedTerm_im n ρ
  rw [heq, ← Complex.ofReal_tsum, Complex.ofReal_re]
  exact tsum_nonneg hnn

/-- **正向方向的条件归约**（剩余缺口的精确形态）：
若零点求和表示 `li_zero_sum_representation_target` 成立，则 RH 蕴含
`0 ≤ (liCoefficient n).re`（对一切 `n ≥ 1`）。

`rh_implies_li_criterion_target` 的完整剩余缺口因此分离为：
1. 零点求和表示（分析卡点：ξ'/ξ 部分分式展开，Hadamard 因子分解级，
   Mathlib 缺失；级数收敛性已由 `summable_li_zero_sum_terms` 解决）；
2. 严格正性 `0 <`（组合卡点：配对级数非零——若和为零，则每项
   `1 - cos(nθ_ρ) = 0` 即 `(1-1/ρ)ⁿ = 1` 对所有零点成立，至多 `n-1`
   个解，与 Hardy 定理的无穷多零点矛盾）。 -/
theorem liCoefficient_re_nonneg_of_representation_of_rh
    (hrep : li_zero_sum_representation_target) (hRH : RiemannHypothesis.Statement)
    (n : ℕ) (hn : 1 ≤ n) : 0 ≤ (liCoefficient n).re := by
  rw [hrep n hn]
  exact tsum_liPairedTerm_re_nonneg_of_rh hRH n

end RiemannExplorer
