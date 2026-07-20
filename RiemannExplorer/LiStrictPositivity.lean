/-
# 严格正性切片：配对级数非零（RH 下 Li 系数的严格正性归约）

本文件补上正向方向「RH ⇒ Li 准则」的**严格正性**一半：在零点求和表示
`li_zero_sum_representation_target` 与 RH 之下，`0 < (liCoefficient n).re`
对一切 `n ≥ 1` 成立。配合无条件的实值性（`liCoefficient_im`），这把
`rh_implies_li_criterion_target` 的剩余缺口**精确压缩为只剩
零点求和表示一个**（`rh_implies_li_criterion_of_representation`）。

## 数学内容

矛盾论证。设 RH 成立且 `S_n := ∑' ρ, liPairedTerm n ρ` 的实部为零。
`LiPositivity.lean` 已证：配对项均为实数且实部
`(liPairedTerm n ρ).re = 2·(1 - Re((1-1/ρ)ⁿ)) ≥ 0`（RH 下
`‖1-1/ρ‖ = 1`）。非负实部级数和为零迫使每项实部为零
（`Summable.le_tsum`），即 `Re((1-1/ρ)ⁿ) = 1`；而 `‖(1-1/ρ)ⁿ‖ = 1`，
实部为 1 且模为 1 的复数只能是 1，故

```text
(1 - 1/ρ)ⁿ = 1    对所有上半平面非平凡零点 ρ 成立。
```

但 `ρ ↦ 1 - 1/ρ` 单射，而 `wⁿ = 1` 只有有限个解（多项式 `Xⁿ - 1`
的根集有限），故满足上式的零点只有**有限多个**
（`finite_upperZeros_pow_eq_one`）；另一方面 Hardy 定理
（`HardyTheorem.hardy_zeros_unbounded_target_proved`，仓库已证）
给出任意高度的临界线零点 `1/2 + it`（`t ≥ 1 > 0`），它们自动是
上半平面非平凡零点，故上半平面非平凡零点**无穷多**
（`infinite_upperZeros`，无条件）。矛盾。

## 主要定理

- `infinite_upperZeros`：`UpperHalfPlaneNontrivialZero` 是无穷类型
  （无条件，Hardy 定理的直接推论）；
- `finite_upperZeros_pow_eq_one`：满足 `(1-1/ρ)ⁿ = 1` 的上半平面零点
  只有有限个（`n ≥ 1`）；
- `liPairedTerm_eq_one_of_re_eq_zero_of_rh`：RH 下配对项实部为零
  蕴含 `(1-1/ρ)ⁿ = 1`；
- `liCoefficient_re_pos_of_representation_of_rh`：**严格正性的条件归约**——
  表示定理 + RH ⇒ `0 < (liCoefficient n).re`；
- `rh_implies_li_criterion_of_representation`：**正向方向的条件证明**——
  表示定理 ⇒ `rh_implies_li_criterion_target`。至此正向方向只差
  零点求和表示（ξ'/ξ 部分分式恒等式，收敛性已由
  `summable_xiPairedMittagLefflerTerm` 解决）。

## 证明纪律

无 `sorry`/`admit`/新公理；公理审计见 `Test/XiFunctionAxiomAudit.lean`。
-/

import RiemannExplorer.LiPositivity
import RiemannExplorer.LiReality
import HardyTheorem.HardyIntegralContradiction

open Complex ComplexConjugate Polynomial
open scoped BigOperators

namespace RiemannExplorer

/-- **上半平面零点的无穷性（无条件）**：Hardy 定理
（`HardyTheorem.hardy_zeros_unbounded_target_proved`）给出任意高度
`t ≥ T` 的临界线零点 `1/2 + it`；取 `T = max (a+1) 1` 得 `t ≥ 1 > 0`，
而 `Re(1/2 + it) = 1/2 ∈ (0,1)`，故它自动是上半平面非平凡零点。
所有虚部组成的集合因此无上界、无穷，从而零点类型本身无穷。 -/
theorem infinite_upperZeros : Infinite UpperHalfPlaneNontrivialZero := by
  have hA : (Set.range fun ρ : UpperHalfPlaneNontrivialZero => (ρ : ℂ).im).Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨t, htT, ht0⟩ :=
      HardyTheorem.hardy_zeros_unbounded_target_proved (max (a + 1) 1)
    have him : (0.5 + Complex.I * (t : ℂ)).im = t := by norm_num [Complex.add_im]
    have hnt : RiemannHypothesis.IsNontrivialZero (0.5 + Complex.I * (t : ℂ)) :=
      ⟨ht0, by norm_num [Complex.add_re], by norm_num [Complex.add_re]⟩
    have ht1 : 1 ≤ t := le_trans (le_max_right (a + 1) 1) htT
    have hta : a < t := by
      have h := le_trans (le_max_left (a + 1) 1) htT
      linarith
    exact ⟨t, ⟨⟨(0.5 + Complex.I * (t : ℂ)), hnt, by rw [him]; linarith⟩, him⟩, hta⟩
  by_contra hni
  haveI : Finite UpperHalfPlaneNontrivialZero := Finite.of_not_infinite hni
  exact hA (Set.finite_range _)

/-- **单位根约束的有限性**：对 `n ≥ 1`，满足 `(1 - 1/ρ)ⁿ = 1` 的
上半平面非平凡零点只有有限个。
证明：`ρ ↦ 1 - 1/ρ` 单射（`inv_inj`），其像落在 `wⁿ = 1` 的解集内，
而后者是多项式 `Xⁿ - 1`（非零：在 `2` 处取值为 `2ⁿ - 1 ≠ 0`）的
根集，由 `Polynomial.finite_setOf_isRoot` 有限。 -/
theorem finite_upperZeros_pow_eq_one (n : ℕ) (hn : 1 ≤ n) :
    {ρ : UpperHalfPlaneNontrivialZero | (1 - 1 / (ρ : ℂ)) ^ n = 1}.Finite := by
  have hW : {w : ℂ | w ^ n = 1}.Finite := by
    have hp : (X ^ n - 1 : ℂ[X]) ≠ 0 := by
      intro h
      have h2 := congrArg (fun p : ℂ[X] => Polynomial.eval (2 : ℂ) p) h
      simp only [eval_sub, eval_pow, eval_X, eval_one, eval_zero] at h2
      rw [sub_eq_zero] at h2
      have h3 : ‖(2 : ℂ) ^ n‖ = ‖(1 : ℂ)‖ := congrArg (fun z : ℂ => ‖z‖) h2
      rw [norm_pow, norm_one, show ‖(2 : ℂ)‖ = 2 by norm_num] at h3
      have h4 : (1 : ℝ) < (2 : ℝ) ^ n := one_lt_pow₀ (by norm_num) (by omega)
      linarith
    have hroots := Polynomial.finite_setOf_isRoot hp
    have heq : {x : ℂ | Polynomial.IsRoot (X ^ n - 1) x} = {w : ℂ | w ^ n = 1} := by
      ext w
      simp [Polynomial.IsRoot, sub_eq_zero]
    rwa [heq] at hroots
  refine Set.Finite.of_finite_image
    (f := fun ρ : UpperHalfPlaneNontrivialZero => (1 : ℂ) - 1 / (ρ : ℂ)) ?_ ?_
  · apply hW.subset
    rintro w ⟨ρ, hρ, rfl⟩
    exact hρ
  · intro ρ _ σ _ h
    have h1 : (1 : ℂ) / (ρ : ℂ) = 1 / (σ : ℂ) := by
      have h' := congrArg (fun z => (1 : ℂ) - z) h
      simpa using h'
    rw [one_div, one_div] at h1
    exact Subtype.ext (inv_inj.mp h1)

/-- RH 下配对项实部为零当且仅当退化为单位根：
`(liPairedTerm n ρ).re = 0` 蕴含 `(1 - 1/ρ)ⁿ = 1`。
证明：实部 `= 2·(1 - Re((1-1/ρ)ⁿ)) = 0` 给出 `Re = 1`；RH 下
`‖(1-1/ρ)ⁿ‖ = 1`，由 `normSq` 展开得虚部为零，故该数等于 1。 -/
theorem liPairedTerm_eq_one_of_re_eq_zero_of_rh (hRH : RiemannHypothesis.Statement)
    (n : ℕ) (ρ : UpperHalfPlaneNontrivialZero)
    (h0 : (liPairedTerm n (ρ : ℂ)).re = 0) : (1 - 1 / (ρ : ℂ)) ^ n = 1 := by
  have hρrh : (ρ : ℂ).re = 1 / 2 := hRH _ ρ.2.1
  have h1 := liPairedTerm_re n (ρ : ℂ)
  rw [h0] at h1
  have hre1 : (((1 : ℂ) - 1 / (ρ : ℂ)) ^ n).re = 1 := by linarith
  have hzn : ‖((1 : ℂ) - 1 / (ρ : ℂ)) ^ n‖ = 1 := by
    rw [norm_pow, norm_one_sub_inv_of_re_eq_half hρrh, one_pow]
  have him0 : (((1 : ℂ) - 1 / (ρ : ℂ)) ^ n).im = 0 := by
    have h3 := Complex.normSq_apply (((1 : ℂ) - 1 / (ρ : ℂ)) ^ n)
    rw [Complex.normSq_eq_norm_sq, hzn, one_pow, hre1] at h3
    have h4 : (((1 : ℂ) - 1 / (ρ : ℂ)) ^ n).im *
        (((1 : ℂ) - 1 / (ρ : ℂ)) ^ n).im = 0 := by linarith
    exact mul_self_eq_zero.mp h4
  exact Complex.ext (by rw [Complex.one_re]; exact hre1)
    (by rw [Complex.one_im]; exact him0)

/-- **严格正性的条件归约**：表示定理 + RH ⇒ `0 < (liCoefficient n).re`
（对一切 `n ≥ 1`）。

证明：由表示定理 `(liCoefficient n).re = S_n.re`，而 RH 下
`S_n.re ≥ 0`（`tsum_liPairedTerm_re_nonneg_of_rh`）。若 `S_n.re = 0`，
非负实部级数（可和由 `summable_liPairedTerm` 经各项实性转移）和为零，
每项实部为零（`Summable.le_tsum` + 逐项非负），于是每个零点满足
`(1-1/ρ)ⁿ = 1`（`liPairedTerm_eq_one_of_re_eq_zero_of_rh`），与
`finite_upperZeros_pow_eq_one`（有限）和 `infinite_upperZeros`
（无穷）矛盾。 -/
theorem liCoefficient_re_pos_of_representation_of_rh
    (hrep : li_zero_sum_representation_target) (hRH : RiemannHypothesis.Statement)
    (n : ℕ) (hn : 1 ≤ n) : 0 < (liCoefficient n).re := by
  have hSnn := tsum_liPairedTerm_re_nonneg_of_rh hRH n
  have hS : (liCoefficient n).re =
      (∑' ρ : UpperHalfPlaneNontrivialZero, liPairedTerm n (ρ : ℂ)).re := by
    rw [hrep n hn]
    congr 1
  rw [hS]
  refine lt_of_le_of_ne' hSnn fun hS0 => ?_
  have heq : (fun ρ : UpperHalfPlaneNontrivialZero ↦ liPairedTerm n (ρ : ℂ)) =
      fun ρ : UpperHalfPlaneNontrivialZero ↦
        (((liPairedTerm n (ρ : ℂ)).re : ℝ) : ℂ) := by
    funext ρ
    refine Complex.ext ?_ ?_
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im]
      exact liPairedTerm_im n ρ
  have hfsum : Summable fun ρ : UpperHalfPlaneNontrivialZero ↦
      (liPairedTerm n (ρ : ℂ)).re := by
    have hC := summable_liPairedTerm n
    rw [heq] at hC
    exact Complex.summable_ofReal.mp hC
  have hSre : (∑' ρ : UpperHalfPlaneNontrivialZero, liPairedTerm n (ρ : ℂ)).re =
      ∑' ρ : UpperHalfPlaneNontrivialZero, (liPairedTerm n (ρ : ℂ)).re := by
    rw [heq, ← Complex.ofReal_tsum, Complex.ofReal_re]
  have hterm0 : ∀ ρ : UpperHalfPlaneNontrivialZero, (liPairedTerm n (ρ : ℂ)).re = 0 := by
    intro ρ
    have hle := Summable.le_tsum hfsum ρ (fun σ _ => liPairedTerm_re_nonneg_of_rh hRH n σ)
    rw [← hSre, hS0] at hle
    exact le_antisymm hle (liPairedTerm_re_nonneg_of_rh hRH n ρ)
  have hall : ∀ ρ : UpperHalfPlaneNontrivialZero, (1 - 1 / (ρ : ℂ)) ^ n = 1 :=
    fun ρ => liPairedTerm_eq_one_of_re_eq_zero_of_rh hRH n ρ (hterm0 ρ)
  have hfin := finite_upperZeros_pow_eq_one n hn
  rw [Set.eq_univ_of_forall hall] at hfin
  haveI := infinite_upperZeros
  exact Set.infinite_univ hfin

/-- **正向方向的条件证明**：零点求和表示
`li_zero_sum_representation_target` 蕴含
`rh_implies_li_criterion_target`（RH ⇒ Li 准则）。
虚部由 `liCoefficient_im`（无条件）给出，严格正性由
`liCoefficient_re_pos_of_representation_of_rh` 给出。
至此正向方向的剩余缺口**只有**零点求和表示本身。 -/
theorem rh_implies_li_criterion_of_representation
    (hrep : li_zero_sum_representation_target) : rh_implies_li_criterion_target :=
  fun hRH n hn =>
    ⟨liCoefficient_im n, liCoefficient_re_pos_of_representation_of_rh hrep hRH n hn⟩

end RiemannExplorer
