/-
# ξ'/ξ 部分分式展开：配对 Mittag-Leffler 级数的解析性（Hadamard 切片三）

本文件是「ξ'/ξ − B − Σ 配对项 = 整函数」论证的**函数论一半**：
配对 Mittag-Leffler 级数不只是逐点收敛
（`summable_xiPairedMittagLefflerTerm`），而且

1. 在任意紧致集上**一致收敛**
   （`tendstoUniformlyOn_tsum_xiPairedMittagLefflerTerm_of_isCompact`）；
2. 其和函数在每个满足 `ξ(s₀) ≠ 0` 的点 `s₀` 处**复可微**
   （`differentiableAt_tsum_xiPairedMittagLefflerTerm`），
   进而在开集 `{s | ξ s ≠ 0}` 上 `DifferentiableOn`
   （`differentiableOn_tsum_xiPairedMittagLefflerTerm`）。

## 证明路线（Weierstrass）

设 `F(s) = Σ_ρ term(s, ρ)`，`term(s, ρ) = [1/(s-ρ) + 1/ρ] + [1/(s-conjρ) + 1/conjρ]`。

- **高/低拆分**：对阈值 `B`，把 `term` 拆成
  `lowTerm`（`‖ρ‖ < B`，有限支撑：落入 `nontrivialZerosFinset B` 的原像）
  与 `highTerm`（`‖ρ‖ ≥ B`）。低部是有限和，解析性逐项处理；高部用
  Weierstrass M 判别法。
- **M 判别法**（`tendstoUniformlyOn_tsum`）：在 `‖s‖ ≤ r` 上取
  `B := max 2 (2r)`，则高部各项被 `(8(r+1)+2)·‖ρ‖⁻²` 一致控制
  （`norm_xiPairedMittagLefflerTerm_le`，因 `2‖s‖ ≤ ‖ρ‖`），
  后者对零点可和（`summable_norm_inv_sq_upperZeros`）。
  紧致集 `K` 有界（`IsCompact.isBounded`），故级数在 `K` 上一致收敛。
- **逐项微分**（`differentiableOn_tsum_of_summable_norm`，复分析
  Weierstrass 定理）：在球 `ball s₀ 1` 上取 `B := max 2 (2(‖s₀‖+1))`，
  高部各项在球上可微（`‖s‖ < ‖s₀‖+1 ≤ ‖ρ‖/2 < ‖ρ‖` 给出 `s ≠ ρ, conjρ`）
  且一致有界，故高部和在球上 `DifferentiableOn`，在 `s₀` 处
  `DifferentiableAt`。
- **低部**：有限支撑使 `∑'` 化为有限和（`tsum_eq_sum`），每项在
  `s₀` 可微（`ξ(s₀) ≠ 0` 蕴含 `s₀ ≠ ρ`（ξ 的零点刻画
  `xiFunction_eq_zero_iff_isNontrivialZero`）且 `s₀ ≠ conjρ`
  （经 `xiFunction_conj`），从而分母非零）。

## 与整函数目标的关系

`xi_partial_fraction_expansion_target` 的差函数
`D(s) := ξ'(s)/ξ(s) − B − F(s)` 现在在 `{s | ξ s ≠ 0}` 上有定义且
（在表示定理成立处）解析。剩余缺口：

1. **可去奇点**：在每个零点 `ρ` 处，`ξ'/ξ` 有留数为重数的一阶极点，
   `F` 有留数为 1（按不同零点计）的一阶极点，差 `D` 可去
   ——这需要留数计算与 Riemann 可去奇点定理；
2. **增长阶**：`|ξ|` 的增长阶 `≤ 1`（Gamma 界 + Phragmén–Lindelöf），
   配合 `F` 的估计给出 `D` 有界/为常数；
3. **配对与重数约定**的拼接（见 `XiPartialFraction.lean` 文件头）。

## 证明纪律

无 `sorry`/`admit`/新公理；公理审计见 `Test/XiFunctionAxiomAudit.lean`。
-/

import RiemannExplorer.XiPartialFraction
import Mathlib.Analysis.Complex.LocallyUniformLimit

open Complex ComplexConjugate
open scoped BigOperators

namespace RiemannExplorer

/-- ξ'/ξ 配对 Mittag-Leffler 级数的和函数（按 `ρ ↔ conj ρ` 配对）。 -/
noncomputable def xiPairedMittagLefflerSum (s : ℂ) : ℂ :=
  ∑' ρ : UpperHalfPlaneNontrivialZero, xiPairedMittagLefflerTerm s (ρ : ℂ)

/-- 逐项可微性：`s₀ ≠ ρ` 且 `s₀ ≠ conjρ` 时，配对 Mittag-Leffler 项
（作为 `s` 的函数）在 `s₀` 复可微。 -/
theorem differentiableAt_xiPairedMittagLefflerTerm {s₀ ρ : ℂ} (hρ : s₀ ≠ ρ)
    (hρc : s₀ ≠ conj ρ) :
    DifferentiableAt ℂ (fun s => xiPairedMittagLefflerTerm s ρ) s₀ := by
  unfold xiPairedMittagLefflerTerm
  refine DifferentiableAt.add (DifferentiableAt.add ?_ ?_) (DifferentiableAt.add ?_ ?_)
  · exact DifferentiableAt.div (differentiableAt_const _) (differentiableAt_id.sub
      (differentiableAt_const _)) (sub_ne_zero.mpr hρ)
  · exact differentiableAt_const _
  · exact DifferentiableAt.div (differentiableAt_const _) (differentiableAt_id.sub
      (differentiableAt_const _)) (sub_ne_zero.mpr hρc)
  · exact differentiableAt_const _

/-! ## 高/低拆分 -/

/-- 配对项按阈值 `B` 的高/低拆分（逐点恒等式）。 -/
theorem xiPairedMittagLefflerTerm_eq_low_add_high (B : ℝ)
    (ρ : UpperHalfPlaneNontrivialZero) (s : ℂ) :
    xiPairedMittagLefflerTerm s (ρ : ℂ) =
      (if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) +
        (if B ≤ ‖(ρ : ℂ)‖ then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) := by
  by_cases h : ‖(ρ : ℂ)‖ < B
  · rw [if_pos h, if_neg (not_le_of_gt h), add_zero]
  · rw [if_neg h, if_pos (le_of_not_gt h), zero_add]

/-- 低部支撑事实：`‖ρ‖ < B` 的零点落入 `nontrivialZerosFinset B` 的原像；
原像之外低部为零。 -/
theorem xiPairedMittagLefflerTerm_low_eq_zero_of_not_mem (B : ℝ) (s : ℂ)
    (ρ : UpperHalfPlaneNontrivialZero)
    (hρ : ρ ∉ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
      (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn) :
    (if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) = 0 := by
  by_cases hlt : ‖(ρ : ℂ)‖ < B
  · exfalso
    apply hρ
    rw [Finset.mem_preimage, PrimeNumberTheorem.mem_nontrivialZerosFinset]
    exact ⟨ρ.2.1, (Complex.abs_im_le_norm _).trans hlt.le⟩
  · exact if_neg hlt

/-- 低部可和（有限支撑）。 -/
theorem summable_xiPairedMittagLefflerTerm_low (B : ℝ) (s : ℂ) :
    Summable fun ρ : UpperHalfPlaneNontrivialZero ↦
      if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0 := by
  classical
  apply summable_of_ne_finset_zero
    (s := (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
      (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn)
  intro ρ hρ
  exact xiPairedMittagLefflerTerm_low_eq_zero_of_not_mem B s ρ hρ

/-- 高部可和（由整体可和减低部可和）。 -/
theorem summable_xiPairedMittagLefflerTerm_high (B : ℝ) (s : ℂ) :
    Summable fun ρ : UpperHalfPlaneNontrivialZero ↦
      if B ≤ ‖(ρ : ℂ)‖ then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0 := by
  classical
  have h : (fun ρ : UpperHalfPlaneNontrivialZero ↦
        if B ≤ ‖(ρ : ℂ)‖ then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) =
      (fun ρ : UpperHalfPlaneNontrivialZero ↦ xiPairedMittagLefflerTerm s (ρ : ℂ)) -
        (fun ρ : UpperHalfPlaneNontrivialZero ↦
          if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) := by
    funext ρ
    rw [Pi.sub_apply]
    by_cases hlt : ‖(ρ : ℂ)‖ < B
    · rw [if_pos hlt, if_neg (not_le_of_gt hlt), sub_self]
    · rw [if_neg hlt, if_pos (le_of_not_gt hlt), sub_zero]
  rw [h]
  exact (summable_xiPairedMittagLefflerTerm s).sub
    (summable_xiPairedMittagLefflerTerm_low B s)

/-- 级数的高/低拆分：`F = F_low + F_high`（逐点）。 -/
theorem xiPairedMittagLefflerSum_eq_low_add_high (B : ℝ) (s : ℂ) :
    xiPairedMittagLefflerSum s =
      (∑' ρ : UpperHalfPlaneNontrivialZero,
        if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) +
        (∑' ρ : UpperHalfPlaneNontrivialZero,
          if B ≤ ‖(ρ : ℂ)‖ then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) := by
  rw [← Summable.tsum_add (summable_xiPairedMittagLefflerTerm_low B s)
    (summable_xiPairedMittagLefflerTerm_high B s)]
  exact tsum_congr fun ρ => xiPairedMittagLefflerTerm_eq_low_add_high B ρ s

/-- 低部和等于有限集上的有限和（`tsum_eq_sum`）。 -/
theorem tsum_xiPairedMittagLefflerTerm_low_eq_sum (B : ℝ) (s : ℂ) :
    (∑' ρ : UpperHalfPlaneNontrivialZero,
      if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) =
      ∑ ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
          (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn,
        (if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) := by
  classical
  exact tsum_eq_sum fun ρ hρ => xiPairedMittagLefflerTerm_low_eq_zero_of_not_mem B s ρ hρ

/-! ## 主定理一：和函数在 ξ 非零点处可微 -/

/-- 高部和在开球 `ball s₀ 1` 上复可微（Weierstrass 逐项微分）：
取 `B := max 2 (2(‖s₀‖+1))`，球内 `‖s‖ < ‖s₀‖+1 ≤ ‖ρ‖/2 < ‖ρ‖`
给出 `s ≠ ρ, conjρ`（各项可微），且各项被 `(8(‖s₀‖+2)+2)·‖ρ‖⁻²`
一致控制（M 判别法主项对零点可和）。 -/
theorem differentiableOn_tsum_xiPairedMittagLefflerTerm_high (s₀ : ℂ) :
    DifferentiableOn ℂ
      (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero,
        if max 2 (2 * (‖s₀‖ + 1)) ≤ ‖(ρ : ℂ)‖ then
          xiPairedMittagLefflerTerm s (ρ : ℂ) else 0)
      (Metric.ball s₀ 1) := by
  classical
  set B := max 2 (2 * (‖s₀‖ + 1)) with hB
  have hball : ∀ s ∈ Metric.ball s₀ 1, ‖s‖ < ‖s₀‖ + 1 := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have h := norm_sub_norm_le s s₀
    have hs0 := norm_nonneg s
    linarith
  refine differentiableOn_tsum_of_summable_norm
    (u := fun ρ : UpperHalfPlaneNontrivialZero =>
      (8 * (‖s₀‖ + 2) + 2) * ‖(ρ : ℂ)‖⁻¹ ^ 2)
    (summable_norm_inv_sq_upperZeros.mul_left _) ?_ Metric.isOpen_ball ?_
  · intro ρ
    by_cases hρB : B ≤ ‖(ρ : ℂ)‖
    · have hFρ : (fun s => if B ≤ ‖(ρ : ℂ)‖ then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) =
          fun s => xiPairedMittagLefflerTerm s (ρ : ℂ) := funext fun s => if_pos hρB
      rw [hFρ]
      intro s hs
      have hsn : ‖s‖ < ‖(ρ : ℂ)‖ := by
        have h1 := hball s hs
        have h2 : 2 * (‖s₀‖ + 1) ≤ B := le_max_right _ _
        have hs0 := norm_nonneg s
        linarith
      have hsρ : s ≠ (ρ : ℂ) := fun h => by rw [h] at hsn; exact lt_irrefl _ hsn
      have hsρc : s ≠ conj (ρ : ℂ) := fun h => by
        have h3 : ‖s‖ = ‖(ρ : ℂ)‖ := by rw [h, Complex.norm_conj]
        linarith
      exact (differentiableAt_xiPairedMittagLefflerTerm hsρ hsρc).differentiableWithinAt
    · have hFρ : (fun s => if B ≤ ‖(ρ : ℂ)‖ then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) =
          fun _ => 0 := funext fun s => if_neg hρB
      rw [hFρ]
      exact differentiableOn_const _
  · intro ρ s hs
    by_cases hρB : B ≤ ‖(ρ : ℂ)‖
    · rw [if_pos hρB]
      have h1 := hball s hs
      have hρ2 : 2 ≤ ‖(ρ : ℂ)‖ := le_trans (le_max_left _ _) hρB
      have hρs : 2 * ‖s‖ ≤ ‖(ρ : ℂ)‖ := by
        have h2 : 2 * (‖s₀‖ + 1) ≤ B := le_max_right _ _
        linarith
      have hre : |(ρ : ℂ).re| ≤ 1 := by
        have h3 := ρ.2.1.2.1
        have h4 := ρ.2.1.2.2
        rw [abs_le]
        constructor <;> linarith
      exact (norm_xiPairedMittagLefflerTerm_le hρ2 hρs hre).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    · rw [if_neg hρB, norm_zero]
      positivity

/-- **主定理一**：配对 Mittag-Leffler 级数的和函数在每个满足
`ξ(s₀) ≠ 0` 的点 `s₀` 处复可微。

`ξ(s₀) ≠ 0` 蕴含 `s₀` 避开所有零点及其共轭：`s₀ = ρ` 会给出
`ξ(s₀) = ξ(ρ) = 0`（`xiFunction_eq_zero_iff_isNontrivialZero`）；
`s₀ = conjρ` 会给出 `ξ(s₀) = conj(ξ(ρ)) = 0`（`xiFunction_conj`）。
低部是有限和（`tsum_eq_sum`），逐项可微；高部在开球上
`DifferentiableOn`（`differentiableOn_tsum_xiPairedMittagLefflerTerm_high`）。 -/
theorem differentiableAt_tsum_xiPairedMittagLefflerTerm {s₀ : ℂ}
    (hξ : xiFunction s₀ ≠ 0) :
    DifferentiableAt ℂ (fun s => xiPairedMittagLefflerSum s) s₀ := by
  classical
  set B := max 2 (2 * (‖s₀‖ + 1)) with hB
  set F₀ := (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
      (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn
  -- ξ(s₀) ≠ 0 ⇒ s₀ 避开零点与其共轭
  have hsρ : ∀ ρ : UpperHalfPlaneNontrivialZero, s₀ ≠ (ρ : ℂ) := by
    intro ρ h
    apply hξ
    rw [h]
    exact (xiFunction_eq_zero_iff_isNontrivialZero ρ.2.1.2.1 ρ.2.1.2.2).mpr ρ.2.1
  have hsρc : ∀ ρ : UpperHalfPlaneNontrivialZero, s₀ ≠ conj (ρ : ℂ) := by
    intro ρ h
    apply hξ
    rw [h, xiFunction_conj,
      (xiFunction_eq_zero_iff_isNontrivialZero ρ.2.1.2.1 ρ.2.1.2.2).mpr ρ.2.1]
    exact map_zero _
  -- 函数分解 F = F_low + F_high
  have hdecomp : (fun s => xiPairedMittagLefflerSum s) =
      (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero,
        if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) +
        (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero,
          if B ≤ ‖(ρ : ℂ)‖ then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) := by
    funext s
    simp only [Pi.add_apply]
    exact xiPairedMittagLefflerSum_eq_low_add_high B s
  rw [hdecomp]
  refine DifferentiableAt.add ?_ ?_
  · -- 低部：有限和，逐项可微
    rw [show (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero,
          if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) =
        fun s => ∑ ρ ∈ F₀,
          (if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0)
      from funext fun s => tsum_xiPairedMittagLefflerTerm_low_eq_sum B s]
    rw [show (fun s => ∑ ρ ∈ F₀,
          (if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0)) =
        (∑ ρ ∈ F₀, fun s =>
          if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0)
      from funext fun s => by rw [Finset.sum_apply]]
    refine DifferentiableAt.sum fun ρ _ => ?_
    by_cases hlt : ‖(ρ : ℂ)‖ < B
    · rw [show (fun s => if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) =
          fun s => xiPairedMittagLefflerTerm s (ρ : ℂ) from funext fun s => if_pos hlt]
      exact differentiableAt_xiPairedMittagLefflerTerm (hsρ ρ) (hsρc ρ)
    · rw [show (fun s => if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) =
          fun _ => 0 from funext fun s => if_neg hlt]
      exact differentiableAt_const _
  · -- 高部：球上 DifferentiableOn ⇒ s₀ 处 DifferentiableAt
    exact (differentiableOn_tsum_xiPairedMittagLefflerTerm_high s₀).differentiableAt
      (Metric.ball_mem_nhds s₀ one_pos)

/-- 与 `differentiableAt_tsum_xiPairedMittagLefflerTerm` 同一论证，但把
「`s₀` 不等于任何上半零点、也不等于任何上半零点的共轭」作为**显式假设**
（原定理由 `xiFunction s₀ ≠ 0` 推出这两条）。用于 `s₀` 本身是 ξ 的**实**零点
（从而自动避开所有非实零点及其共轭）的情形。 -/
theorem differentiableAt_tsum_xiPairedMittagLefflerTerm_of_ne {s₀ : ℂ}
    (hsρ : ∀ ρ : UpperHalfPlaneNontrivialZero, s₀ ≠ (ρ : ℂ))
    (hsρc : ∀ ρ : UpperHalfPlaneNontrivialZero, s₀ ≠ conj (ρ : ℂ)) :
    DifferentiableAt ℂ (fun s => xiPairedMittagLefflerSum s) s₀ := by
  classical
  set B := max 2 (2 * (‖s₀‖ + 1)) with hB
  set F₀ := (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
      (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn
  -- 函数分解 F = F_low + F_high
  have hdecomp : (fun s => xiPairedMittagLefflerSum s) =
      (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero,
        if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) +
        (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero,
          if B ≤ ‖(ρ : ℂ)‖ then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) := by
    funext s
    simp only [Pi.add_apply]
    exact xiPairedMittagLefflerSum_eq_low_add_high B s
  rw [hdecomp]
  refine DifferentiableAt.add ?_ ?_
  · -- 低部：有限和，逐项可微
    rw [show (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero,
          if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) =
        fun s => ∑ ρ ∈ F₀,
          (if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0)
      from funext fun s => tsum_xiPairedMittagLefflerTerm_low_eq_sum B s]
    rw [show (fun s => ∑ ρ ∈ F₀,
          (if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0)) =
        (∑ ρ ∈ F₀, fun s =>
          if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0)
      from funext fun s => by rw [Finset.sum_apply]]
    refine DifferentiableAt.sum fun ρ _ => ?_
    by_cases hlt : ‖(ρ : ℂ)‖ < B
    · rw [show (fun s => if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) =
          fun s => xiPairedMittagLefflerTerm s (ρ : ℂ) from funext fun s => if_pos hlt]
      exact differentiableAt_xiPairedMittagLefflerTerm (hsρ ρ) (hsρc ρ)
    · rw [show (fun s => if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) =
          fun _ => 0 from funext fun s => if_neg hlt]
      exact differentiableAt_const _
  · -- 高部：球上 DifferentiableOn ⇒ s₀ 处 DifferentiableAt
    exact (differentiableOn_tsum_xiPairedMittagLefflerTerm_high s₀).differentiableAt
      (Metric.ball_mem_nhds s₀ one_pos)

/-- 和函数在开集 `{s | ξ s ≠ 0}` 上 `DifferentiableOn`。 -/
theorem differentiableOn_tsum_xiPairedMittagLefflerTerm :
    DifferentiableOn ℂ xiPairedMittagLefflerSum {s : ℂ | xiFunction s ≠ 0} :=
  fun _s hs => (differentiableAt_tsum_xiPairedMittagLefflerTerm hs).differentiableWithinAt

/-! ## 主定理二：紧致集上的一致收敛性 -/

/-- **主定理二**（Weierstrass M 判别法）：配对 Mittag-Leffler 级数的
有限部分和网在任意紧致集 `K` 上一致收敛到级数和。

证明：`K` 有界（`IsCompact.isBounded`），设 `K ⊆ closedBall 0 r`，
取 `B := max 2 (2r)`。高部各项在 `K` 上被 `(8(r+1)+2)·‖ρ‖⁻²` 一致控制
（`norm_xiPairedLefflerTerm_le`），由 `tendstoUniformlyOn_tsum` 一致收敛；
低部的部分和网在包含有限支撑集 `F₀` 后恒等于低部和
（`Finset.sum_subset` + `tsum_eq_sum`），平凡一致收敛；
两部由 `TendstoUniformlyOn.add` 合并。 -/
theorem tendstoUniformlyOn_tsum_xiPairedMittagLefflerTerm_of_isCompact {K : Set ℂ}
    (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun u : Finset UpperHalfPlaneNontrivialZero => fun s =>
        ∑ ρ ∈ u, xiPairedMittagLefflerTerm s (ρ : ℂ))
      (fun s => xiPairedMittagLefflerSum s) Filter.atTop K := by
  classical
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  have hKr : ∀ s ∈ K, ‖s‖ ≤ max r 0 := by
    intro s hs
    have h := hr hs
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    exact h.trans (le_max_left _ _)
  set B := max 2 (2 * max r 0) with hB
  set F₀ := (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
      (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn
  set lowTerm := fun ρ : UpperHalfPlaneNontrivialZero => fun s : ℂ =>
      if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0 with hlow
  set highTerm := fun ρ : UpperHalfPlaneNontrivialZero => fun s : ℂ =>
      if B ≤ ‖(ρ : ℂ)‖ then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0 with hhigh
  -- 高部：M 判别法
  have hhighU : TendstoUniformlyOn
      (fun u : Finset UpperHalfPlaneNontrivialZero => fun s => ∑ ρ ∈ u, highTerm ρ s)
      (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero, highTerm ρ s) Filter.atTop K := by
    refine tendstoUniformlyOn_tsum
      (u := fun ρ : UpperHalfPlaneNontrivialZero => (8 * (max r 0 + 1) + 2) * ‖(ρ : ℂ)‖⁻¹ ^ 2)
      (summable_norm_inv_sq_upperZeros.mul_left _) fun ρ s hs => ?_
    show ‖(if B ≤ ‖(ρ : ℂ)‖ then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0)‖ ≤
      (8 * (max r 0 + 1) + 2) * ‖(ρ : ℂ)‖⁻¹ ^ 2
    by_cases hρB : B ≤ ‖(ρ : ℂ)‖
    · rw [if_pos hρB]
      have h1 := hKr s hs
      have hρ2 : 2 ≤ ‖(ρ : ℂ)‖ := le_trans (le_max_left _ _) hρB
      have hρs : 2 * ‖s‖ ≤ ‖(ρ : ℂ)‖ := le_trans
        (mul_le_mul_of_nonneg_left h1 (by norm_num)) (le_max_right _ _ |>.trans hρB)
      have hre : |(ρ : ℂ).re| ≤ 1 := by
        have h3 := ρ.2.1.2.1
        have h4 := ρ.2.1.2.2
        rw [abs_le]
        constructor <;> linarith
      exact (norm_xiPairedMittagLefflerTerm_le hρ2 hρs hre).trans
        (mul_le_mul_of_nonneg_right (by linarith [h1]) (by positivity))
    · rw [if_neg hρB, norm_zero]
      positivity
  -- 低部：部分和网最终恒等于低部和
  have hlowU : TendstoUniformlyOn
      (fun u : Finset UpperHalfPlaneNontrivialZero => fun s => ∑ ρ ∈ u, lowTerm ρ s)
      (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero, lowTerm ρ s) Filter.atTop K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Filter.eventually_ge_atTop F₀] with u hu s _hs
    have hsum : ∑ ρ ∈ u, lowTerm ρ s = ∑' ρ : UpperHalfPlaneNontrivialZero, lowTerm ρ s := by
      have h1 : ∑ ρ ∈ u, lowTerm ρ s = ∑ ρ ∈ F₀, lowTerm ρ s := by
        symm
        exact Finset.sum_subset hu fun ρ hρu hρF => by
          rw [hlow]
          exact xiPairedMittagLefflerTerm_low_eq_zero_of_not_mem B s ρ hρF
      have h2 : (∑' ρ : UpperHalfPlaneNontrivialZero, lowTerm ρ s) =
          ∑ ρ ∈ F₀, lowTerm ρ s := by
        rw [hlow]
        exact tsum_xiPairedMittagLefflerTerm_low_eq_sum B s
      rw [h1, h2]
    rw [hsum, dist_self]
    exact hε
  -- 合并：部分和网与极限都按高/低拆分
  have hnet : (fun u : Finset UpperHalfPlaneNontrivialZero => fun s =>
        ∑ ρ ∈ u, xiPairedMittagLefflerTerm s (ρ : ℂ)) =
      (fun u => fun s => ∑ ρ ∈ u, lowTerm ρ s) + (fun u => fun s => ∑ ρ ∈ u, highTerm ρ s) := by
    funext u s
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ρ _ => by
      rw [hlow, hhigh]
      exact xiPairedMittagLefflerTerm_eq_low_add_high B ρ s
  have hlim : (fun s => xiPairedMittagLefflerSum s) =
      (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero, lowTerm ρ s) +
        (fun s => ∑' ρ : UpperHalfPlaneNontrivialZero, highTerm ρ s) := by
    funext s
    simp only [Pi.add_apply]
    rw [hlow, hhigh]
    exact xiPairedMittagLefflerSum_eq_low_add_high B s
  rw [hnet, hlim]
  exact hlowU.add hhighU

end RiemannExplorer
