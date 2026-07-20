/-
# ξ'/ξ 部分分式展开：配对 Mittag-Leffler 项的收敛性与商常数识别
（Hadamard 切片一、二）

本文件是 `li_zero_sum_representation_target` 剩余硬卡点——
ξ'/ξ 部分分式展开（Hadamard 因子分解级，Mathlib 缺失）——的
前两个最小可证切片：展开式右端配对项级数的无条件收敛性，以及
商常数的条件识别（`B = ξ'(0)/ξ(0)`）。展开式本身登记为
`def ... : Prop` 目标 `xi_partial_fraction_expansion_target`。

## 数学内容

Hadamard 因子分解给出（形式地）

```text
ξ'(s)/ξ(s) = B + Σ_ρ [1/(s - ρ) + 1/ρ]
```

其中 `ρ` 走遍 ξ 的零点（即 ζ 的非平凡零点）。按 `ρ ↔ conj ρ` 配对，
定义配对 Mittag-Leffler 项

```text
xiPairedMittagLefflerTerm s ρ = [1/(s-ρ) + 1/ρ] + [1/(s-conjρ) + 1/conjρ]
```

本文件证明：

- **代数分解**（`xiPairedMittagLefflerTerm_eq`）：配对项等于
  「主部 + 常数部」，

  ```text
  = 2(s - ↑ρ.re) / ((s - ρ)(s - conj ρ)) + ↑(2·ρ.re / normSq ρ)
  ```

  分子用到 `ρ + conj ρ = ↑(2·ρ.re)`（`Complex.add_conj`），
  常数部用 `1/ρ + 1/conjρ = 2·Re(ρ⁻¹) = 2·ρ.re/normSq ρ`
  （与 `norm_liPairedTerm_le` 相同的恒等式）。

- **范数界**（`norm_xiPairedMittagLefflerTerm_le`）：对 `‖ρ‖ ≥ 2`、
  `2‖s‖ ≤ ‖ρ‖`、`|ρ.re| ≤ 1`，

  ```text
  ‖xiPairedMittagLefflerTerm s ρ‖ ≤ (8·(‖s‖+1) + 2)·‖ρ‖⁻²
  ```

  关键：`|ρ.re| ≤ 1` 蕴含 `‖s - ρ‖ ≥ ‖ρ‖ - ‖s‖ ≥ ‖ρ‖/2`，
  分母 `‖(s-ρ)(s-conjρ)‖ ≥ ‖ρ‖²/4`，分子 `≤ 2(‖s‖+1)`；
  常数部 `≤ 2·‖ρ‖⁻²`（`LiZeroSumConvergence` 中已建立的估计）。

- **主定理**（`summable_xiPairedMittagLefflerTerm`）：对每个固定的
  `s : ℂ`，配对 Mittag-Leffler 项级数在上半平面非平凡零点上
  （无条件）收敛。按 `B := max 2 (2‖s‖)` 拆高低：低点落入固定有限集
  `nontrivialZerosFinset B` 的原像（有限支撑，
  `summable_of_ne_finset_zero`）；高点由范数界被
  `(8(‖s‖+1)+2)·‖ρ‖⁻²` 控制，后者可和即
  `summable_norm_inv_sq_upperZeros`（`Summable.of_norm_bounded`）。
  （`s = ρ` 时 `1/(s-ρ) = 1/0 = 0` 按 Lean 约定，可和性不受影响。）

- **商常数识别**（`xiPairedMittagLefflerTerm_zero_left`、
  `tsum_xiPairedMittagLefflerTerm_zero_left`、
  `xi_partial_fraction_const_eq_logDeriv_zero`、
  `xi_partial_fraction_const_unique`）：`s = 0` 处每个配对项恒为零
  （`1/(0-ρ) + 1/ρ = 0`），级数恒为零；而 `ξ(0) = 1/2 ≠ 0`，
  故若展开式以常数 `B` 成立，则 `B = ξ'(0)/ξ(0)`，且该常数唯一。

## 剩余缺口的精确形态

`li_zero_sum_representation_target` 与
`xi_partial_fraction_expansion_target` 在本切片之后仍需：

1. **可去奇点论证**：`ξ'/ξ - B - Σ_ρ [1/(s-ρ) + 1/ρ]` 为整函数
   （每个 `s = ρ` 处两边留数同为 1，差可去）；
2. **ξ 的增长阶 ≤ 1**：`|ξ(s)| ≲ exp(C·|s|·log|s|)`（Gamma 因子界 +
   Phragmén–Lindelöf；仓库已有 `ZeroFreeRegion.PhragmenLindelofZeta`
   风格工具可复用），从而上述整函数为常数；
3. ~~商常数 B 的识别~~：**已条件解决**（模展开式本身），
   `B = ξ'(0)/ξ(0)`（`xi_partial_fraction_const_eq_logDeriv_zero`）；
4. **配对约定**：本文件按 `ρ ↔ conj ρ` 配对；经典写法按
   `ρ ↔ 1 - ρ` 配对，两者经函数方程等价，需在拼接时说明；
5. **重数约定**：`UpperHalfPlaneNontrivialZero` 是「不同零点」的
   子类型；Hadamard 级数按解析重数计次。零点重数 > 1 的场合需在
   拼接表示定理时处理（注意 ζ 零点是否均为单零点本身未知，
   因此表示定理的重数版本应表述为对重数求和）。

## 证明纪律

无 `sorry`/`admit`/新公理；公理审计见 `Test/XiFunctionAxiomAudit.lean`。
-/

import RiemannExplorer.LiZeroSumConvergence

open Complex ComplexConjugate
open scoped BigOperators

namespace RiemannExplorer

/-- ξ'/ξ 部分分式展开（按 `ρ ↔ conj ρ` 配对）的配对 Mittag-Leffler 项：
`[1/(s-ρ) + 1/ρ] + [1/(s-conjρ) + 1/conjρ]`。 -/
noncomputable def xiPairedMittagLefflerTerm (s ρ : ℂ) : ℂ :=
  (1 / (s - ρ) + 1 / ρ) + (1 / (s - conj ρ) + 1 / conj ρ)

/-- 配对 Mittag-Leffler 项的代数分解：主部 `2(s - ↑ρ.re)/((s-ρ)(s-conjρ))`
加常数部 `↑(2·ρ.re/normSq ρ)`。（常数部恒等式对 `ρ = 0` 也平凡成立，
故只需 `s - ρ ≠ 0`、`s - conj ρ ≠ 0`。） -/
theorem xiPairedMittagLefflerTerm_eq {s ρ : ℂ} (hsρ : s - ρ ≠ 0)
    (hsρc : s - conj ρ ≠ 0) :
    xiPairedMittagLefflerTerm s ρ =
      2 * (s - ((ρ.re : ℝ) : ℂ)) / ((s - ρ) * (s - conj ρ)) +
        ((2 * ρ.re / Complex.normSq ρ : ℝ) : ℂ) := by
  have hA : (1 : ℂ) / (s - ρ) + 1 / (s - conj ρ) =
      2 * (s - ((ρ.re : ℝ) : ℂ)) / ((s - ρ) * (s - conj ρ)) := by
    have h2 : (s - ρ) + (s - conj ρ) = 2 * (s - ((ρ.re : ℝ) : ℂ)) := by
      have h := Complex.add_conj ρ
      rw [show ((ρ.re : ℝ) : ℂ) = (ρ + conj ρ) / 2 by rw [h]; push_cast; ring]
      ring
    rw [div_add_div _ _ hsρ hsρc, one_mul, mul_one, add_comm, h2]
  have hB : (1 : ℂ) / ρ + 1 / conj ρ = ((2 * ρ.re / Complex.normSq ρ : ℝ) : ℂ) := by
    rw [one_div, one_div, ← Complex.conj_inv, Complex.add_conj, Complex.inv_re]
    congr 1
    ring
  unfold xiPairedMittagLefflerTerm
  rw [show ((1 : ℂ) / (s - ρ) + 1 / ρ) + (1 / (s - conj ρ) + 1 / conj ρ) =
      (1 / (s - ρ) + 1 / (s - conj ρ)) + (1 / ρ + 1 / conj ρ) by ring, hA, hB]

/-- 配对 Mittag-Leffler 项的范数界：对 `‖ρ‖ ≥ 2`、`2‖s‖ ≤ ‖ρ‖`、
`|ρ.re| ≤ 1`（非平凡零点自动满足最后一项，因 `0 < ρ.re < 1`），

```text
‖xiPairedMittagLefflerTerm s ρ‖ ≤ (8·(‖s‖+1) + 2)·‖ρ‖⁻²。
```

证明：`‖s - ρ‖ ≥ ‖ρ‖ - ‖s‖ ≥ ‖ρ‖/2`（`norm_sub_norm_le` +
`norm_sub_rev`），`conj ρ` 同理，故分母 `≥ ‖ρ‖²/4`；分子
`‖2(s - ↑ρ.re)‖ ≤ 2(‖s‖ + 1)`（`norm_sub_le` 与 `|ρ.re| ≤ 1`），
于是主部 `≤ 8(‖s‖+1)·‖ρ‖⁻²`；常数部估计与 `norm_liPairedTerm_le`
中的线性项完全相同，`≤ 2·‖ρ‖⁻²`。 -/
theorem norm_xiPairedMittagLefflerTerm_le {s ρ : ℂ} (hρ2 : 2 ≤ ‖ρ‖)
    (hρs : 2 * ‖s‖ ≤ ‖ρ‖) (hre : |ρ.re| ≤ 1) :
    ‖xiPairedMittagLefflerTerm s ρ‖ ≤ (8 * (‖s‖ + 1) + 2) * ‖ρ‖⁻¹ ^ 2 := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hρ2
    norm_num at hρ2
  have hρpos : (0 : ℝ) < ‖ρ‖ := lt_of_lt_of_le (by norm_num) hρ2
  have hsle : ‖s‖ ≤ ‖ρ‖ / 2 := by linarith
  have hsρ : s - ρ ≠ 0 := by
    intro h
    have hs : s = ρ := sub_eq_zero.mp h
    rw [hs] at hsle
    linarith
  have hsρc : s - conj ρ ≠ 0 := by
    intro h
    have hs : s = conj ρ := sub_eq_zero.mp h
    have : ‖s‖ = ‖ρ‖ := by rw [hs, Complex.norm_conj]
    linarith
  -- 分母两项的下界：‖s - ρ‖, ‖s - conj ρ‖ ≥ ‖ρ‖/2
  have hsub1 : ‖ρ‖ / 2 ≤ ‖s - ρ‖ := by
    have h := norm_sub_norm_le ρ s
    rw [norm_sub_rev] at h
    linarith
  have hsub2 : ‖ρ‖ / 2 ≤ ‖s - conj ρ‖ := by
    have h := norm_sub_norm_le (conj ρ) s
    rw [Complex.norm_conj, norm_sub_rev] at h
    linarith
  have hsubpos1 : (0 : ℝ) < ‖s - ρ‖ := lt_of_lt_of_le (by linarith) hsub1
  have hsubpos2 : (0 : ℝ) < ‖s - conj ρ‖ := lt_of_lt_of_le (by linarith) hsub2
  -- 分子界与分母界
  have hre' : ‖((ρ.re : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_real, Real.norm_eq_abs]
    exact hre
  have hnum : ‖2 * (s - ((ρ.re : ℝ) : ℂ))‖ ≤ 2 * (‖s‖ + 1) := by
    rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hsub := (norm_sub_le s ((ρ.re : ℝ) : ℂ)).trans (add_le_add le_rfl hre')
    exact mul_le_mul_of_nonneg_left hsub (by norm_num)
  have hden : ‖ρ‖ ^ 2 / 4 ≤ ‖(s - ρ) * (s - conj ρ)‖ := by
    rw [norm_mul, show ‖ρ‖ ^ 2 / 4 = (‖ρ‖ / 2) * (‖ρ‖ / 2) by ring]
    exact mul_le_mul hsub1 hsub2 (by linarith) (norm_nonneg _)
  have hρ2pos : (0 : ℝ) < ‖ρ‖ ^ 2 := sq_pos_of_pos hρpos
  have hDquarter_pos : (0 : ℝ) < ‖ρ‖ ^ 2 / 4 := by linarith
  have hρ2ne : ‖ρ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hρpos)
  -- 主部：≤ 8(‖s‖+1)·‖ρ‖⁻²
  have eA : 2 * (‖s‖ + 1) / (‖ρ‖ ^ 2 / 4) = 8 * (‖s‖ + 1) * ‖ρ‖⁻¹ ^ 2 := by
    rw [inv_pow, div_eq_iff hDquarter_pos.ne', mul_assoc, ← mul_div_assoc,
      inv_mul_cancel₀ hρ2ne]
    ring
  have hApart : ‖2 * (s - ((ρ.re : ℝ) : ℂ)) / ((s - ρ) * (s - conj ρ))‖ ≤
      8 * (‖s‖ + 1) * ‖ρ‖⁻¹ ^ 2 := by
    rw [norm_div]
    have hDpos : (0 : ℝ) < ‖(s - ρ) * (s - conj ρ)‖ := by
      rw [norm_mul]
      exact mul_pos hsubpos1 hsubpos2
    calc ‖2 * (s - ((ρ.re : ℝ) : ℂ))‖ / ‖(s - ρ) * (s - conj ρ)‖
        ≤ 2 * (‖s‖ + 1) / ‖(s - ρ) * (s - conj ρ)‖ :=
          div_le_div_of_nonneg_right hnum hDpos.le
      _ ≤ 2 * (‖s‖ + 1) / (‖ρ‖ ^ 2 / 4) :=
          div_le_div_of_nonneg_left (by positivity) hDquarter_pos hden
      _ = 8 * (‖s‖ + 1) * ‖ρ‖⁻¹ ^ 2 := eA
  -- 常数部：≤ 2·‖ρ‖⁻²（与 norm_liPairedTerm_le 的线性项估计相同）
  have hBnorm : ‖((2 * ρ.re / Complex.normSq ρ : ℝ) : ℂ)‖ ≤ 2 * ‖ρ‖⁻¹ ^ 2 := by
    rw [norm_real, Real.norm_eq_abs]
    have hnormSq : (0 : ℝ) < Complex.normSq ρ := Complex.normSq_pos.mpr hρ0
    have habs : |2 * ρ.re / Complex.normSq ρ| = 2 * |ρ.re| / Complex.normSq ρ := by
      rw [abs_div, abs_of_pos hnormSq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [habs]
    have h1 : 2 * |ρ.re| ≤ 2 * 1 := mul_le_mul_of_nonneg_left hre (by norm_num)
    have h2 : 2 * |ρ.re| / Complex.normSq ρ ≤ 2 * 1 / Complex.normSq ρ :=
      div_le_div_of_nonneg_right h1 hnormSq.le
    have h3 : 2 * 1 / Complex.normSq ρ = 2 * ‖ρ‖⁻¹ ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, inv_pow]
      ring
    exact h2.trans_eq h3
  calc ‖xiPairedMittagLefflerTerm s ρ‖
      = ‖2 * (s - ((ρ.re : ℝ) : ℂ)) / ((s - ρ) * (s - conj ρ)) +
          ((2 * ρ.re / Complex.normSq ρ : ℝ) : ℂ)‖ := by
        rw [xiPairedMittagLefflerTerm_eq hsρ hsρc]
    _ ≤ ‖2 * (s - ((ρ.re : ℝ) : ℂ)) / ((s - ρ) * (s - conj ρ))‖ +
          ‖((2 * ρ.re / Complex.normSq ρ : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ 8 * (‖s‖ + 1) * ‖ρ‖⁻¹ ^ 2 + 2 * ‖ρ‖⁻¹ ^ 2 := add_le_add hApart hBnorm
    _ = (8 * (‖s‖ + 1) + 2) * ‖ρ‖⁻¹ ^ 2 := by ring

/-- **主定理**：对每个固定的 `s : ℂ`，ξ'/ξ 部分分式的配对
Mittag-Leffler 项级数在上半平面非平凡零点上（无条件）收敛。

证明：按 `B := max 2 (2‖s‖)` 把被加项拆成两个函数。低点函数在
`nontrivialZerosFinset B` 的原像之外恒为零（有限支撑，
`summable_of_ne_finset_zero`；成员判定只需 `IsNontrivialZero` 与
`|ρ.im| ≤ B`）；高点函数由 `norm_xiPairedMittagLefflerTerm_le`
（`|ρ.re| ≤ 1` 来自 `0 < ρ.re < 1`）被 `(8(‖s‖+1)+2)·‖ρ‖⁻²` 控制，
后者可和由 `summable_norm_inv_sq_upperZeros` 给出
（`Summable.of_norm_bounded`）。 -/
theorem summable_xiPairedMittagLefflerTerm (s : ℂ) :
    Summable fun ρ : UpperHalfPlaneNontrivialZero ↦
      xiPairedMittagLefflerTerm s (ρ : ℂ) := by
  classical
  set B := max 2 (2 * ‖s‖) with hB
  have hsplit : (fun ρ : UpperHalfPlaneNontrivialZero ↦
        xiPairedMittagLefflerTerm s (ρ : ℂ)) =
      (fun ρ : UpperHalfPlaneNontrivialZero ↦
          if ‖(ρ : ℂ)‖ < B then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) +
        (fun ρ : UpperHalfPlaneNontrivialZero ↦
          if B ≤ ‖(ρ : ℂ)‖ then xiPairedMittagLefflerTerm s (ρ : ℂ) else 0) := by
    funext ρ
    simp only [Pi.add_apply]
    by_cases h : ‖(ρ : ℂ)‖ < B
    · rw [if_pos h, if_neg (by linarith), add_zero]
    · rw [if_neg h, if_pos (le_of_not_gt h), zero_add]
  rw [hsplit]
  refine Summable.add ?_ ?_
  · apply summable_of_ne_finset_zero
      (s := (PrimeNumberTheorem.nontrivialZerosFinset B).preimage
        (fun ρ : UpperHalfPlaneNontrivialZero ↦ (ρ : ℂ)) Subtype.coe_injective.injOn)
    intro ρ hρ
    rw [Finset.mem_preimage] at hρ
    by_cases hlt : ‖(ρ : ℂ)‖ < B
    · exfalso
      apply hρ
      rw [PrimeNumberTheorem.mem_nontrivialZerosFinset]
      exact ⟨ρ.2.1, (Complex.abs_im_le_norm _).trans hlt.le⟩
    · exact if_neg hlt
  · refine Summable.of_norm_bounded
      (g := fun ρ : UpperHalfPlaneNontrivialZero ↦
        (8 * (‖s‖ + 1) + 2) * ‖(ρ : ℂ)‖⁻¹ ^ 2)
      (summable_norm_inv_sq_upperZeros.mul_left _) fun ρ => ?_
    by_cases h : B ≤ ‖(ρ : ℂ)‖
    · rw [if_pos h]
      have hρ2 : 2 ≤ ‖(ρ : ℂ)‖ := le_trans (le_max_left _ _) h
      have hρs : 2 * ‖s‖ ≤ ‖(ρ : ℂ)‖ := le_trans (le_max_right _ _) h
      have hre : |(ρ : ℂ).re| ≤ 1 := by
        have h1 := ρ.2.1.2.1
        have h2 := ρ.2.1.2.2
        rw [abs_le]
        constructor <;> linarith
      exact norm_xiPairedMittagLefflerTerm_le hρ2 hρs hre
    · rw [if_neg h, norm_zero]
      positivity

/-! ## 商常数识别（条件切片） -/

/-- 配对 Mittag-Leffler 项在 `s = 0` 处恒为零（无条件）：
`1/(0-ρ) + 1/ρ = -(1/ρ) + 1/ρ = 0`，共轭部分同理。
（Lean 约定下 `ρ = 0` 时也成立：`1/(0-0) + 1/0 = 0 + 0`。） -/
theorem xiPairedMittagLefflerTerm_zero_left (ρ : ℂ) :
    xiPairedMittagLefflerTerm 0 ρ = 0 := by
  unfold xiPairedMittagLefflerTerm
  simp only [zero_sub, div_neg]
  ring

/-- `s = 0` 处配对 Mittag-Leffler 级数恒为零（无条件）。 -/
theorem tsum_xiPairedMittagLefflerTerm_zero_left :
    (∑' ρ : UpperHalfPlaneNontrivialZero,
      xiPairedMittagLefflerTerm 0 (ρ : ℂ)) = 0 := by
  rw [show (fun ρ : UpperHalfPlaneNontrivialZero ↦
        xiPairedMittagLefflerTerm 0 (ρ : ℂ)) = fun _ => 0
      from funext fun ρ => xiPairedMittagLefflerTerm_zero_left _]
  exact tsum_zero

/-- 目标：ξ'/ξ 的部分分式展开（Hadamard 因子分解级）。

数学形式：存在常数 `B`（必等于 `ξ'(0)/ξ(0)`，由
`xi_partial_fraction_const_eq_logDeriv_zero` 条件识别），对所有满足
`ξ(s) ≠ 0` 的 `s`，

```text
ξ'(s)/ξ(s) = B + Σ_ρ ([1/(s-ρ) + 1/ρ] + [1/(s-conjρ) + 1/conjρ])
```

按 `ρ ↔ conj ρ` 配对（经典写法按 `ρ ↔ 1 - ρ` 配对，经函数方程
`ξ(s) = ξ(1-s)` 与共轭对称等价，拼接时需说明）；右端级数的收敛性
已由 `summable_xiPairedMittagLefflerTerm` 解决。

剩余缺口（见本文件头）：(i) 可去奇点论证——`ξ'/ξ − B − Σ` 为整函数；
(ii) ξ 增长阶 `≤ 1`（Gamma 界 + Phragmén–Lindelöf）迫使该整函数为常数；
(iii) 按不同零点计数、不含解析重数的约定对齐。 -/
def xi_partial_fraction_expansion_target : Prop :=
  ∃ B : ℂ, ∀ s : ℂ, xiFunction s ≠ 0 →
    deriv xiFunction s / xiFunction s =
      B + ∑' ρ : UpperHalfPlaneNontrivialZero, xiPairedMittagLefflerTerm s (ρ : ℂ)

/-- **商常数识别**：若部分分式展开以常数 `B` 成立，则
`B = ξ'(0)/ξ(0)`。
证明：`ξ(0) = 1/2 ≠ 0`（`xiFunction_zero`），故展开式在 `s = 0`
适用；而 `s = 0` 处每个配对项为零（`xiPairedMittagLefflerTerm_zero_left`），
级数恒为零（`tsum_xiPairedMittagLefflerTerm_zero_left`）。 -/
theorem xi_partial_fraction_const_eq_logDeriv_zero (B : ℂ)
    (hexp : ∀ s : ℂ, xiFunction s ≠ 0 → deriv xiFunction s / xiFunction s =
      B + ∑' ρ : UpperHalfPlaneNontrivialZero, xiPairedMittagLefflerTerm s (ρ : ℂ)) :
    B = deriv xiFunction 0 / xiFunction 0 := by
  have h0 : xiFunction 0 ≠ 0 := by
    rw [xiFunction_zero]
    norm_num
  have h := hexp 0 h0
  rw [tsum_xiPairedMittagLefflerTerm_zero_left, add_zero] at h
  exact h.symm

/-- 商常数唯一性：两个使部分分式展开成立的常数必相等
（都等于 `ξ'(0)/ξ(0)`）。 -/
theorem xi_partial_fraction_const_unique {B₁ B₂ : ℂ}
    (h₁ : ∀ s : ℂ, xiFunction s ≠ 0 → deriv xiFunction s / xiFunction s =
      B₁ + ∑' ρ : UpperHalfPlaneNontrivialZero, xiPairedMittagLefflerTerm s (ρ : ℂ))
    (h₂ : ∀ s : ℂ, xiFunction s ≠ 0 → deriv xiFunction s / xiFunction s =
      B₂ + ∑' ρ : UpperHalfPlaneNontrivialZero, xiPairedMittagLefflerTerm s (ρ : ℂ)) :
    B₁ = B₂ :=
  (xi_partial_fraction_const_eq_logDeriv_zero B₁ h₁).trans
    (xi_partial_fraction_const_eq_logDeriv_zero B₂ h₂).symm

end RiemannExplorer
