/-
# ξ 函数基础设施 (A 线第一阶段)

本文件按 `docs/research/xi-definition-audit.md` 的建议建立规范 (canonical) 的
`xiFunction` API，回答审计中的悬而未决问题：

1.  **`RiemannExplorer.lean` 中 `completedZeta` 的仿射修正项是否为极点消去项？**
    是。由 Mathlib 的
    `completedRiemannZeta_eq : completedRiemannZeta s = completedRiemannZeta₀ s - 1/s - 1/(1-s)`
    可得 `(1/2)·s·(s-1)·completedRiemannZeta s`
    `= (1/2)·s·(s-1)·completedRiemannZeta₀ s - (1/2)·(s-1) + (1/2)·s`。
    本文件以此**全局整函数**表达式为 `xiFunction` 的定义，并证明它与
    旧名 `RiemannHypothesis.completedZeta` 定义相等 (`xiFunction_eq_completedZeta`)。

2.  **规范名**：`RiemannExplorer.xiFunction`，与 Mathlib 的
    `completedRiemannZeta`（亚纯）和 `completedRiemannZeta₀`（整）的关系
    分别由 `xiFunction_eq_half_mul_completed`（远离 0,1）与定义本身（全局）给出。

3.  **本文件已证的定理**（均无 sorry，公理审计见
    `Test/XiFunctionAxiomAudit.lean`）：
    - `xiFunction_one_sub`：函数方程 `ξ(s) = ξ(1-s)`；
    - `xiFunction_zero` / `xiFunction_one`：`ξ(0) = ξ(1) = 1/2`；
    - `differentiable_xiFunction`：`ξ` 为整函数（全复平面可微）；
    - `xiFunction_eq_half_mul_completed`：桥接 Mathlib 亚纯 completed zeta；
    - `xiFunction_eq_classical` / `xiFunction_eq_classical_of_one_lt_re`：
      经典形式 `ξ(s) = (1/2)·s·(s-1)·Gammaℝ(s)·ζ(s)`；
    - `xiFunction_eq_zero_iff` / `xiFunction_eq_zero_iff_isNontrivialZero`：
      临界带内 `ξ(s) = 0 ↔ ζ(s) = 0`；
    - `riemannHypothesis_iff_xi_zeros_on_critical_line`：
      RH 等价于「`ξ` 在临界带内的零点都在临界线上」；
    - `xiFunction_conj`：`ξ(conj s) = conj (ξ s)`；
    - `xiFunction_critical_line_real`：临界线上 `ξ(1/2 + it)` 取实值。

4.  **本文件不放** Li 系数、显式公式或 Hardy Z 函数；那些是下游消费者
    （见 `RiemannExplorer/LiCriterion.lean`）。
-/

import RiemannExplorer

open Complex ComplexConjugate

namespace RiemannExplorer

/-! ## 规范定义 -/

/-- Riemann ξ 函数（规范定义，全局整函数形式）。

数学目标形式为
`ξ(s) = (1/2)·s·(s-1)·π^(-s/2)·Γ(s/2)·ζ(s) = (1/2)·s·(s-1)·completedRiemannZeta s`，
后者只在 `s ≠ 0, 1` 处良定义。用 Mathlib 的极点消去关系
`completedRiemannZeta s = completedRiemannZeta₀ s - 1/s - 1/(1-s)`
把极点项显式消去后得到的全局整函数表达式即本定义；
仿射修正项 `-(1/2)·(s-1) + (1/2)·s` 正是 `s = 0, 1` 两处极点的消去项。 -/
noncomputable def xiFunction (s : ℂ) : ℂ :=
  (1 / 2) * s * (s - 1) * completedRiemannZeta₀ s - (1 / 2) * (s - 1) + (1 / 2) * s

/-- 与旧名 `RiemannHypothesis.completedZeta` 的桥接：二者定义相等。
旧名保留作接口兼容，新工作统一使用 `xiFunction`。 -/
theorem xiFunction_eq_completedZeta (s : ℂ) :
    xiFunction s = RiemannHypothesis.completedZeta s := rfl

/-! ## 特殊值与函数方程 -/

/-- `ξ(0) = 1/2`（经典值）。 -/
theorem xiFunction_zero : xiFunction 0 = 1 / 2 := by
  simp [xiFunction]

/-- `ξ(1) = 1/2`（经典值）。 -/
theorem xiFunction_one : xiFunction 1 = 1 / 2 := by
  simp [xiFunction]

/-- 函数方程：`ξ(s) = ξ(1 - s)`。
由 Mathlib 的 `completedRiemannZeta₀_one_sub` 与仿射修正项在
`s ↦ 1 - s` 下的不变性（纯代数）给出。 -/
theorem xiFunction_one_sub (s : ℂ) :
    xiFunction s = xiFunction (1 - s) := by
  simp [xiFunction, completedRiemannZeta₀_one_sub s]
  ring

/-- `ξ` 是整函数：在全复平面可微。
由 `differentiable_completedZeta₀`（Mathlib）与多项式运算封闭性给出。 -/
theorem differentiable_xiFunction : Differentiable ℂ xiFunction := by
  have hΛ : Differentiable ℂ completedRiemannZeta₀ := differentiable_completedZeta₀
  have h1 : Differentiable ℂ fun s : ℂ ↦ (1 / 2 : ℂ) * s :=
    differentiable_id.const_mul _
  have h2 : Differentiable ℂ fun s : ℂ ↦ s - 1 :=
    differentiable_id.sub_const _
  have h3 : Differentiable ℂ fun s : ℂ ↦ (1 / 2 : ℂ) * s * (s - 1) := h1.mul h2
  have h4 : Differentiable ℂ fun s : ℂ ↦
      (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s := h3.mul hΛ
  have h5 : Differentiable ℂ fun s : ℂ ↦ (1 / 2 : ℂ) * (s - 1) := h2.const_mul _
  unfold xiFunction
  exact (h4.sub h5).add h1

/-! ## 与 Mathlib completed zeta 的桥接 -/

/-- 桥接定理（亚纯形式）：`s ≠ 0, 1` 时
`ξ(s) = (1/2)·s·(s-1)·completedRiemannZeta s`。 -/
theorem xiFunction_eq_half_mul_completed {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xiFunction s = (1 / 2) * s * (s - 1) * completedRiemannZeta s := by
  have hs10 : (1 : ℂ) - s ≠ 0 := sub_ne_zero_of_ne (Ne.symm hs1)
  unfold xiFunction
  rw [completedRiemannZeta_eq]
  field_simp [hs0, hs10]
  ring

/-- 经典形式：`s ≠ 0`、`s ≠ 1` 且 `Gammaℝ s ≠ 0` 时
`ξ(s) = (1/2)·s·(s-1)·Gammaℝ(s)·ζ(s)`，
其中 `Gammaℝ s = π^(-s/2)·Γ(s/2)` 为 Mathlib 的实 Gamma 因子。 -/
theorem xiFunction_eq_classical {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hG : Gammaℝ s ≠ 0) :
    xiFunction s = (1 / 2) * s * (s - 1) * Gammaℝ s * riemannZeta s := by
  rw [xiFunction_eq_half_mul_completed hs0 hs1, riemannZeta_def_of_ne_zero hs0]
  field_simp [hG]

/-- 经典形式（收敛区域版）：`1 < s.re` 时
`ξ(s) = (1/2)·s·(s-1)·Gammaℝ(s)·ζ(s)`。 -/
theorem xiFunction_eq_classical_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    xiFunction s = (1 / 2) * s * (s - 1) * Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  exact xiFunction_eq_classical hs0 hs1
    (Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs))

/-! ## 零点对应 -/

/-- 临界带内的零点对应：`0 < s.re < 1` 时 `ξ(s) = 0 ↔ ζ(s) = 0`。
此时 `1/2`、`s`、`s - 1`、`Gammaℝ s` 均非零。 -/
theorem xiFunction_eq_zero_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    xiFunction s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at h0
    simp at h0
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  have hhalf : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have hs10 : s - 1 ≠ 0 := sub_ne_zero_of_ne hs1
  rw [xiFunction_eq_classical hs0 hs1 hG]
  constructor
  · intro h
    simpa [mul_eq_zero, hhalf, hs0, hs10, hG] using h
  · intro h
    simp [h]

/-- 临界带内 `ξ` 的零点恰好是 `ζ` 的非平凡零点。 -/
theorem xiFunction_eq_zero_iff_isNontrivialZero {s : ℂ} (h0 : 0 < s.re)
    (h1 : s.re < 1) :
    xiFunction s = 0 ↔ RiemannHypothesis.IsNontrivialZero s := by
  rw [xiFunction_eq_zero_iff h0 h1]
  exact ⟨fun hz ↦ ⟨hz, h0, h1⟩, fun h ↦ h.1⟩

/-- RH 的 ξ 表述：`RiemannHypothesis.Statement` 等价于
「`ξ` 在临界带内的零点都在临界线 `Re(s) = 1/2` 上」。
这是 Li 准则路线（`RiemannExplorer/LiCriterion.lean`）与
Hadamard 乘积路线共用的零点接口。 -/
theorem riemannHypothesis_iff_xi_zeros_on_critical_line :
    RiemannHypothesis.Statement ↔
      ∀ s : ℂ, xiFunction s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 := by
  constructor
  · intro h s hx h0 h1
    exact h s ⟨(xiFunction_eq_zero_iff h0 h1).mp hx, h0, h1⟩
  · intro h s hs
    exact h s ((xiFunction_eq_zero_iff hs.2.1 hs.2.2).mpr hs.1) hs.2.1 hs.2.2

/-! ## 共轭对称与临界线实值性 -/

/-- 施瓦茨对称：`ξ(conj s) = conj (ξ s)`。
由 `HardyTheorem.completedRiemannZeta₀_conj_eq`（整函数 + 解析延拓）给出。 -/
theorem xiFunction_conj (s : ℂ) :
    xiFunction (conj s) = conj (xiFunction s) := by
  have h2 : conj (2 : ℂ) = 2 := by
    rw [conj_eq_iff_re]
    norm_num
  have hΛ : completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) :=
    HardyTheorem.completedRiemannZeta₀_conj_eq s
  simp only [xiFunction, map_add, map_sub, map_mul, map_div₀, map_one, h2, hΛ]

/-- 临界线实值性：对实数 `t`，`ξ(1/2 + it)` 为实数。
由函数方程 `ξ(s) = ξ(1 - s)`、临界线上 `1 - s = conj s`
以及施瓦茨对称 `ξ(conj s) = conj (ξ s)` 复合给出。 -/
theorem xiFunction_critical_line_real (t : ℝ) :
    ∃ r : ℝ, xiFunction ((1 / 2 : ℂ) + I * t) = (r : ℂ) := by
  let s := (1 / 2 : ℂ) + I * t
  have hfe : xiFunction s = xiFunction (1 - s) := xiFunction_one_sub s
  have h2 : 1 - s = conj s := by
    simp [s, Complex.ext_iff]
    all_goals norm_num
  rw [h2, xiFunction_conj] at hfe
  use (xiFunction s).re
  have hs_eq : xiFunction ((1 / 2 : ℂ) + I * t) = xiFunction s := by simp [s]
  rw [hs_eq]
  have h_re : ↑(xiFunction s).re = xiFunction s := by
    rw [← conj_eq_iff_re]
    exact hfe.symm
  exact h_re.symm

end RiemannExplorer
