/-
# Li 系数的实值性（无条件定理）

本文件证明 Li 准则路线的关键无条件事实：

```text
(liCoefficient n).im = 0   对所有 n : ℕ 成立。
```

这恰好把 `LiCriterionHolds` 中的「虚部为零」一半**无条件**消去：
Li 准则因此归约为纯实数不等式 `0 < (liCoefficient n).re`。

## 证明路线

ξ 函数满足 Schwarz 对称 `ξ(conj s) = conj (ξ s)`
（`RiemannExplorer.xiFunction_conj`）。取开集

```text
U := ξ ⁻¹' {w : ℂ | 0 < w.re}
```

它是开的（ξ 连续）、共轭稳定的、且包含实点 `s = 1`（因为 ξ(1) = 1/2）。
在 `U` 上 ξ 实部为正，故 `Complex.log ∘ ξ` 良定义且可微（避开分支切割），
并且 `log (conj w) = conj (log w)`（`Complex.log_conj`，由 `arg w ≠ π`）。

于是 `F(s) = s^(n-1) · log ξ(s)` 在 `U` 上可微且 Schwarz 对称，
由 `RiemannExplorer/SchwarzSymmetric.lean` 的归纳引理，
其在实点 `1` 处的任意阶迭代导数都是实数，故 `λ_n ∈ ℝ`。

这是 Li 准则「系数为实数」的经典事实的形式化；
文献中它通常作为 Hadamard 乘积的推论出现，这里直接从 Schwarz 对称性推出，
不依赖任何未证的乘积展开。
-/

import RiemannExplorer.LiCriterion
import RiemannExplorer.SchwarzSymmetric

open Complex ComplexConjugate Topology

namespace RiemannExplorer

/-- ξ 的实部为正的开区域：`U := ξ ⁻¹' {w | 0 < w.re}`。 -/
def xiPosReSet : Set ℂ := xiFunction ⁻¹' {w : ℂ | 0 < w.re}

/-- `U` 是开集（ξ 连续、半平面开）。 -/
theorem isOpen_xiPosReSet : IsOpen xiPosReSet :=
  (isOpen_lt continuous_const continuous_re).preimage
    differentiable_xiFunction.continuous

/-- `U` 共轭稳定：由 ξ 的 Schwarz 对称性。 -/
theorem conj_mem_xiPosReSet {s : ℂ} (hs : s ∈ xiPosReSet) :
    conj s ∈ xiPosReSet := by
  show 0 < (xiFunction (conj s)).re
  rw [xiFunction_conj, Complex.conj_re]
  exact hs

/-- 实点 `1 ∈ U`：因为 `ξ(1) = 1/2`。 -/
theorem one_mem_xiPosReSet : (1 : ℂ) ∈ xiPosReSet := by
  show 0 < (xiFunction 1).re
  rw [xiFunction_one]
  norm_num

/-- 在 `U` 上 `F(s) = s^(n-1) · log ξ(s)` 可微：
ξ 实部为正 ⇒ ξ(s) ∈ slitPlane ⇒ `log` 在该点可微。 -/
theorem differentiableOn_pow_mul_log_xi (n : ℕ) :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ s ^ (n - 1) * Complex.log (xiFunction s)) xiPosReSet := by
  intro s hs
  have hsp : 0 < (xiFunction s).re := hs
  have hlog : DifferentiableAt ℂ Complex.log (xiFunction s) :=
    Complex.differentiableAt_log (Or.inl hsp)
  exact ((differentiableAt_pow (n - 1)).mul
    (hlog.comp s (differentiable_xiFunction s))).differentiableWithinAt

/-- 在 `U` 上 `F` 满足 Schwarz 对称：
由 `xiFunction_conj` 与 `Complex.log_conj`（`arg ≠ π` 由实部为正给出）。 -/
theorem schwarzSymmetricOn_pow_mul_log_xi (n : ℕ) :
    ∀ s ∈ xiPosReSet,
      (fun s : ℂ ↦ s ^ (n - 1) * Complex.log (xiFunction s)) (conj s) =
        conj ((fun s : ℂ ↦ s ^ (n - 1) * Complex.log (xiFunction s)) s) := by
  intro s hs
  have hsp : 0 < (xiFunction s).re := hs
  have harg : (xiFunction s).arg ≠ Real.pi := by
    intro h
    exact absurd (Complex.arg_eq_pi_iff.mp h).1 (not_lt.mpr hsp.le)
  show conj s ^ (n - 1) * Complex.log (xiFunction (conj s)) =
    conj (s ^ (n - 1) * Complex.log (xiFunction s))
  rw [xiFunction_conj, Complex.log_conj _ harg, map_mul, map_pow]

/-- **主定理（无条件）**：每个 Li 系数都是实数。

证明：`F(s) = s^(n-1) · log ξ(s)` 在 `1` 的开邻域 `xiPosReSet` 上可微且
Schwarz 对称，故其任意阶迭代导数在实点 `1` 处取实值；
`λ_n = (1/(n-1)!) · (第 n 阶迭代导数在 1 处的值)` 因此为实数。 -/
theorem liCoefficient_is_real (n : ℕ) :
    ∃ r : ℝ, liCoefficient n = (r : ℂ) := by
  obtain ⟨r, hr⟩ := iteratedDeriv_schwarz_real
    isOpen_xiPosReSet (fun s hs ↦ conj_mem_xiPosReSet hs)
    (differentiableOn_pow_mul_log_xi n) (schwarzSymmetricOn_pow_mul_log_xi n)
    one_mem_xiPosReSet n
  rw [Complex.ofReal_one] at hr
  exact ⟨(1 / (Nat.factorial (n - 1) : ℝ)) * r, by
    rw [liCoefficient, hr]
    push_cast
    ring⟩

/-- **Li 准则的虚部条件无条件成立**：
`(liCoefficient n).im = 0` 对所有 `n` 成立。
`LiCriterionHolds` 因此等价于纯实数不等式
`∀ n ≥ 1, 0 < (liCoefficient n).re`。 -/
theorem liCoefficient_im (n : ℕ) : (liCoefficient n).im = 0 := by
  obtain ⟨r, hr⟩ := liCoefficient_is_real n
  rw [hr]
  exact Complex.ofReal_im r

/-- 归约形式：Li 准则 ⇔ 所有系数的实部为正（虚部条件已无条件消去）。 -/
theorem liCriterionHolds_iff_re_pos :
    LiCriterionHolds ↔ ∀ n : ℕ, 1 ≤ n → 0 < (liCoefficient n).re := by
  constructor
  · intro h n hn
    exact (h n hn).2
  · intro h n hn
    exact ⟨liCoefficient_im n, h n hn⟩

end RiemannExplorer
