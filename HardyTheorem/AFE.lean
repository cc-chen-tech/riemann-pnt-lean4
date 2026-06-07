/-
# Hardy D 链 Phase 2 — Unwrapped theta + 校正 AFE 目标

本文件集中 Phase 2 的两个目标:

1. `unwrappedRiemannSiegelTheta`:  Riemann-Siegel theta 函数的 unwrapped(连续)
   版本。在 Lean / Mathlib 4.29.1 中,Riemann-Siegel theta 没有"原生的"连续
   全局版本,故本文件采取以下策略:把 `unwrappedRiemannSiegelTheta` 定义为
   `thetaPhase` 本身(principal value 已经是实数,虽然有 2π 周期性带来的
   间断点;在更进一步的 Phase 3 / Phase 4 中可以替换为真正的连续 lift,例如
   用 `Complex.log` / `Real.log` 在实轴上取连续分支)。重要的是
   `exp(I · unwrapped t) = exp(I · thetaPhase t)` 这一等式,直接来自定义。
   当后续把 `unwrappedRiemannSiegelTheta` 替换为真正的连续 lift 时,
   `thetaPhase_unwrapped_relation` 仍需保持(只是 `rfl` 会被替换为非平凡
   的 `Complex.exp_eq_exp_iff_exists_int` 证明)。

2. `zeta_critical_afe_target`:  AFE(approximate functional equation)目标。
   与 `HardyTheorem.Details.approximate_functional_equation_target` 等价的
   Phase 2 入口,放在 `HardyTheorem.AFE` 命名空间下;形式上把相位项
   `exp(I · thetaPhase t)` 替换为 `exp(I · unwrappedRiemannSiegelTheta t)`,
   二者数学上等价(由 `thetaPhase_unwrapped_relation` 给出)。这样
   下游可以按 AFE 中心 `exp(-2I · θ(t))` 的"未包装"视角统一处理,
   而不必关心 principal branch 的 2π 跳跃。

## 与既有 `HardyTheorem.Details.approximate_functional_equation_target` 的关系

- 内容等价:本文件 `zeta_critical_afe_target` 与
  `HardyTheorem.Details.approximate_functional_equation_target` 表达的是
  同一个 AFE 命题(`∃ C > 0, ∀ t > 1, ∃ R, ‖R‖ ≤ C * t^(-1/4)`)。
- 形式区别:本目标用 `unwrappedRiemannSiegelTheta` 替换了 `thetaPhase`,
  下游可以按"未包装的相位"统一处理。
- 短期不需要证明(本任务为"目标声明"占位),故本文件不写证明,
  只声明 `def ... : Prop`。
-/

import HardyTheorem

open Complex Asymptotics Filter

namespace HardyTheorem.AFE

/-! ## 1. Unwrapped Riemann-Siegel theta -/

/-- Riemann-Siegel theta 函数的 unwrapped 版本。

技术说明:在 Lean / Mathlib 4.29.1 下,Riemann-Siegel theta 没有"原生的"
连续全局实值版本。`thetaPhase`(在 `HardyTheorem.lean`)给出 principal branch
的实数值,本定义在 `thetaPhase` 基础上做以下**形式化**:
- 当前实现把 `unwrappedRiemannSiegelTheta` 直接定义为 `thetaPhase` 本身。
  这样 `thetaPhase_unwrapped_relation` 是 `rfl`,形式上正确。
- 后续 Phase 3 / Phase 4 可以把本定义替换为真正的连续 lift(例如用
  `Real.log` 在实轴上的连续分支,或 `Complex.log` 在 `Gamma(1/4 + I t / 2)`
  上的实轴连通分支),此时 `thetaPhase_unwrapped_relation` 需要用
  `Complex.exp_eq_exp_iff_exists_int` 证明
  `unwrappedRiemannSiegelTheta t - thetaPhase t ∈ (2 * Real.pi) * ℤ`。

重要:不论本定义取哪个具体实现,`exp(I · unwrapped t) = exp(I · thetaPhase t)`
总是成立,这是 AFE 中相位项 `exp(-2I · θ t)` 不依赖 principal branch 选择的
关键。-/
noncomputable def unwrappedRiemannSiegelTheta : ℝ → ℝ := thetaPhase

/-- `unwrappedRiemannSiegelTheta` 与 `thetaPhase` 在 `exp(I · ·)` 意义下相同。

即:存在整数 `k(t)`,使 `unwrappedRiemannSiegelTheta t = thetaPhase t + 2π · k(t)`,
从而 `exp(I · unwrappedRiemannSiegelTheta t) = exp(I · thetaPhase t)`。

本引理在 AFE 中保证相位项 `exp(I · thetaPhase t)` 与
`exp(I · unwrappedRiemannSiegelTheta t)` 数学等价。-/
lemma thetaPhase_unwrapped_relation (t : ℝ) :
    Complex.exp (I * (unwrappedRiemannSiegelTheta t : ℂ)) =
      Complex.exp (I * (thetaPhase t : ℂ)) := rfl

/-! ## 2. 校正的 AFE 目标 -/

/-- Approximate functional equation 目标(Phase 2 校正版)。

形式:`∃ R > 0, ∀ t > 1, ∃ R' : ℂ, ζ(1/2 + I·t) = finite_sum + R' ∧ ‖R'‖ ≤ R · t^(-1/4)`,
其中 finite_sum 包含 `θ(t)` 一侧的相位项(此处用 `unwrappedRiemannSiegelTheta`
替换 `thetaPhase`,数学等价)。

本目标是 `HardyTheorem.Details.approximate_functional_equation_target`
的 Phase 2 入口,语义一致,仅相位项使用 unwrapped 版本。

下游可以按 AFE 中心 `exp(-2I · θ_unwrapped t)` 的"未包装"视角统一处理
hardyZ 矩估计的输入,不需关心 principal branch 的 2π 跳跃。-/
def zeta_critical_afe_target : Prop :=
    ∃ R > (0 : ℝ), ∀ t : ℝ, t > 1 → ∃ R' : ℂ,
      (riemannZeta ((1 / 2 : ℂ) + I * t) =
        (∑ n ∈ Finset.range (Nat.floor (Real.sqrt (t / (2 * Real.pi)))),
            1 / ((n + 1 : ℂ) ^ ((1 / 2 : ℂ) + I * t))
         + Complex.exp (I * (unwrappedRiemannSiegelTheta t : ℂ)) *
            ∑ n ∈ Finset.range (Nat.floor (Real.sqrt (t / (2 * Real.pi)))),
              1 / ((n + 1 : ℂ) ^ ((1 / 2 : ℂ) - I * t))
         + R')) ∧
      ‖R'‖ ≤ R * (t : ℝ) ^ (-1 / 4 : ℝ)

/-- 包装 `zeta_critical_afe_target` 的小构造子:从 `(R, hR_pos, hrem)` 构造命题。-/
lemma zeta_critical_afe_target_of
    (R : ℝ) (hR : 0 < R)
    (hrem : ∀ t : ℝ, t > 1 → ∃ R' : ℂ,
      (riemannZeta ((1 / 2 : ℂ) + I * t) =
        (∑ n ∈ Finset.range (Nat.floor (Real.sqrt (t / (2 * Real.pi)))),
            1 / ((n + 1 : ℂ) ^ ((1 / 2 : ℂ) + I * t))
         + Complex.exp (I * (unwrappedRiemannSiegelTheta t : ℂ)) *
            ∑ n ∈ Finset.range (Nat.floor (Real.sqrt (t / (2 * Real.pi)))),
              1 / ((n + 1 : ℂ) ^ ((1 / 2 : ℂ) - I * t))
         + R')) ∧
      ‖R'‖ ≤ R * (t : ℝ) ^ (-1 / 4 : ℝ)) :
    zeta_critical_afe_target :=
  ⟨R, hR, hrem⟩

end HardyTheorem.AFE
