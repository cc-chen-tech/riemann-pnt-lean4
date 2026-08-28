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
   临界线函数方程的 dual multiplier 是
   `exp(-2 * I * thetaPhase t)`,不是 `exp(I * thetaPhase t)`。本文件先从
   已证明的 `Gammaℝ` 相位公式推出这个归一化恒等式,再用它声明正确的
   AFE 目标。目标本身仍只是 `def ... : Prop`,没有把 AFE 当成公理或定理。

## 与旧 AFE placeholder 的关系

- 旧 placeholder 使用 `exp(I * thetaPhase t)`,其相位不正确,不能作为
  square-root AFE 使用。
- 本文件中的目标使用精确的 `exp(-2 * I * thetaPhase t)` multiplier。
- 短期不需要证明(本任务为"目标声明"占位),故本文件不写证明,
  只声明 `def ... : Prop`。
-/

import HardyTheorem

open Complex Asymptotics Filter
open scoped ComplexConjugate

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

/-! ## 2. Exact normalization of the critical-line dual phase -/

/-- The unit phase of `Gammaℝ (1/2 + I*t)` is `exp (I * thetaPhase t)`.

This repackages the already proved real/imaginary-part theorem in a form that
can be used without choosing an argument branch. -/
theorem criticalGamma_div_norm_eq_exp (t : ℝ) :
    Gammaℝ ((1 / 2 : ℂ) + I * t) /
        ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ =
      Complex.exp (I * (thetaPhase t : ℂ)) := by
  let s : ℂ := (1 / 2 : ℂ) + I * t
  have hGamma : Gammaℝ s ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp [s]
  have hnorm : (‖Gammaℝ s‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.mpr hGamma).ne'
  have hcomponents := Gammaℝ_re_im_arg t
  have hexpRe :
      (Complex.exp (I * (thetaPhase t : ℂ))).re =
        Real.cos (thetaPhase t) := by
    rw [show I * (thetaPhase t : ℂ) = (thetaPhase t : ℂ) * I by ring]
    exact Complex.exp_ofReal_mul_I_re _
  have hexpIm :
      (Complex.exp (I * (thetaPhase t : ℂ))).im =
        Real.sin (thetaPhase t) := by
    rw [show I * (thetaPhase t : ℂ) = (thetaPhase t : ℂ) * I by ring]
    exact Complex.exp_ofReal_mul_I_im _
  have hGammaEq :
      Gammaℝ s = (‖Gammaℝ s‖ : ℂ) *
        Complex.exp (I * (thetaPhase t : ℂ)) := by
    apply Complex.ext
    · simpa [s, hexpRe] using hcomponents.1
    · simpa [s, hexpIm] using hcomponents.2
  change Gammaℝ s / (‖Gammaℝ s‖ : ℂ) = _
  apply (div_eq_iff hnorm).2
  simpa [mul_comm] using hGammaEq

/-- The exact dual multiplier in the critical-line approximate functional
equation.  The factor `-2` is essential. -/
noncomputable def criticalAfeDualPhase (t : ℝ) : ℂ :=
  Complex.exp (-2 * I * (unwrappedRiemannSiegelTheta t : ℂ))

/-- The dual phase is independent of replacing the principal theta by the
currently chosen unwrapped representative. -/
theorem criticalAfeDualPhase_eq_exp_neg_two_thetaPhase (t : ℝ) :
    criticalAfeDualPhase t =
      Complex.exp (-2 * I * (thetaPhase t : ℂ)) := by
  rfl

/-- On the critical line the ratio
`conj (Gammaℝ s) / Gammaℝ s` is exactly the AFE dual phase
`exp (-2 * I * thetaPhase t)`.

This proves the normalization only; it does not prove an approximate
functional equation or a remainder estimate. -/
theorem criticalGamma_conj_div_gamma_eq_dualPhase (t : ℝ) :
    conj (Gammaℝ ((1 / 2 : ℂ) + I * t)) /
        Gammaℝ ((1 / 2 : ℂ) + I * t) =
      criticalAfeDualPhase t := by
  let s : ℂ := (1 / 2 : ℂ) + I * t
  have hGamma : Gammaℝ s ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp [s]
  have hnorm : (‖Gammaℝ s‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.mpr hGamma).ne'
  have hunit := criticalGamma_div_norm_eq_exp t
  change conj (Gammaℝ s) / Gammaℝ s = _
  change Gammaℝ s / (‖Gammaℝ s‖ : ℂ) = _ at hunit
  have hGammaEq :
      Gammaℝ s = (‖Gammaℝ s‖ : ℂ) *
        Complex.exp (I * (thetaPhase t : ℂ)) := by
    have h := (div_eq_iff hnorm).mp hunit
    simpa [mul_comm] using h
  have hconjExp :
      conj (Complex.exp (I * (thetaPhase t : ℂ))) =
        Complex.exp (-I * (thetaPhase t : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  rw [hGammaEq]
  rw [map_mul, Complex.conj_ofReal, hconjExp]
  apply (div_eq_iff (mul_ne_zero hnorm (Complex.exp_ne_zero _))).2
  calc
    (‖Gammaℝ s‖ : ℂ) *
          Complex.exp (-I * (thetaPhase t : ℂ)) =
        (‖Gammaℝ s‖ : ℂ) *
          (criticalAfeDualPhase t *
            Complex.exp (I * (thetaPhase t : ℂ))) := by
      congr 1
      rw [criticalAfeDualPhase_eq_exp_neg_two_thetaPhase, ← Complex.exp_add]
      congr 1
      ring
    _ = criticalAfeDualPhase t *
          ((‖Gammaℝ s‖ : ℂ) *
            Complex.exp (I * (thetaPhase t : ℂ))) := by ring

/-! ## 3. Corrected AFE target -/

/-- Approximate functional equation 目标(Phase 2 校正版)。

形式:`∃ R > 0, ∀ t > 1, ∃ R' : ℂ, ζ(1/2 + I·t) = finite_sum + R' ∧ ‖R'‖ ≤ R · t^(-1/4)`,
其中 dual sum 的相位是上面已证明的
`criticalAfeDualPhase t = exp(-2I · thetaPhase t)`。此定义只声明
待证命题;它不向下游提供任何未证明的 analytic input。-/
def zeta_critical_afe_target : Prop :=
    ∃ R > (0 : ℝ), ∀ t : ℝ, t > 1 → ∃ R' : ℂ,
      (riemannZeta ((1 / 2 : ℂ) + I * t) =
        (∑ n ∈ Finset.range (Nat.floor (Real.sqrt (t / (2 * Real.pi)))),
            1 / ((n + 1 : ℂ) ^ ((1 / 2 : ℂ) + I * t))
         + criticalAfeDualPhase t *
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
         + criticalAfeDualPhase t *
            ∑ n ∈ Finset.range (Nat.floor (Real.sqrt (t / (2 * Real.pi)))),
              1 / ((n + 1 : ℂ) ^ ((1 / 2 : ℂ) - I * t))
         + R')) ∧
      ‖R'‖ ≤ R * (t : ℝ) ^ (-1 / 4 : ℝ)) :
    zeta_critical_afe_target :=
  ⟨R, hR, hrem⟩

end HardyTheorem.AFE
