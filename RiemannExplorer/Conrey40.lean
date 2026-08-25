/-
# 旧版 Conrey 名称兼容别名（实际是 Selberg 正比例目标）

本文件只保留历史调用接口。这里的命题要求临界线上存在某个正比例，
并且定义上等同于 Selberg 目标；它**不是** Conrey 1989 年关于简单零点
严格超过 `2/5` 的定理。`HardyTheorem.lean:1319` 处的
`HardyTheorem.zeroCountOnCriticalLine T` 统计 `Im(s) ∈ [0, T]` 区间内
`Re(s) = 1/2` 上的非平凡零点个数。

## 完整 statement(实数陈述,数学含义清晰)

```
∃ c > 0, ∃ T₀ > 0, ∀ T ≥ T₀,
  (HardyTheorem.zeroCountOnCriticalLine T : ℝ) ≥
    c * T / (2 * Real.pi) * Real.log T
```

真正的 Conrey 目标现在定义为
`HardyTheorem.conreyTwoFifthsSimpleZerosTarget`：分子只计简单临界线零点，
分母 `riemannZeroCount` 按解析重数计全部非平凡零点，并要求 `c > 2/5`。

## 与 Selberg 1962 的关系

Conrey 的简单零点定理确实强于 Selberg 正比例定理，但本文件中的旧命名
没有表达这一区别。它与 `HardyTheorem.selberg_zero_proportion_target`
互推仅仅因为二者定义相同。本文件继续保留该别名，避免静默破坏调用方；
新证明必须使用上面的 multiplicity-sensitive 目标。

## 前置依赖(已存在,本文件不重新实现)

- `HardyTheorem.zeroCountOnCriticalLine`(`HardyTheorem.lean:1319`,
  `noncomputable def`)
- `RiemannExplorer.conrey_40_percent_zeros_on_critical_line_target`
  (真 statement 版,见 `RiemannExplorer.lean:235`)
- 命名空间:本文件使用 `RiemannExplorer.Conrey40` 子命名空间,避免
  与上层 `RiemannExplorer.conrey_40_percent_zeros_on_critical_line_target`
  的 bare name 冲突。

## 修正 TASK_BRIEF 的一处 cross-reference

`TASK_BRIEF.md` 提到"`RiemannExplorer.zeroCountOnCriticalLine`",
但实际 `zeroCountOnCriticalLine` 定义在
`HardyTheorem.zeroCountOnCriticalLine`(`HardyTheorem.lean:1319`)。
`RiemannExplorer.lean` 中没有同名定义,引用应使用 `HardyTheorem` 命名空间。
-/

import RiemannExplorer
import HardyTheorem.ConreyTwoFifthsBridge

namespace RiemannExplorer
namespace Conrey40

/-! ## 核心 def(Prop 目标别名) -/

/-- 历史名称兼容别名；数学内容只是 Selberg 正比例目标。

**完整 statement**(数学含义,见本文件顶部 doc-comment):

```
∃ c > 0, ∃ T₀ > 0, ∀ T ≥ T₀,
  (HardyTheorem.zeroCountOnCriticalLine T : ℝ) ≥
    c * T / (2 * Real.pi) * Real.log T
```

`HardyTheorem.zeroCountOnCriticalLine T` 是 `Re(s) = 1/2` 且 `Im(s) ∈ [0, T]`
区间上非平凡零点的个数,定义见 `HardyTheorem.lean:1319`。

本目标不再使用 `True` 占位；它直接别名到上层
`KnownResults.conrey_40_percent_zeros_on_critical_line_target` 的真实
statement，但不能据此称为真正的 Conrey `> 2/5` 定理。 -/
def conrey_40_percent_zeros_on_critical_line_target : Prop :=
  KnownResults.conrey_40_percent_zeros_on_critical_line_target

/-! ## Alias sanity-check lemma -/

/-- Alias sanity check: the submodule interface is definitionally the same
target as the upper-level `KnownResults` statement. -/
lemma conrey_40_percent_zeros_on_critical_line_target_iff_known :
    conrey_40_percent_zeros_on_critical_line_target ↔
      KnownResults.conrey_40_percent_zeros_on_critical_line_target :=
  Iff.rfl

end Conrey40
end RiemannExplorer
