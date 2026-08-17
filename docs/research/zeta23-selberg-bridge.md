# Zeta23 → Selberg/Conrey 目标蕴含链（外部机器检查证明闭合）

## 一句话结论

Anthropic 的机器检查 Lean 仓库
[`anthropics/zeta-23-lean`](https://github.com/anthropics/zeta-23-lean)
（论文 *More than two thirds of the zeros of the Riemann zeta function lie
on the critical line*，2026）的 **Theorem B**（至少 2/3 的 zeta 零点是简单
的且在临界线上）**形式化蕴含**本仓库的两个开放 `def ... : Prop` 目标：

- `HardyTheorem.selberg_odd_zero_proportion_target`
- `KnownResults.conrey_40_percent_zeros_on_critical_line_target`

闭合**不需要任何新的解析数学**——只需要定义级桥接引理 + 组装。本文件把
这条蕴含链写成精确的数学陈述，作为合并的蓝图。

## 两边的目标形状

本仓库开放目标（`HardyTheorem/CriticalLineMultiplicity.lean:250`）：

```lean
selberg_odd_zero_proportion_target : Prop :=
  ∃ c > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
    (criticalLineOddZeroCount T : ℝ) ≥ c * (T / (2 * Real.pi) * Real.log T)
```

其中 `criticalLineOddZeroCount T` = 临界线 `Re s = 1/2` 上、`0 ≤ Im ≤ T`、
**奇解析重数**的零点，每个计一次（Finset 基数）。

Zeta23 侧（`comparator/Solution/Multiplicity.lean`）：

```lean
two_thirds_simple_on_critical_line_cumulative :
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T
```

其中 `Ncount 0 T` = 临界带内 `0 < Im ≤ T` 的零点（按重数计），`N0simple 0 T`
= 临界线上**简单**零点（去重计）。该定理的证明位于
`Zeta23.thmB₀_mult_cumulative`（`Zeta23/FinalMult.lean:365`）。

## 蕴含链（三步桥接）

### 引理 1：简单 ⊂ 奇重数（定义级，易证）

```
N0simple 0 T ≤ criticalLineOddZeroCount T
```

理由：简单零点解析重数为 1（奇数），且每个去重的简单临界线零点都落入
`criticalLineZerosFinset T` 的奇重数子集。边界 `Im = 0` 无临界带零点
（`ζ(1/2) ≠ 0`，临界带内无实零点），故 Zeta23 的 `(0, T]` 与仓库的
`[0, T]` 一致。

### 引理 2：主项下界（Zeta23 自带 RvM，无需对齐仓库计数）

```
Ncount 0 T ≥ (1 - ε') * (T / (2π) * log T)     （最终成立）
```

来源：Zeta23 自带 Riemann–von Mangoldt 模块（`Zeta23/RvM/`）对
`Ncount` 给出 `Ncount 0 T = T/(2π)·log(T/2π) − T/(2π) + O(log T)`，
取下界即可。**注意**：这里直接用 Zeta23 自己的 RvM，避免与本仓库
`riemannZeroCount` 做跨定义对齐。

### 引理 3：组装

```
criticalLineOddZeroCount T
  ≥ N0simple 0 T                       （引理 1）
  ≥ (2/3 − ε) · Ncount 0 T             （Zeta23 Thm B cumulative）
  ≥ (2/3 − ε)(1 − ε′) · T/(2π) · log T （引理 2）
```

取 `c = (2/3 − ε)(1 − ε′) > 0`（例如 ε = ε′ = 1/12 得 c = 77/144 ≈ 0.5347），
即得 `selberg_odd_zero_proportion_target`。

### 下游（复用仓库现有引理，零新工作）

```
selberg_odd_zero_proportion_target
  → selberg_zero_proportion_target          （CriticalLineMultiplicity.lean:
                                              selberg_zero_proportion_target_of_odd）
  → conrey_40_percent_zeros_on_critical_line_target
                                            （RiemannExplorer.lean:
                                              conrey_40_percent_zeros_on_critical_line_target_of_selberg）
```

## 闭合清单

| 仓库目标 | 状态 | 来源 |
|---|---|---|
| `HardyTheorem.selberg_odd_zero_proportion_target` | **闭合**（若合并） | Zeta23 Thm B + 引理 1–3 |
| `KnownResults.conrey_40_percent_zeros_on_critical_line_target` | **闭合**（若合并） | 上一步 + 现有两引理 |
| 其余 10 个开放目标 | 不受影响 | Zeta23 与 VK/RH 误差/Hardy 渐近无关 |

## 不闭合的边界（诚实声明）

- `Global.vinogradov_korobov_zero_free_region`：Zeta23 不含指数和/VK 内容；
- `PrimeNumberTheorem.RH_*` 四个 RH 误差目标：Zeta23 是线上比例定理，与
  RH 误差尺度无关；
- `HardyTheorem.integral_asymptotic_target`、`hardy_two_signed_moments_target`、
  `HardyTheorem.Details.*`：对象是 Hardy `Z` 函数矩渐近，与 Zeta23 无关。

## 合并蓝图（Phase 3，若决策门通过）

1. 升级工具链至 `v4.33.0-rc2`、Mathlib 至 `v4.33.0-rc2`（commit
   `51e6992efd06126df61a496bebf8f49482a4e129`）；
2. 把 Zeta23 源码作为 tracked 树 vendor 进仓库（保留 Apache 2.0 头）；
3. 新文件 `HardyTheorem/Zeta23SelbergBridge.lean`：引理 1 + 引理 3 组装
   （引理 2 直接引用 vendored 的 `Zeta23/RvM/`），定理
   `selberg_odd_zero_proportion_target_of_zeta23`；
4. `Test/Zeta23SelbergBridgeContract.lean` + `AxiomAudit.lean`（仅三个标准
   公理）；
5. 目标清册与 README 更新。

## 参考

- 仓库：<https://github.com/anthropics/zeta-23-lean>（Apache 2.0，commit 见
  `zeta23-external-verification.md`）
- 论文：*More than two thirds of the zeros of the Riemann zeta function lie
  on the critical line*（Claude / Anthropic, 2026），Theorem B [thm:B]
- 本仓库开放目标出处：`HardyTheorem/CriticalLineMultiplicity.lean`（250 行）、
  `RiemannExplorer.lean`（235 行）

## 验证状态（2026-08-16，已合并 main）

- Zeta23 完整构建通过（`ZETA23_RESUME10_EXIT=0`，312 个模块 olean）；
- 桥接输入定理 `Zeta23.thmB₀_mult_cumulative` 的 `#print axioms` 审计：
  **仅 `[propext, Classical.choice, Quot.sound]`**，无 `sorry`/自定义公理；
  签名与本文件引理 1–3 的蓝图完全吻合（cumulative 形式，`(2/3 − ε)` 系数）；
- **桥接已完成并合并到 `main`**(merge commit `f92f9965`):`HardyTheorem/Zeta23SelbergBridge.lean`
  组装了引理 1–3,定理 `selberg_odd_zero_proportion_target_of_zeta23` 与
  `conrey_40_percent_zeros_on_critical_line_target_of_zeta23` 均在仓库内核内
  证明,显式常数 `7/48`,公理审计仅三个标准公理;`Test/Zeta23SelbergBridgeContract.lean`
  与 `Test/Zeta23SelbergBridgeAxiomAudit.lean` 随附;
- 合并后 `main` 全量桥接闭包构建通过(`lake build`,8885 jobs);
- 上游 LICENSE/NOTICE 已随 `Zeta23/` vendor;全部来源与归属见
  [zeta23-merge-provenance.md](zeta23-merge-provenance.md)。
