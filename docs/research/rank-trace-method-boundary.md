# rank–trace 方法能力边界对账（Zeta23 天花板 × 仓库审计）

## 目的

把两条互为正/负的证据放在一起，精确钉死"rank–trace（有限秩证书）方法"
在黎曼 zeta 问题上的能力边界：

1. **正面（线上计数）**：Zeta23 用 rank–trace 不等式把"临界线上简单零点
   比例"推到 2/3（最优窗口 0.67250），并证明该方法已接近自身天花板；
2. **负面（线外排除）**：本仓库 `growth-budget-audit` 证明固定秩证书的
   推力（O(1) 谱间隙）会被随高度增长的误差淹没，不能排除临界线外零点。

合起来：**rank–trace 是"线上比例"问题的有效（且接近饱和的）工具，却
不是"线外排除/RH"问题的工具。** 两条结论互相印证，不存在矛盾。

## 证据一：Zeta23（线上比例，正面 + 天花板）

- 定理 A：`liminf N₀*(T,2T)/N(T,2T) ≥ 2/3`；
- 定理 B：`liminf N₀ˢ(T,2T)/N(T,2T) ≥ 2/3`（简单零点，dyadic + cumulative）；
- 定理 C：`liminf N_d/N ≥ 5/6`（不同零点）；
- 定理 D：最优 Montgomery–Taylor 窗口下 `≥ 2 − 1/c₁* = 0.67250…`，
  `c₁* = √2·tanϑ/(1+ϑ·tanϑ)`，ϑ = 1/√2；
- **Lemma R tightness**（`Zeta23/ZeroSide/TightMult.lean`）：对整数重数
  `m_j ≤ c` 的线上原子 + b 个特征值 c 的配对块，
  `2c·tr(P+Q) − ‖P+Q‖_F² = Σ_j k_c(m_j) + c²·b` —— 不等式**取等**，即只用
  这些量无法再改进；
- **bandwidth-one 天花板**（`Zeta23/PairCeiling/`）：任何此类证书最多证明
  简单零点比例 `0.6818287 + 2.55·10⁻⁶·(|r′(1)| + ∫|r″|)` —— 2/3 结果已经
  贴着 0.6818 的天花板（差 < 0.015）。

含义：在该方法内部，67.25% 已接近机制上限；要突破需要新机制（更高的
bandwidth、新的守恒量），而不是在证书里调参。

## 证据二：仓库 growth-budget 审计（线外排除，负面）

`docs/research/exceptional-zero-growth-budget-audit.md`（第三阶 worktree 内，
已并入本说明的核对范围）证明：对"有限簇 + 固定秩证书"结构，

1. **无持续性**：只能保证一步严格更新，无法迭代；
2. **无条带定位**：witness 不落在 Carlson 计数条带 `Re ρ > σ` 内；
3. **速率死墙**：每窗口一个 witness 的粒度给出 `O(log T)`/`O(log log T)`
   个零点，而 Carlson 上界是幂级 `T^{4σ(1−σ)}(log T)^4`——`log T = o(T^α)`
   是 Mathlib 已证事实。

即固定秩证书的"推力"是 O(1) 的，而它要压过的误差随高度幂式增长。

## 对账结论

| 问题 | 方法 | 结论 |
|---|---|---|
| 临界线上零点比例 ≥ c | rank–trace（c = 2 简单 / c = 3 去重） | **成功**：2/3、5/6、0.67250，接近天花板 0.6818 |
| 排除临界线外零点（RH） | 固定秩证书 + 固定簇 L² 强制性 | **失败**：审计证明推力不增长，被增长误差淹没 |

两条证据不矛盾：线上计数是"统计"问题（大量零点、谱平均），rank–trace 的
有限秩 + 平均结构正好匹配；线外排除是"单零点尺度"问题，需要的是**随高度
增长的检测器或删有限集稳定的增长型下界**——正是仓库审计点名缺失的输入。

## 对本仓库的意义

1. **避免重复劳动**：仓库曾探索 rank–trace / 有限维证书方向（`WeilExtremal
   Kernels`、`vk-edge-annihilator` 相关文档）。外部证据表明：同样的工具在
   线上比例问题上是正资产（且接近饱和），在线外排除问题上是死路——这与
   仓库 `growth-budget-audit` 的结论方向一致，可以互相引用。
2. **Selberg 方向的选择**：若未来想闭合 `selberg_odd_zero_proportion_target`
   （比例类目标），rank–trace 是**已知可行且已有完整机器检查参考实现**的
   路线（见 `zeta23-selberg-bridge.md`）；不要把它误用于 RH 矛盾程序。
3. **文档化引用**：本对账可作为仓库审计文档的外部佐证，引用
   Zeta23 的 tightness（`Zeta23.ZeroSide.TightMult.lemmaR_tight`）与
   bandwidth-one 天花板（`Zeta23.PairCeiling.ceiling_stability`、
   `ceiling_law256`）。

## 边界声明

- 本对账是**方法层面的判断**，不是定理；Zeta23 的 tightness/天花板是
  内核检查的定理，仓库的 growth-budget 阻塞点也是内核检查的结论，但
  "两者共同证明方法 X 不能用于 Y"是人的综合判断；
- Zeta23 的 2/3 与仓库的 2/3 阈值（`PsiPowerErrorBelowTwoThirds`）数字
  相同、含义无关，勿混用。
