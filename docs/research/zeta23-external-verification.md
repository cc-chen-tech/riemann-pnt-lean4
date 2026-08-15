# Zeta23 外部验证记录（anthropics/zeta-23-lean）

## 目的

在把 Anthropic 的 [`zeta-23-lean`](https://github.com/anthropics/zeta-23-lean)
合并进本仓库之前，按本仓库的纪律独立验证该外部工件：**构建通过、无 `sorry`、
`#print axioms` 仅报告 Lean 三个标准公理**（`propext`、`Classical.choice`、
`Quot.sound`）。本文件记录验证命令、结论与复现方法；任何"合并可闭合目标"
的声明都以这里的验证结果为前提。

## 工件信息

- 仓库：<https://github.com/anthropics/zeta-23-lean>
- 论文：*More than two thirds of the zeros of the Riemann zeta function lie
  on the critical line*（Claude / Anthropic, San Francisco, 2026）
- 许可：Apache 2.0（LICENSE / NOTICE 随仓库）
- 工具链：Lean `v4.33.0-rc2`；Mathlib commit
  `51e6992efd06126df61a496bebf8f49482a4e129`（tag `v4.33.0-rc2`，
  记录于 `lake-manifest.json`）
- 规模：329 个 `.lean` 文件，约 103,000 行（浅克隆 `--depth 1` 核验日期
  2026-08-14）

## 结构

```
comparator/   受信任声明（ChallengeDeps, Challenge）+ 不受信任的 Solution + 对照器
Zeta23/       正式证明：Final.lean (A/B/C), ThmD/ (最优窗口), ThmE/ThmDE/ (L 函数),
              LinAlg/ (rank-trace 核心), WeilEF/ 显式公式, RvM/, GammaFacts/,
              Chebyshev.lean, MV/ (Montgomery–Vaughan), PrimeSide/, ZeroSide/, Tail/,
              Assembly/, XiPrime/, PairCeiling/
```

关键定理（用于本仓库桥接）：

- `comparator/Solution/Multiplicity.lean`：
  `two_thirds_simple_on_critical_line`（dyadic）与
  `two_thirds_simple_on_critical_line_cumulative`（cumulative），证明本体
  `Zeta23.thmB₀_mult` / `Zeta23.thmB₀_mult_cumulative`
  （`Zeta23/FinalMult.lean:350/365`）。

## 验证命令（复现）

```bash
# 在独立克隆中（避免污染本仓库）
git clone --depth 1 https://github.com/anthropics/zeta-23-lean /tmp/zeta23
cd /tmp/zeta23
elan toolchain install leanprover/lean4:v4.33.0-rc2   # 或由 lake 自动安装
lake exe cache get        # 拉取 Mathlib 预编译缓存（数 GB）；失败则本地构建数小时
lake build                # 构建 Zeta23 库（默认 target 导入头条模块）
# axiom 审计：15 + 12 + 6 个受信任声明的对照
lake env lean comparator/PrintAxioms.lean
lake env lean comparator/PrintAxioms/Multiplicity.lean
lake env lean comparator/PrintAxioms/XiPrime.lean
lake env lean comparator/PrintAxioms/PairCeiling.lean
```

预期：无错误、`Zeta23/` 与 `Solution` 无 `sorry` 警告（`comparator/` 下的
受信任挑战文件内是刻意保留的 `sorry`），axiom 审计输出 33 行
`'...' depends on axioms: [propext, Classical.choice, Quot.sound]`。

## 验证状态（2026-08-14，本会话）

- [x] 浅克隆成功，结构与 README 描述一致（文件/模块核验）；
- [x] **`lake build` 构建成功**：`ZETA23_RESUME10_EXIT=0`。完整构建在受限
  环境（16GB 内存、外部 SIGINT 频繁中断、github.com 间歇性不可达）下经过
  多次可恢复续跑完成；mathlib（8.7GB olean）+ Zeta23 库（312 个模块 olean）
  全部编译通过，含桥接所需的 `Zeta23.FinalMult`（`thmB₀_mult_cumulative`）；
- [x] **桥接定理 axiom 审计通过**：`lake env lean` 对
  `Zeta23.thmB₀_mult_cumulative` 执行 `#print axioms`，输出：

  ```lean
  Zeta23.thmB₀_mult_cumulative (ε : ℝ) :
    ε > 0 → ∃ T₀, ∀ T ≥ T₀, (2 / 3 - ε) * ↑(Zeta23.Ncount 0 T) ≤ ↑(Zeta23.N0simple 0 T)
  'Zeta23.thmB₀_mult_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

  即：定理签名与桥接蓝图（`zeta23-selberg-bridge.md` 引理 1–3）完全吻合，
  且只依赖 Lean 三个标准公理——**"外部机器检查证明"标注在此升级为已验证
  结论**（该定理层面）；
- [x] **完整 comparator 对照审计通过**（`AUDIT_DONE`）：`Solution` /
  `Solution.Multiplicity` / `Solution.XiPrime` / `comparator` 全部构建
  （9002 jobs），`#print axioms` 输出抽样：

  ```text
  'two_thirds_on_critical_line'            depends on axioms: [propext, Classical.choice, Quot.sound]
  'two_thirds_on_critical_line_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
  'two_thirds_simple_on_critical_line'     depends on axioms: [propext, Classical.choice, Quot.sound]
  'two_thirds_simple_on_critical_line_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
  'five_sixths_distinct'                   depends on axioms: [propext, Classical.choice, Quot.sound]
  'five_sixths_distinct_cumulative'        depends on axioms: [propext, Classical.choice, Quot.sound]
  'xiPrime_simple_zeros_on_critical_line'(_cumulative) depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

  即：Zeta23 的 Theorem A/B/C 与 ξ′ 附加结果全部无 `sorry`、无自定义公理。
  **结论：Zeta23 是一个完整、可构建、axiom 干净的外部机器检查证明
  （按本仓库自己的"内核检查即证明"标准）。**

## 声明边界

1. 本文件只验证"该仓库确实证明了它声称的定理"（内核检查层面）；不评估
   论文的同行评审状态，也不评估方法的新颖性——对本仓库而言，内核检查即
   仓库自己的"已证明"标准（见 README 与 `docs/implementation-standards.md`）。
2. 验证只针对 Zeta23 本身；"Zeta23 Thm B ⇒ 本仓库两目标"的桥接是**本
   仓库侧**的工作，见 `zeta23-selberg-bridge.md`，不属于 Zeta23 的声明。
3. 工具链差异（本仓库 4.29.1 vs Zeta23 4.33.0-rc2）意味着直接 merge 前
   必须经过 `research/zeta23-toolchain-triage` 的迁移试测（决策门）。
