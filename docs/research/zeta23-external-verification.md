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
- [ ] 工具链安装 + `lake build` + axiom 审计：**待网络恢复**（会话期间
  `github.com:443` 间歇性不可达，工具链与 Mathlib 缓存下载受阻；重试任务
  `bash-4` 在后台运行）。完成前，README 与目标清册中的"外部机器检查证明"
  标注视为**待验证声明**，不升级为结论。

## 声明边界

1. 本文件只验证"该仓库确实证明了它声称的定理"（内核检查层面）；不评估
   论文的同行评审状态，也不评估方法的新颖性——对本仓库而言，内核检查即
   仓库自己的"已证明"标准（见 README 与 `docs/implementation-standards.md`）。
2. 验证只针对 Zeta23 本身；"Zeta23 Thm B ⇒ 本仓库两目标"的桥接是**本
   仓库侧**的工作，见 `zeta23-selberg-bridge.md`，不属于 Zeta23 的声明。
3. 工具链差异（本仓库 4.29.1 vs Zeta23 4.33.0-rc2）意味着直接 merge 前
   必须经过 `research/zeta23-toolchain-triage` 的迁移试测（决策门）。
