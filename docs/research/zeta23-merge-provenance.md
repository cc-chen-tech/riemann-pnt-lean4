# Zeta23 合并的来源与归属说明 / Provenance of the Zeta23 merge

本文档说明 `research/zeta23-toolchain-triage` 分支(及其向 `main` 的合并)中
**每一部分内容的来源**,确保外部工作不会被误认为本仓库作者的工作。

This document records where every piece of the Zeta23 merge comes from, so
that external work is never mistaken for this repository's own authorship.

---

## 1. `Zeta23/` — 外部代码库,非本仓库工作

**来源**:Anthropic 的 [`anthropics/zeta-23-lean`](https://github.com/anthropics/zeta-23-lean)
(论文 *More than two thirds of the zeros of the Riemann zeta function lie
on the critical line*,2026)。

- 上游 commit:`3635e74826a4c1fcece7d1cd2b6fa75e43a00510`(2026-08 vendor 时点);
- 许可:**Apache License 2.0**;版权:**Copyright 2026 Anthropic, PBC**;
- 每个源文件的版权头均已原样保留(`Copyright (c) 2026 Anthropic...`);
- `Zeta23/LICENSE` 与 `Zeta23/NOTICE` 已随代码一并 vendor;
- `Zeta23/NOTICE` 声明该库包含派生自
  [`PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
  (Kontorovich–Tao 项目)的软件;
- **代码未做任何修改**(仅接入本仓库的 lakefile 构建)。

The `Zeta23/` directory is vendored verbatim from Anthropic's repository
under Apache 2.0.  It is **not** the work of this repository's author.

## 2. `HardyTheorem/Zeta23SelbergBridge.lean` — 定义级桥接(本仓库侧组装)

本文件证明的是**桥接**,不是新的解析数学:

- 输入一:`Zeta23.thmB₀_mult_cumulative`(Theorem B:至少 2/3 的零点简单且在
  临界线上)——**Anthropic 的机器检查定理**(上表来源);
- 输入二:本仓库自己的全高度 Riemann–von Mangoldt 下界
  (`exists_eventually_riemannZeroCount_ge_selbergScale`)——本仓库此前的工作;
- 桥接内容:零点集合与重数函数的定义级对齐、简单⊂奇重的集合包含、不等式组装
  (显式常数 7/48)。

结论归属于:两个输入各自的作者 + 组装者。**不要把 Theorem B 本身归因于本仓库。**

The bridge assembles Anthropic's machine-checked Theorem B with this
repository's own Riemann–von Mangoldt lower bound; the analytic content is
theirs, the definition-level assembly is the bridge's only contribution.

## 3. VK-edge manuscript 与 paper-gates — 条件于外部定理

`docs/research/vk-edge-zero-oscillation-manuscript.md` 与
`docs/research/vk-edge-zero-oscillation-paper-gates.md` 的论证**条件于**:

- **Bellotti**, *A new zero-density estimate for the Riemann zeta function
  and the error term in the Prime Number Theorem*,
  Bull. London Math. Soc. / [arXiv:2508.02041](https://arxiv.org/abs/2508.02041)
  —— 使用的输入:VK 边缘零点的有界计数(其 Theorem 1.2 的推论);
- **Révész**, *Oscillation of the remainder term in the prime number theorem
  of Beurling, caused by a given zeta-zero*, IMRN 2023 /
  [arXiv:2202.01837](https://arxiv.org/abs/2202.01837)
  —— 使用的输入:移位围道、留数多项式与 Cassels 长度的构造(其 Theorem 6 的
  证明部件);
- 对比文献:**Schlage-Puchta** [arXiv:1912.00853](https://arxiv.org/abs/1912.00853);
- 预注册对比:**Neuwirth** [arXiv:2603.28229](https://arxiv.org/abs/2603.28229)。

两个文档均明确声明:**在优先权核查与外部专家审阅完成前,不得宣称新结果。**

Both notes are explicitly conditional on the cited Bellotti and Révész
theorems and must not be presented as new results before priority checks.

## 4. `MathlibAux/FiniteSpectrumGap.lean` — 本仓库纸面证明的形式化

本模块形式化的是**本仓库自己的**纸面证明记录
(`docs/research/vk-edge-pi-over-two-proof-record.md`,缺失奇谐波论证)。
不依赖外部定理。完整间隙定理仍为 `Prop` 目标(未证)。

## 5. 4.33 工具链迁移修复 — 本仓库自身代码的机械修复

`ZeroFreeRegion/MeromorphicAux.lean`、`HardyTheorem/FirstZetaApproximation.lean`
等约 15 个文件的 4.33 迁移修复是对**本仓库自身代码**的机械修复
(API/记法/simp 行为变化),不产生新的数学内容,也不引用外部证明。

## 6. 提交身份说明

`feat(zeta23): close Selberg/Conrey targets...`(0c39c2dd)与
`feat(research): finite-spectrum gap formal statements...`(95726fbd)及本说明
文档由**自动化 AI 编码会话**产生;其中引用的数学内容分别属于上表所列的作者
(Anthropic / Bellotti / Révész 等)。
