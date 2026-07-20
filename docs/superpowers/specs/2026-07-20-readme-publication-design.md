# 投稿型 README 重构设计

## 目标

将仓库首页从内部研究日志重构为适合论文投稿、同行评审和公开传播的项目入口。
README 以中文为主要叙事语言，以英文摘要和英文术语作为国际读者的辅助入口。
读者应当能够在几分钟内回答四个问题：

1. 这个项目研究什么，为什么重要？
2. 当前 `main` 分支已经机械验证了哪些数学结论？
3. 哪些结果只存在于研究分支，哪些仍是 `def ... : Prop` 目标？
4. 如何复现构建、检查公理依赖并引用该项目？

## 目标读者

主要读者按以下顺序排列：

1. 形式化数学、交互式定理证明和自动推理领域的审稿人；
2. 对 Riemann zeta 函数和解析数论感兴趣的数学研究者；
3. 不具备复分析或 Lean 背景、但希望理解项目意义的普通技术读者；
4. 希望复现、扩展或审计证明的 Lean 开发者。

README 不以内部任务调度、逐日研究日志或完整模块索引为主要用途。这些内容应保留在
`docs/` 中，并由 README 链接。

## 内容结构

### 1. 双语标题与一句话定位

中文主标题：

> Lean 4 中黎曼 zeta 函数的形式化解析数论

英文副标题：

> Formalized Analytic Number Theory for the Riemann Zeta Function in Lean 4

标题下方用一句中文和一句英文说明：本项目在 Mathlib 上机械验证 Riemann zeta
函数、素数定理和零点分布中的一组经典解析数论定理。

### 2. 面向非数学专业读者的介绍

最前面的中文介绍控制在约 700--1000 个汉字，并避免从公式或模块名称开始。它需要说明：

- 素数分布为什么既有规律又难以精确预测；
- zeta 函数的零点如何控制素数计数误差和振荡；
- Riemann 假设在这张图景中的位置；
- Lean 如何把传统证明转换为内核可检查的证明项；
- 项目已经验证多项经典定理，但没有证明 RH。

介绍可以使用一个低门槛类比，但不得用类比替代数学声明。所有涉及“证明了什么”的句子
必须能在后续定理表中找到对应 Lean 声明。

### 3. English Summary

提供 150--250 词的独立英文摘要，覆盖：

- project scope and Mathlib dependency;
- the verified headline theorems on `main`;
- multiplicity-aware zero-counting and reusable analytic infrastructure;
- reproducibility and axiom-audit policy;
- explicit non-claims: no RH, no Vinogradov--Korobov region, and no numerical
  explicit constants unless separately proved.

英文摘要不逐句翻译中文介绍，而是服务于国际审稿人的快速判断。

### 4. 核心成果与状态表

使用一张紧凑表格列出当前公开成果。每行包含：

- 数学结论；
- Lean 定理标识符；
- 文件链接；
- 状态和验证边界。

`main` 的标题级结果至少包括：

- classical zero-free region;
- ordinary PNT and the classical de la Vallee Poussin error term;
- Hardy's theorem;
- all-height Riemann--von Mangoldt formula;
- fixed-sigma Carlson zero-density estimate;
- local-separation Hilbert and exponential mean-square estimates.

表格之后单独列出研究分支结果：

- Hardy--Littlewood linear lower bound and odd-multiplicity refinement;
- Pintz envelope foundation;
- Vinogradov--Korobov exponential-sum infrastructure;
- smoothed-error, zero-forced oscillation, and finite Weil certificates.

研究分支必须标明 branch、集成状态和未完成验证。它们不得与 `main` 的已验证成果混排。

### 5. 证明架构

使用一张 Mermaid 图展示三条主链：

1. `3-4-1 -> classical zero-free region -> Strong PNT`；
2. `Hardy -> Hardy--Littlewood -> Selberg target`；
3. `Riemann--von Mangoldt -> multiplicity counting -> Carlson zero density`。

图中节点需要使用“proved on main”、“proved on research branch”或“open target”三种明确
标签。图后用简短段落解释各链之间的数学关系。

### 6. 分层阅读与链接策略

README 采用“通俗解释 -> 数学细节 -> Lean 声明 -> 可复现验证”四层链接，而不是要求
读者一次读完整个证明工程。

通俗介绍中的关键术语应在首次出现时提供链接：

- “素数定理”和“Strong PNT”链接到项目内数学贡献说明及可靠的外部背景资料；
- “zeta 函数零点”和“Riemann 假设”链接到 Mathlib 定义、项目内零点说明及权威背景页；
- “零自由区域”链接到 `docs/zero-free-region-chain.md`；
- “显式公式”链接到 `docs/explicit-formula-chain.md`；
- “Hardy 定理”链接到 `docs/hardy-theorem-chain.md`；
- “RH 误差等价”链接到 `docs/rh-error-equivalence-chain.md`。

核心成果表中的每一行至少提供两类链接：

1. 对应 Lean 源文件的精确相对路径；
2. 面向人类读者的证明链或数学解释文档。

对于 Riemann--von Mangoldt、Carlson zero density 和 Carneiro--Littmann local-separation
三个目前缺少独立说明页的成果，实施阶段应先判断 `docs/mathematical-contributions.md`
能否提供足够稳定的锚点。如果不能，则分别增加短的 chain 文档。新文档应解释数学陈述、
证明分层、核心 Lean 定理和非声明边界，不复制源码清单。

“了解更多”链接优先使用仓库内相对链接，保证离线克隆后仍可导航。外部链接只用于：

- 原始或现代数学文献；
- Mathlib 官方文档；
- 其他正式化项目和投稿 venue；
- Riemann 假设等需要权威公共背景的主题。

链接文字必须描述目标内容，例如“Hardy 定理证明链”，而不是使用模糊的“点击这里”。
README 中的内部相对链接、标题锚点和源码路径需要纳入验收检查。

### 7. 论文与创新定位

README 应将数学经典性和形式化创新分开表述：

- 不声称发明 Riemann--von Mangoldt、Hardy、Hardy--Littlewood 或 Carlson 定理；
- 贡献重点是 Lean 4 形式化、乘重数零点基础设施、解析证明接口、可复现工件和公理审计；
- 不使用未经完整 prior-art 检索支持的“first formalization”表述；
- 可以使用“to the best of our knowledge”，但必须同时链接现有 Lean、HOL Light、
  Isabelle 和 Mathlib 相关工作。

论文包按成熟度分为：

1. 可立即整理：Riemann--von Mangoldt + Carlson + local-separation infrastructure；
2. 集成后可整理：Hardy + Hardy--Littlewood critical-line zero lower bounds；
3. 长期目标：Selberg positive proportion、Vinogradov--Korobov、Pintz oscillation bridge。

### 8. 复现与审计

README 只保留最短可复现路径：

- Lean/toolchain prerequisites;
- dependency setup;
- focused contract builds;
- baseline verification;
- full `lake build`；
- source scan and `#print axioms` policy.

详细命令、任务计数、目标清单和 chain-gap 报告链接到 `PUBLISHING.md` 及相关
`docs/` 文件。README 不把一次历史构建结果写成永久状态；需要日期时注明验证日期。

### 9. Related Work 与 Citation

相关工作至少覆盖：

- Math Inc. `strongpnt`；
- `PrimeNumberTheoremAnd`；
- Harrison 的 HOL Light analytic PNT；
- Eberl--Paulson 的 Isabelle PNT；
- Loeffler--Stoll 的 Mathlib zeta/L-function work；
- Carneiro--Littmann weighted Hilbert inequality。

Citation 提供软件条目，并预留论文条目位置，但在论文标题、作者列表、DOI 或 arXiv
标识确定前不填入占位信息。

## 信息迁移

现有 README 中以下内容应保留但移出首页：

- 大量逐定理接口名称；
- 移动 Perron 公式和 Jensen/Borel 中间层的完整演化记录；
- 所有 target-management wrapper 清单；
- 历史性的“下一步”段落；
- 超过首页阅读需要的文件索引。

迁移优先复用现有文件：

- `docs/mathematical-contributions.md`；
- `docs/formal-theorem-inventory.md`；
- `docs/target-statements-and-chains.md`；
- `docs/missing-chains-index.md`；
- `PUBLISHING.md`。

若现有文档不能无损容纳某一段内容，再增加一个 README archive 文档。不得直接删除
仍然准确且独有的技术说明。

## 验收标准

重构后的 README 必须满足：

1. 总长度约 350--500 行，第一屏不以公式或内部模块名开场；
2. 中文为主要叙事语言，英文摘要可独立理解项目贡献；
3. 所有标题级成果都有可点击源码链接和准确 Lean 定理名；
4. `main`、研究分支和开放目标严格分区；
5. 不声称 RH、Vinogradov--Korobov、Selberg 或 Pintz 最大阶已经证明；
6. 不将路线接口或 `def ... : Prop` 计作定理；
7. 构建和公理审计命令与当前仓库实际文件一致；
8. Markdown、表格、Mermaid 和本地链接经过渲染或静态检查；
9. 现有独有技术信息已迁移或有明确文档链接，没有静默丢失；
10. `git diff` 只包含 README 重构及必要的文档迁移，不包含 Lean 证明改动。
11. 通俗介绍中的主要数学概念、成果表和证明图均有可用的深入阅读链接；
12. 仓库内部链接使用相对路径，并通过链接检查确认目标存在。

## 非目标

本次工作不包括：

- 修改 Lean 定理、证明或项目依赖；
- 合并 Hardy--Littlewood、Pintz、VK 或其他研究分支；
- 撰写完整论文正文；
- 选择最终期刊或会议并完成投稿；
- 宣布历史优先权或新的非形式化数学定理。
