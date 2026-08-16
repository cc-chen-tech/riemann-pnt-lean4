# Closed-but-unmerged PR 恢复审计台账（2026-08-16）

## 固定快照

- 仓库：`cc-chen-tech/riemann-pnt-lean4`
- 冻结时间：`2026-08-16T12:25:08.059Z`
- 固定 `origin/main`：`2b8849068aff00558ec32f17df36da53a9d883c0`
- Closed-but-unmerged：**245**
- Open PR：**0**
- 本文仅做只读恢复分类；未重新打开 PR，未修改作者分支，未启动 Lean/Lake。

## 判定口径

- **精确覆盖**：PR 唯一增量中的 production、Contract、AxiomAudit 与独立文档在固定 `main` 上 blob 一致；累计注册文件允许因后续追加而整体 blob 不同。
- **被后继覆盖**：唯一内容由后继 PR/固定载体保存。表中“当前 main”明确区分“已由替代集成进入 main”和“仅在待返工载体中保存”。
- **重复**：有独立 main-based 重做项完整承接有效内容。
- **独有但需返工**：仍有独有实质内容不在 `main`，且存在依赖、接口或范围 blocker。
- **明确拒绝**：原 PR 已失去可恢复价值，不能原样进入当前 `main`。

GitHub Closed 状态本身不作为覆盖证据。机械检查使用 GitHub 固定 PR commits/files、`refs/pull/*/head` 与固定 `main` tree；替代集成另以关闭评论中的 merged replacement PR 和 merge SHA 交叉核对。

## 分类汇总

| 分类 | 数量 |
|---|---:|
| 精确覆盖 | 81 |
| 被后继覆盖 | 155 |
| 重复 | 1 |
| 独有但需返工 | 7 |
| 明确拒绝 | 1 |
| **合计** | **245** |

注意：“被后继覆盖”中有一部分只是由 #188、#261 或 #277 继续保存，尚未进入 `main`；不得把该分类等同于 Merged。

## 恢复载体

| 优先级 | 载体 | 范围 | 当前 blocker | 恢复动作 |
|---:|---|---|---|---|
| 1 | #19 | Ford incomplete-moment 剩余层 | 聚合范围混杂、条件接口边界 | 从最新 main 拆成独立 source/Contract/AxiomAudit PR |
| 2 | #289 → #294 → #304 | occupancy → capacity decay → tail budget | 同名 theorem 类型冲突 | 先设计非冲突兼容接口，再顺序重放 |
| 3 | #261 | #199–#254 历史链 + actual cubic two-height 增量 | 35-production 非等价闭包、公开接口冲突 | 以当前 owner theorem 为基底，6–10 增量/批；需要新数学决定时停止 |
| 4 | #277 | dynamic-left 两侧界 | 依赖 #261 的 4 个 cubic 前置 | #261 兼容前置合入后重放 |
| 5 | #188 | #112–#187 后继链的未集成尾部 | 44-production 递归依赖、55 直接路径缺失 | 重新恢复依赖 DAG，按 main-based 小批审计 |

#2 不恢复原 PR；若仍需要流程文档，按当前 target inventory 重新撰写。#257 由独立 #258 重做，有效内容已经通过 #313 进入 `main`。

## 逐 PR 分类

| PR | 固定 head | base | 分类 | 当前 main | 证据摘要 |
|---:|---|---|---|---|---|
| [#2](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/2) | `1529f90ea7f4` | `main` | 明确拒绝 | 否（原样恢复无效） | 22-target 状态快照已陈旧，须按当前 main 重写 |
| [#14](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/14) | `ed6152a77bc9` | `main` | 被后继覆盖 | 是（替代集成） | 替代证据：#16, #17, #18 |
| [#19](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/19) | `1b991f80e1a5` | `main` | 独有但需返工 | 部分（#27 已合入） | Layer A 经 #27 合入；Ford incomplete-moment 等独有模块仍缺失 |
| [#48](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/48) | `8982941c417b` | `research/pintz-carlson-stack-01-foundation` | 被后继覆盖 | 是（替代集成） | 替代证据：#363, #364, #365, #366 |
| [#50](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/50) | `557ad645bb9e` | `research/pintz-carlson-stack-03-relative-pnt` | 被后继覆盖 | 是（替代集成） | 替代证据：#371, #374, #375 |
| [#52](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/52) | `2c436af6effa` | `research/pintz-carlson-stack-05-profile-optimization` | 精确覆盖 | 是 | 90 个唯一增量路径 blob 全部一致 |
| [#54](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/54) | `595b990a8aa8` | `research/pintz-carlson-stack-07-hybrid-transfer` | 被后继覆盖 | 是（替代集成） | 替代证据：#394 |
| [#56](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/56) | `fcf76ebcd78e` | `research/pintz-carlson-stack-09-finite-capture` | 被后继覆盖 | 是（替代集成） | 替代证据：#399, #400, #401, #402, #403, #404 |
| [#58](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/58) | `a682da79e21b` | `research/pintz-carlson-stack-11-zero-package` | 精确覆盖 | 是 | 116 个唯一增量路径 blob 全部一致 |
| [#60](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/60) | `07ad8980eaf9` | `research/pintz-carlson-stack-13-moving-carlson` | 精确覆盖 | 是 | 21 个唯一增量路径 blob 全部一致 |
| [#62](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/62) | `d0581e319261` | `research/pintz-carlson-stack-15-dynamic-counts` | 精确覆盖 | 是 | 15 个唯一增量路径 blob 全部一致 |
| [#64](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/64) | `f4be8067b829` | `research/pintz-carlson-stack-16-dyadic-cover` | 被后继覆盖 | 是（替代集成） | 替代证据：#423 |
| [#65](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/65) | `7851d9a2fabc` | `research/vk-edge-full-moving-energy` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；3 个累计注册文件后续演进 |
| [#66](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/66) | `7bd33948f1c5` | `research/vk-edge-initial-full-energy` | 精确覆盖 | 是 | 7 个实质路径 blob 一致；3 个累计注册文件后续演进 |
| [#67](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/67) | `b1bf5ff84f23` | `research/pintz-carlson-stack-18-classical-gap` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#69](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/69) | `495b379bd261` | `research/pintz-carlson-stack-19-classical-pnt` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#70](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/70) | `4cf8bd16db35` | `research/vk-edge-distinct-complement-witness` | 精确覆盖 | 是 | 10 个实质路径 blob 一致；1 个累计注册文件后续演进 |
| [#71](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/71) | `c7b4dd93a902` | `research/pintz-carlson-stack-20-classical-full-pnt` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#72](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/72) | `4f489a7d4cfc` | `research/pintz-carlson-stack-21-classical-quantitative-mass` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#73](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/73) | `0d106aa76ccd` | `research/pintz-carlson-stack-22-classical-quantitative-middle` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#74](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/74) | `bd9c81fbfd12` | `research/pintz-carlson-stack-23-classical-quantitative-positive-tail` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#75](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/75) | `313471a94f75` | `research/pintz-carlson-stack-24-classical-quantitative-full-zero-tail` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#76](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/76) | `9f1f082e615d` | `research/pintz-carlson-stack-25-classical-quantitative-full-pnt` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#77](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/77) | `91fa5cb0f377` | `research/pintz-carlson-stack-26-classical-closed-form-full-pnt` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#78](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/78) | `d456563d5633` | `research/pintz-carlson-stack-27-balanced-truncation-rate` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#79](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/79) | `811e2c9d442b` | `research/pintz-carlson-stack-28-balanced-quantitative-mass` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#80](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/80) | `3c103039b5fa` | `research/pintz-carlson-stack-29-balanced-closed-form-full-pnt` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#81](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/81) | `940407104a63` | `research/pintz-carlson-stack-30-theta-sharp-carlson-rate` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#82](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/82) | `dd132b03560a` | `research/pintz-carlson-stack-31-theta-sharp-full-pnt` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#83](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/83) | `7e21dbcf2678` | `research/pintz-carlson-stack-32-half-sharp-carlson-rate` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#84](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/84) | `bae6b7e54280` | `research/pintz-carlson-stack-33-half-sharp-full-pnt` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#85](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/85) | `13ca5b525fe3` | `research/pintz-carlson-stack-34-half-sharp-target-amplitude-barrier` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#86](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/86) | `ccabd1bb4cab` | `research/pintz-carlson-stack-35-target-amplitude-two-height-exponent` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#87](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/87) | `9f63ad6554f7` | `research/pintz-carlson-stack-36-actual-target-amplitude-two-height-strip` | 被后继覆盖 | 是（替代集成） | 替代证据：#428 |
| [#88](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/88) | `6aa4332e297b` | `research/pintz-carlson-stack-37-actual-target-amplitude-low-layer-two-height` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#89](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/89) | `e45baf0b25e2` | `research/pintz-carlson-stack-38-actual-target-amplitude-positive-tail-composition` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#90](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/90) | `129ca68a818a` | `research/pintz-carlson-stack-39-actual-target-amplitude-full-tail-conjugation` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#91](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/91) | `63312871891b` | `research/pintz-carlson-stack-40-actual-explicit-formula-unified-target-transfer` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#92](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/92) | `f76c3c4941bd` | `research/pintz-carlson-stack-41-selected-height-two-height-full-tail` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#93](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/93) | `7ab8c88f5451` | `research/pintz-carlson-stack-42-selected-height-unified-explicit-formula-transfer` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#94](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/94) | `63af4900bca7` | `research/pintz-carlson-stack-43-automatic-good-height-natural-unified-transfer` | 被后继覆盖 | 是（替代集成） | 替代证据：#429 |
| [#95](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/95) | `b2c6b8c3a15a` | `research/pintz-carlson-stack-44-joint-two-height-parameter-feasibility` | 被后继覆盖 | 是（替代集成） | 替代证据：#429 |
| [#96](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/96) | `18fe90a01038` | `research/pintz-carlson-stack-45-automatic-joint-parameter-unified-transfer` | 被后继覆盖 | 是（替代集成） | 替代证据：#429 |
| [#97](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/97) | `ea4c9e05346b` | `research/pintz-carlson-stack-46-real-ordinate-closed-automatic-transfer` | 被后继覆盖 | 是（替代集成） | 替代证据：#430 |
| [#98](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/98) | `050b5e8b8b18` | `research/pintz-carlson-stack-47-prescribed-cap-joint-feasibility` | 被后继覆盖 | 是（替代集成） | 替代证据：#430 |
| [#99](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/99) | `ee563d50fde8` | `research/pintz-carlson-stack-48-global-real-part-bound-unified-transfer` | 被后继覆盖 | 是（替代集成） | 替代证据：#430 |
| [#100](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/100) | `f6ba335602d7` | `research/pintz-carlson-stack-49-automatic-reverse-cluster-exclusion` | 被后继覆盖 | 是（替代集成） | 替代证据：#430 |
| [#101](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/101) | `0378e44ef10f` | `research/pintz-carlson-stack-50-automatic-reverse-finite-height-zero-free` | 被后继覆盖 | 是（替代集成） | 替代证据：#430 |
| [#102](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/102) | `4d4dc83557b6` | `research/pintz-carlson-stack-51-quantitative-reverse-finite-height-zero-free` | 被后继覆盖 | 是（替代集成） | 替代证据：#431 |
| [#103](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/103) | `01150a77e356` | `research/pintz-carlson-stack-52-optimal-common-outer-height-exponent` | 被后继覆盖 | 是（替代集成） | 替代证据：#431 |
| [#104](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/104) | `c5a63115e35c` | `research/pintz-carlson-stack-53-optimal-prescribed-cap-outer-height` | 被后继覆盖 | 是（替代集成） | 替代证据：#431 |
| [#105](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/105) | `9cdd68f4e9e9` | `research/pintz-carlson-stack-54-near-optimal-truncation-parameters` | 被后继覆盖 | 是（替代集成） | 替代证据：#431 |
| [#106](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/106) | `9e7f07b620ec` | `research/pintz-carlson-stack-55-near-optimal-actual-unified-transfer` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#107](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/107) | `0f89d1774888` | `research/pintz-carlson-stack-56-midpoint-sigma-strict-improvement` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#108](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/108) | `73efd0e4e1a4` | `research/pintz-carlson-stack-57-exact-sigma-optimizer` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#109](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/109) | `a0626301845c` | `research/pintz-carlson-stack-58-unique-sigma-optimizer` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#110](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/110) | `701387aa6094` | `research/pintz-carlson-stack-59-global-optimal-truncation-parameters` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#111](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/111) | `563183f34b62` | `research/pintz-carlson-stack-60-global-optimal-actual-unified-transfer` | 精确覆盖 | 是 | 5 个唯一增量路径 blob 全部一致 |
| [#112](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/112) | `a4673b23aa64` | `research/pintz-carlson-stack-61-global-optimal-quantitative-reverse-zero-free` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#113](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/113) | `651ae53a3dbb` | `research/pintz-carlson-stack-62-improved-global-cap-threshold` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#114](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/114) | `1ae79bcd1b57` | `research/pintz-carlson-stack-63-improved-cap-automatic-actual-transfer` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#115](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/115) | `568516257b0b` | `research/pintz-carlson-stack-64-improved-cap-automatic-reverse-zero-free` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#116](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/116) | `bc1762cc96b7` | `research/pintz-carlson-stack-65-explicit-improved-cap-gain` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#117](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/117) | `03af525366dc` | `research/vk-edge-proportional-window-transfer` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；3 个累计注册文件后续演进 |
| [#118](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/118) | `d7e84fa6fe7c` | `research/pintz-carlson-stack-66-cubic-cap-deficit-asymptotic` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#119](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/119) | `ecb769d81e8f` | `research/exceptional-zero-detect-or-count-sharp` | 精确覆盖 | 是 | 21 个实质路径 blob 一致；1 个累计注册文件后续演进 |
| [#120](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/120) | `330a39f99a63` | `research/pintz-carlson-stack-67-improved-cap-threshold-strict-mono` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#121](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/121) | `059cfd3bcf21` | `research/pintz-carlson-stack-68-unique-optimal-target-exponent` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#122](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/122) | `a0493e512022` | `research/pintz-carlson-stack-69-canonical-strict-target-exponent` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#123](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/123) | `9b4b805d8a73` | `research/pintz-carlson-stack-70-theta-only-actual-unified-transfer` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#124](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/124) | `43abb5b84e39` | `research/pintz-carlson-stack-71-theta-only-quantitative-reverse-zero-free` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#125](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/125) | `4be1fcc2c44e` | `research/pintz-carlson-stack-72-theta-only-target-asymptotic` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#126](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/126) | `79b9b9e7317d` | `research/pintz-carlson-stack-73-cubic-strict-target-exponent` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#127](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/127) | `65a1ccfeab38` | `research/pintz-carlson-stack-74-cubic-strict-theta-only-actual-transfer` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#128](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/128) | `750bda8bc2fd` | `research/pintz-carlson-stack-75-cubic-strict-theta-only-reverse-zero-free` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#129](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/129) | `fcc2add66dc8` | `research/pintz-carlson-stack-76-positive-outside-cluster-cap-transfer` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#130](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/130) | `a7081442f023` | `research/pintz-carlson-stack-77-nonvacuous-outside-cluster-reverse-zero-free` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#131](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/131) | `f0e19602cc9a` | `research/pintz-carlson-stack-78-moving-right-edge-exceptional-cluster` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#132](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/132) | `d46653ff25d3` | `research/pintz-carlson-stack-79-moving-cluster-complement-majorant` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#133](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/133) | `6ee3a8db31ca` | `research/pintz-carlson-stack-80-moving-right-edge-unified-transfer` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#134](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/134) | `970950f23348` | `research/pintz-carlson-stack-81-moving-right-edge-seed-stability` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#135](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/135) | `724575289311` | `main` | 被后继覆盖 | 是（替代集成） | 替代证据：#338–#354 |
| [#136](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/136) | `2c45714fa6ee` | `research/exceptional-zero-directed-growth` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；3 个累计注册文件后续演进 |
| [#137](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/137) | `ea8d559ec710` | `research/pintz-carlson-stack-82-moving-right-edge-signed-seed-stability` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#138](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/138) | `6ee5ccb4abcd` | `research/pintz-carlson-stack-83-moving-extension-absolute-mass` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#139](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/139) | `0febc2dca557` | `research/pintz-carlson-stack-84-moving-extension-shrinking-gap` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#140](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/140) | `a3df824fbd52` | `research/pintz-carlson-stack-85-fixed-geometry-shrinking-gap-obstruction` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#141](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/141) | `3dcd30197b00` | `research/vk-edge-right-higher-sharp-blocker` | 被后继覆盖 | 是（替代集成） | 替代证据：#283 |
| [#142](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/142) | `7061ee428894` | `research/pintz-carlson-stack-86-carlson-pointwise-gap-extension-absolute-mass` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#143](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/143) | `4c179a1bb1de` | `research/pintz-carlson-stack-87-boundary-capture-extension-absolute-mass` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#144](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/144) | `a14652d979ec` | `research/pintz-carlson-stack-88-finite-seed-target-line-selector` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#145](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/145) | `cba6b056230a` | `research/pintz-carlson-stack-89-boundary-captured-signed-pnt-transfer` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#146](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/146) | `948dfec3cf68` | `research/pintz-carlson-stack-90-target-line-capture-budget-sufficiency` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#147](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/147) | `87b94ac619cd` | `research/pintz-carlson-stack-91-seed-witness-half-threshold-signed-pnt` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#148](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/148) | `d491721c89c6` | `research/pintz-carlson-stack-92-zero-package-sign-alternative` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#149](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/149) | `283cb1fb9587` | `research/pintz-carlson-stack-93-seed-witness-sign-alternative-pnt` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#150](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/150) | `e1865e1942a7` | `research/pintz-carlson-stack-94-actual-zero-package-pnt-sign-alternative` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#151](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/151) | `dea1a243df94` | `research/pintz-carlson-stack-95-actual-zero-package-unnormalized-sign-alternative` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#152](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/152) | `01662d6599f5` | `research/pintz-carlson-stack-96-quantitative-zero-package-energy` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#153](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/153) | `50a69fbbe9e2` | `research/pintz-carlson-stack-97-finite-height-package-boundary-capture` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#154](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/154) | `bd048aa8a9f4` | `research/pintz-carlson-stack-98-automatic-package-energy-boundary-budget` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#155](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/155) | `dcae2b0d24ea` | `research/pintz-carlson-stack-99-automatic-seed-to-unnormalized-pnt-sign` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#156](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/156) | `df04a81b665c` | `research/pintz-carlson-stack-100-variable-boundary-exponent-transfer` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#157](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/157) | `9c1b7b13e7e3` | `research/pintz-carlson-stack-101-variable-boundary-visible-carlson-tail` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#158](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/158) | `befc60fde8ec` | `research/pintz-carlson-stack-102-monotone-boundary-absorption-gap` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#159](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/159) | `49423d9ff03c` | `research/pintz-carlson-stack-103-variable-boundary-amplitude-domination` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#160](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/160) | `40987ce46d9b` | `research/pintz-carlson-stack-104-variable-boundary-visible-residual-assembly` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#161](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/161) | `e152626088c1` | `research/pintz-carlson-stack-105-variable-boundary-full-tail-budget` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#162](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/162) | `2e8383841903` | `research/pintz-carlson-stack-106-variable-boundary-real-tail-decay` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#163](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/163) | `003b8806fdbf` | `research/pintz-carlson-stack-107-variable-boundary-positive-tail-index-bridge` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#164](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/164) | `698a7fd22816` | `research/pintz-carlson-stack-108-variable-boundary-low-strip-decay` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#165](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/165) | `270a3152083e` | `research/pintz-carlson-stack-109-variable-boundary-end-to-end-sign-transfer` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#166](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/166) | `f7f22a66ee09` | `research/pintz-carlson-stack-110-monotone-end-to-end-sign-transfer` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#167](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/167) | `86a68a0e5bb5` | `research/pintz-carlson-stack-111-monotone-end-to-end-signed-omega` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#168](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/168) | `50abd0244389` | `research/pintz-carlson-stack-112-monotone-moving-upper-signed-omega-unified` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#169](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/169) | `04d08aa5d660` | `research/pintz-carlson-stack-113-canonical-good-height-moving-unified` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#170](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/170) | `043e674bb1b5` | `research/pintz-carlson-stack-114-geometric-moving-right-edge-unified` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#171](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/171) | `511a57e14321` | `research/pintz-carlson-stack-115-natural-running-maximum-boundary` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#172](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/172) | `8cb3f7098d70` | `research/pintz-carlson-stack-116-sigma-only-running-boundary` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#173](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/173) | `6d64a0987ba8` | `research/pintz-carlson-stack-117-zero-free-gap-upper-decay` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#174](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/174) | `db919af83ba0` | `research/pintz-carlson-stack-118-zero-free-envelope-running-boundary` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#175](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/175) | `02e270630e8b` | `research/pintz-carlson-stack-119-certified-good-height-optimizer` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#176](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/176) | `987271cc0885` | `research/pintz-carlson-stack-120-finite-switching-remainder-envelope` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#177](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/177) | `93cc3b04f289` | `research/pintz-carlson-stack-121-optimized-height-unified-transfer` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#178](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/178) | `c2cb902d5168` | `research/pintz-carlson-stack-122-certified-cost-cover` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#179](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/179) | `1686accffdf1` | `research/pintz-carlson-stack-123-actual-good-height-rate-grid` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#180](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/180) | `5be6e6a5536d` | `research/pintz-carlson-stack-124-finite-rate-remainder-decay` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#181](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/181) | `6f1a4043f00b` | `research/pintz-carlson-stack-125-full-budget-rate-optimizer` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#182](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/182) | `e222aabe92ec` | `research/pintz-carlson-stack-126-balanced-rate-grid-approximation` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#183](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/183) | `acd679287af0` | `research/pintz-carlson-stack-127-strict-margin-grid-full-budget-transfer` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#184](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/184) | `240560fa3f5c` | `research/pintz-carlson-stack-128-actual-strict-margin-finite-zero-majorant` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#185](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/185) | `fbf82540f248` | `research/pintz-carlson-stack-129-actual-strict-margin-grid-full-pnt-envelope` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#186](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/186) | `e74e14328b16` | `research/pintz-carlson-stack-130-automatic-optimal-strict-margin-pnt-grid` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#187](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/187) | `985bf3f547f7` | `research/pintz-carlson-stack-131-automatic-optimal-height-carlson-bridge` | 被后继覆盖 | 否（载体 #188 待返工） | 提交历史由后继链保存至 #188；尚未声称进入 main |
| [#188](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/188) | `c96fac859d53` | `research/pintz-carlson-stack-132-automatic-actual-grid-dyadic-carlson-full-pnt` | 独有但需返工 | 否 | 55 个直接增量路径缺失；递归为 44 个非等价 production |
| [#199](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/199) | `4640a6612947` | `research/pintz-carlson-stack-143-canonical-polynomial-running-boundary` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#200](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/200) | `13f384ff03ad` | `research/pintz-carlson-stack-144-canonical-polynomial-sigma-only` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#201](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/201) | `bd8ec20aef01` | `research/pintz-carlson-stack-145-optimal-polynomial-height-window` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#202](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/202) | `8f3e4792b6fa` | `research/pintz-carlson-stack-146-optimal-polynomial-sigma-only-transfer` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#203](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/203) | `41a7cd87d9a3` | `research/pintz-carlson-stack-147-weighted-optimal-polynomial-height-window` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#204](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/204) | `c10d3d943252` | `research/pintz-carlson-stack-148-carlson-weighted-optimal-polynomial-window` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#205](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/205) | `aeecf80fe6b5` | `research/pintz-carlson-stack-149-joint-slope-full-transfer-obstruction` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#206](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/206) | `e198a970aa39` | `research/pintz-carlson-stack-150-reciprocal-low-layer` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#207](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/207) | `cabf57476b06` | `research/pintz-carlson-stack-151-reciprocal-dynamic-transfer` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#208](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/208) | `6d38ec4f38d6` | `research/pintz-carlson-stack-152-reciprocal-variable-boundary-transfer` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#209](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/209) | `863afde9824b` | `research/pintz-carlson-stack-153-reciprocal-sigma-only-running-boundary` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#210](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/210) | `947c9edc68d1` | `research/pintz-carlson-stack-154-reciprocal-optimal-contour-height` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#211](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/211) | `6942c8acbbd3` | `research/pintz-carlson-stack-155-near-optimal-sigma-only-transfer` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#212](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/212) | `d826c2eab7c6` | `research/pintz-carlson-stack-156-prescribed-height-sigma-only-transfer` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#213](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/213) | `b4b4bba3c874` | `research/pintz-carlson-stack-157-near-optimal-prescribed-height-anchor` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#214](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/214) | `a971c947ed00` | `research/pintz-carlson-stack-158-fixed-cluster-reciprocal-low-layer` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#215](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/215) | `d12cfef878b3` | `research/pintz-carlson-stack-159-fixed-cluster-reciprocal-boundary-mass` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#216](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/216) | `d5828970809b` | `research/pintz-carlson-stack-160-fixed-cluster-reciprocal-full-residual` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#217](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/217) | `d7f044f2a733` | `research/pintz-carlson-stack-161-actual-zero-package-reciprocal-sign-alternative` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#218](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/218) | `08bea8997bc2` | `research/pintz-carlson-stack-162-automatic-reciprocal-sign-alternative` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#219](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/219) | `4c04e01caed5` | `research/pintz-carlson-stack-163-automatic-reciprocal-unnormalized-omega` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#220](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/220) | `9f7007aa29c4` | `research/pintz-carlson-stack-164-attained-global-right-edge-omega` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#221](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/221) | `68cc442c3b31` | `research/pintz-carlson-stack-165-attained-right-edge-real-closed-seed` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#222](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/222) | `9b383bb47069` | `research/pintz-carlson-stack-166-attained-right-edge-real-closed-omega` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#223](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/223) | `4064e0f6f3de` | `research/pintz-carlson-stack-167-actual-package-moving-right-edge-omega` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#224](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/224) | `a878d3198c27` | `research/pintz-carlson-stack-168-reciprocal-moving-complement` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#225](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/225) | `844a2bee7157` | `research/pintz-carlson-stack-169-reciprocal-moving-extension-omega` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#226](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/226) | `7fb9701b843c` | `research/pintz-carlson-stack-170-half-threshold-moving-omega` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#227](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/227) | `3e0dbd23a614` | `research/pintz-carlson-stack-171-running-boundary-reciprocal-sign-alternative` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#228](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/228) | `9e2e0b730d12` | `research/pintz-carlson-stack-172-moving-window-l2-handoff` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#229](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/229) | `20f5a658ea3e` | `research/pintz-carlson-stack-173-near-optimal-height-l2-unified` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#230](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/230) | `033aa2690c1c` | `research/pintz-carlson-stack-174-height-normalized-contour-obstruction` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#231](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/231) | `27c5bde48d29` | `research/pintz-carlson-stack-175-kernel-order-criterion` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#232](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/232) | `70d7cbca2041` | `research/pintz-carlson-stack-176-quadratic-kernel-certificate-transfer` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#233](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/233) | `54f0356b47df` | `research/pintz-carlson-stack-177-quadratic-kernel-unnormalized-transfer` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#234](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/234) | `87ec7a15f88d` | `research/pintz-carlson-stack-178-third-order-perron-kernel` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#235](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/235) | `1b7e2668f27b` | `research/pintz-carlson-stack-179-cubic-kernel-second-difference` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#236](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/236) | `faef560b13a3` | `research/pintz-carlson-stack-180-cubic-factor-local-lower-bound` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#237](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/237) | `f7d8562a6db9` | `research/pintz-carlson-stack-181-third-order-perron-inversion` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#238](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/238) | `05f9ef31b1e4` | `research/pintz-carlson-stack-182-third-order-perron-truncation` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#239](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/239) | `c829201f36a8` | `research/pintz-carlson-stack-183-von-mangoldt-second-riesz-perron` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#240](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/240) | `82105a1571b8` | `research/pintz-carlson-stack-184-complete-cubic-logderiv-perron` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#241](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/241) | `d4206cbc5f1e` | `research/pintz-carlson-stack-185-third-order-explicit-residues` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#242](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/242) | `222244f3693a` | `research/pintz-carlson-stack-186-cubic-explicit-formula` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#243](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/243) | `542627798580` | `research/pintz-carlson-stack-187-quadratic-hinge-second-difference` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#244](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/244) | `ff88481bef0d` | `research/pintz-carlson-stack-188-second-riesz-psi-sandwich` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#245](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/245) | `4f807d518157` | `research/pintz-carlson-stack-189-cubic-second-difference-transfer` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#246](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/246) | `338160d770a2` | `research/pintz-carlson-stack-190-common-pole-cubic-triple` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#247](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/247) | `ef5b99ba5cda` | `research/pintz-carlson-stack-191-cubic-residue-second-difference-kernel` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#248](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/248) | `119eb6cd7449` | `research/pintz-carlson-stack-192-cubic-kernel-factorization` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#249](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/249) | `4e5cd682f41e` | `research/pintz-carlson-stack-193-cubic-multiplier-near-one` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#250](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/250) | `50caf0884b2d` | `research/pintz-carlson-stack-194-cubic-contour-kernel-factorization` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#251](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/251) | `35f4df6df2b9` | `research/pintz-carlson-stack-195-automatic-cubic-contour-integrability` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#252](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/252) | `d642e28f52cf` | `research/pintz-carlson-stack-196-normalized-desmoothed-explicit-formula` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#253](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/253) | `f85eebe46720` | `research/pintz-carlson-stack-197-actual-desmoothed-contour-edge-budget` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#254](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/254) | `c15b773691ab` | `research/pintz-carlson-stack-198-inner-zero-free-horizontal-budget` | 被后继覆盖 | 否（载体 #261 待返工） | 提交历史由后继链保存至 #261；尚未声称进入 main |
| [#255](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/255) | `6c0c573c0599` | `research/vk-edge-prime-side-detector` | 被后继覆盖 | 是（替代集成） | 替代证据：#284 |
| [#257](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/257) | `239e03c8c2f4` | `research/pintz-carlson-stack-199-good-height-desmoothed-central-contour` | 重复 | 是（#258/#313） | 独立 #258 重做；有效 production 经 #313 进入 main |
| [#258](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/258) | `c589476c8690` | `research/pintz-carlson-dyadic-shell-mass-base` | 被后继覆盖 | 是（替代集成） | 替代证据：#313 |
| [#259](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/259) | `87330be6adae` | `research/vk-edge-gaussian-bucket-schur` | 精确覆盖 | 是 | 3 个唯一增量路径 blob 全部一致 |
| [#261](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/261) | `4211d549fcbf` | `research/pintz-carlson-actual-cubic-two-height-l2-tail-base` | 独有但需返工 | 否 | 63 个路径缺失；35-production 闭包与当前公开接口冲突 |
| [#262](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/262) | `d84fb68b96bf` | `codex/half-isolated-dyadic-gram-schur` | 精确覆盖 | 是 | 3 个唯一增量路径 blob 全部一致 |
| [#263](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/263) | `18b5381a9804` | `research/vk-edge-right-higher-sharp-blocker` | 精确覆盖 | 是 | 9 个实质路径 blob 一致；3 个累计注册文件后续演进 |
| [#267](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/267) | `1aa03b3f3063` | `research/vk-edge-sharp-low-height-energy` | 精确覆盖 | 是 | 9 个实质路径 blob 一致；3 个累计注册文件后续演进 |
| [#268](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/268) | `5e6485096064` | `codex/exceptional-zero-dyadic-direct-l2` | 精确覆盖 | 是 | 5 个实质路径 blob 一致；1 个累计注册文件后续演进 |
| [#269](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/269) | `44b4f45a5377` | `codex/vk-edge-q-power-detector-design` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；3 个累计注册文件后续演进 |
| [#271](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/271) | `b89b6b833f46` | `codex/half-isolated-dyadic-capacity-integration-base` | 精确覆盖 | 是 | 3 个唯一增量路径 blob 全部一致 |
| [#272](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/272) | `90e14c90869e` | `research/pintz-carlson-actual-cubic-two-height-l2-tail` | 被后继覆盖 | 否（载体 #277 待返工） | 提交历史由后继链保存至 #277；尚未声称进入 main |
| [#273](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/273) | `46044f7c9f2e` | `research/vk-edge-desmoothed-left-derivative` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；3 个累计注册文件后续演进 |
| [#274](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/274) | `be130196e84e` | `codex/half-isolated-dyadic-capacity-bridge` | 被后继覆盖 | 是（替代集成） | 替代证据：closing evidence comment |
| [#275](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/275) | `f16d34019d57` | `research/vk-edge-desmoothed-left-oscillatory` | 被后继覆盖 | 否（载体 #277 待返工） | 提交历史由后继链保存至 #277；尚未声称进入 main |
| [#276](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/276) | `a6b919538011` | `codex/half-isolated-zeta-full-dyadic-capacity-bridge` | 被后继覆盖 | 是（替代集成） | 替代证据：closing evidence comment |
| [#277](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/277) | `2302bfa17362` | `research/vk-edge-desmoothed-left-amplitude` | 独有但需返工 | 否 | focused 因 4 个 cubic 前置缺失而失败；依赖 #261 兼容移植 |
| [#278](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/278) | `b5f5e043023b` | `codex/exceptional-zero-target-dyadic-gram-schur` | 精确覆盖 | 是 | 8 个实质路径 blob 一致；1 个累计注册文件后续演进 |
| [#281](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/281) | `4ce67e6a60bc` | `codex/half-isolated-zeta-excluded-gram-capacity-bridge` | 精确覆盖 | 是 | 3 个唯一增量路径 blob 全部一致 |
| [#289](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/289) | `3a2bc9560058` | `codex/exceptional-zero-target-dyadic-gram-schur` | 独有但需返工 | 否 | 同名 theorem 类型冲突；需 main-based 非冲突接口 |
| [#290](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/290) | `05afbe6c28d0` | `codex/exceptional-zero-dyadic-carlson-summation` | 精确覆盖 | 是 | 3 个唯一增量路径 blob 全部一致 |
| [#294](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/294) | `94a80236d198` | `codex/exceptional-zero-target-dyadic-occupancy` | 独有但需返工 | 否 | 独有 capacity-decay 增量依赖 #289 兼容接口 |
| [#304](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/304) | `e2cbfbf4d800` | `codex/exceptional-zero-target-dyadic-capacity-decay` | 独有但需返工 | 否 | 独有 tail-budget 增量依赖 #289→#294 |
| [#433](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/433) | `3141a303b958` | `main` | 精确覆盖 | 是 | 3 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#434](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/434) | `0e1645c656dc` | `codex/actual-cubic-two-height-l2-tail-20260811` | 精确覆盖 | 是 | 15 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#435](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/435) | `f3fcc315ac98` | `codex/actual-cubic-carlson-moving-tail-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#436](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/436) | `0a8fb4c87e13` | `codex/actual-cubic-carlson-quantitative-moving-tail-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#437](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/437) | `7ebc4f6667cf` | `codex/actual-cubic-carlson-diagonal-tail-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#438](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/438) | `b4f5e2955aea` | `codex/actual-cubic-carlson-smoothed-high-low-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#439](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/439) | `84a0a716f1a4` | `codex/actual-third-order-explicit-formula-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#440](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/440) | `a97bb63bf5d2` | `codex/actual-third-order-zeta-contour-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#441](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/441) | `5492d3dc4379` | `codex/actual-third-order-lseries-bridge-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#442](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/442) | `198f92d405d1` | `codex/actual-third-order-contour-remainder-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#443](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/443) | `704a3958fb3c` | `codex/actual-third-order-dynamic-height-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#444](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/444) | `4280efb9707b` | `codex/actual-third-order-high-to-low-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#445](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/445) | `7e1817096577` | `codex/actual-third-order-zero-pole-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#446](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/446) | `b0c6f030297d` | `codex/actual-third-order-zero-pole-rectangle-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#447](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/447) | `6fc253b0ca27` | `codex/actual-third-order-zero-pole-contour-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#448](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/448) | `b031bb0bac02` | `codex/actual-third-order-zero-pole-lseries-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#449](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/449) | `92cdc6bac8f7` | `codex/actual-third-order-zero-residue-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#450](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/450) | `d02bbc5317dd` | `codex/actual-third-order-zero-residue-unique-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#451](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/451) | `b85452167de0` | `codex/actual-third-order-zero-residue-rectangle-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#452](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/452) | `a3e0eff1d034` | `codex/actual-third-order-zero-residue-contour-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#453](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/453) | `8152edee22b3` | `codex/actual-third-order-dynamic-height-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#454](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/454) | `88029c1a8024` | `codex/separated-third-order-contour-carlson-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#455](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/455) | `30705d67f969` | `codex/third-order-dynamic-perron-target-20260811` | 精确覆盖 | 是 | 4 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#456](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/456) | `725b2a757107` | `codex/third-order-actual-synchronized-formula-integration-base-20260811` | 精确覆盖 | 是 | 3 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#457](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/457) | `4ef5d2e98d29` | `codex/third-order-actual-synchronized-formula-20260811` | 精确覆盖 | 是 | 3 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#458](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/458) | `439e6732340b` | `codex/third-order-actual-l2-synchronized-transfer-20260811` | 精确覆盖 | 是 | 3 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#459](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/459) | `12873ebceac1` | `codex/third-order-actual-low-layer-dyadic-capacity-20260812` | 精确覆盖 | 是 | 3 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#460](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/460) | `1e9676239521` | `codex/third-order-actual-low-layer-gaussian-l2-adapter-20260812` | 精确覆盖 | 是 | 3 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#461](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/461) | `b1cb3f3030eb` | `codex/third-order-actual-low-layer-summed-gaussian-l2-20260812` | 精确覆盖 | 是 | 3 个实质路径 blob 一致；2 个累计注册文件后续演进 |
| [#466](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/466) | `9c0f0b8bc2b0` | `main` | 被后继覆盖 | 是（替代集成） | 替代证据：#471 |
| [#467](https://github.com/cc-chen-tech/riemann-pnt-lean4/pull/467) | `932ae8cfe3bd` | `codex/amplification-assembly-layer` | 精确覆盖 | 是 | 2 个唯一增量路径 blob 全部一致 |

## 后续约束

1. 只对“独有但需返工”的恢复载体创建 main-based 替代 PR；原 Closed PR 不必为了状态美观而重开。
2. 任一恢复批次若需要改 theorem statement、增添数学假设、改变常数或 Occupancy，立即停止并单独申请数学范围授权。
3. 每个增量运行 focused source/Contract/AxiomAudit；每批只运行一次 allowlist 与完整 baseline。
4. 替代 PR 合入后，在本台账记录 replacement PR、merge SHA、固定 head 与验证证据，再把对应条目升级为“精确覆盖”或“被后继覆盖且已进入 main”。
5. 本台账不声称真实 zeta 实例化、Carlson 矛盾、`Re rho > 2/3` 排除或 RH。
