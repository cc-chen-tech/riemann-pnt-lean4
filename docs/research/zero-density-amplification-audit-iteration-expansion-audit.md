# zero-density amplification: iteration expansion counter-model audit (phase 5)

本阶段补齐“局部邻接证书是否产生 `q^n` 个不同窗口/零点”的组合层：

## 1) 分层模型

新增

- `iterativeWindowLayer`：由根 `roots` 与父-子映射 `children` 按递归定义。
- `IterativeWindowLayerCertificate`：记录 `depth`, `roots`, `children`, `q`, 根非空、每层最小分支数、层间子集对齐不交。

核心结论：

- `iterativeWindowLayer_qpow_lowerBound`：在 `n ≤ depth` 下
  
  `q(T)^n ≤ |iterativeWindowLayer roots children n T|`
  
  可按层递推证明；`n=0` 由根非空给出，`n+1` 由
  `card_biUnion` 与 `sum` 下界得到。

## 2) 反例（局部最小度不够）

定义共享邻居模型：

- `roots = Finset.univ`（两点），
- 每个父节点都只连接 `{0,1}`。

则所有层仍是大小为 2，故

- `2^2 ≤ |层2|` 在每个 `T` 都失败，
- 说明“每点有 2 个邻居”并不蕴含指数增长。

## 3) 轻量可审计替代条件

- `iterativeWindowLayer_qpow_lowerBound_with_subcertificate`：若可以审计到显式**无重叠子层证书**，并且在目标深度该子层包含于主层，则子证书的 `q^n` 下界可直接迁移到主层。

这是对“层间有重叠/共享邻居”场景的可操作补救：先审计一组可去重子枝条，再用主层包含性继承增长界。

## 4) 连接 Carlson

- `iterativeWindowLayer_to_carlson_contradiction`：把上述层级下界转为现有
  `iterativeBranch_qpow_carlson_contradiction` 的 `hbranch` 先决条件，
  直接得到 Carlson 反证。
