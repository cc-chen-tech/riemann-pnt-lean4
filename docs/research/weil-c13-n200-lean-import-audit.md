# `c=13,N=200` 区间 LDL 的 Lean 导入审计

## 已经存在的严格数据

高精度运行保存了：

- 双路线、双精度、转置感知的 source intersection；
- 49 个 source tiles 和 160801 个矩阵元；
- 7 个 streaming panels；
- 28 个区间 lower-factor blocks；
- 7 个区间 diagonal blocks；
- 401 个严格正的 pivot intervals；
- source、workspace 和 checkpoint 的内容哈希。

因此 Arb 运行本身具有完整的有限区间 LDL 工作数据，而不仅是 401 个
主元的屏幕输出。

## checkpoint verifier 的精确边界

当前标准库 checkpoint verifier 检查：

- canonical JSON 和 payload hash；
- source manifest 文件及 payload hash；
- 参数和精度一致性；
- pivot 区间语法及正号；
- workspace manifest 摘要。

它不重新执行：

- 区间三角求解；
- block Schur 更新；
- source matrix 与区间 `L D L^T` 的包含关系。

所以仅把 checkpoint 的 401 个正号复制进 Lean，不能推出原矩阵正定。

## Lean 闭合所需的定量证书

新增的 `IntervalLDLCoercivity.lean` 将问题压缩为三个严格有理量：

\[
D_{kk}\ge\delta>0,
\]

\[
\lVert x\rVert_2^2
 \le\kappa\lVert L^{\mathsf T}x\rVert_2^2,
\]

\[
\lvert A-C\rvert\ \text{的最大对称行和}\le\rho,
\qquad C=LDL^{\mathsf T}.
\]

只要

\[
\rho<\frac{\delta}{\kappa},
\]

Lean 即可推出区间中的原矩阵严格正定，并继续通过已经形式化的非负
cutoff-free archimedean tail。

## 下一生成器必须执行的算法

1. 从每个 factor interval 选择一个精确有理中心，组成单位下三角
   \(L_0\) 和正对角 \(D_0\)。
2. 取
   \(\delta=\min_k(D_0)_{kk}\)。
3. 精确求出 \(L_0^{-\mathsf T}\)，或给出其算子范数的严格有理上界
   \(\kappa\)。
4. 分块计算
   \(C=L_0D_0L_0^{\mathsf T}\)。
5. 对 source intersection 的每一行计算
   \(\sum_j\sup|A_{ij}-C_{ij}|\)，取最大值为 \(\rho\)。
6. 只有在精确比较
   \(\rho<\delta/\kappa\) 成立时才输出 positive artifact。
7. Artifact 必须绑定 source manifest、workspace manifest、factor blocks、
   checkpoint 和生成器的哈希。

## 规模风险

直接把 401 阶、约 2950 位十进制的全部 \(L_0\) 展开为 Lean 源码可能
产生非常大的文件和编译成本。更可行的发表路径是：

- 分块保存有理数据；
- 使用一个小型、形式化证明正确的 block checker；
- 每个 block 独立哈希；
- Lean 只组合 checker 的 soundness theorem 与通过结果。

在该 checker 完成前，当前状态应描述为：

> 严格 Arb 区间 LDL 证书及完整工作数据已经存在；Lean 已具备定量
> 传递定理，但尚未重放 401 阶分块算术。
