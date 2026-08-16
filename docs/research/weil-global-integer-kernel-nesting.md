# Weil 全局整数核与自动 nesting

## 正确的 cutoff 定义

固定参数 \(c\) 后，将完整解析矩阵元写成

\[
K_c:\mathbb Z\times\mathbb Z\longrightarrow\mathbb R.
\]

第 \(N\) 个有限矩阵应定义为

\[
Q_N(c)_{ij}=K_c(i-N,j-N),
\qquad 0\le i,j\le2N.
\]

在该定义中，\(N\) 只决定保留哪些整数 Fourier 指标，不参与已经存在
的矩阵元数值。

## Lean 定理

`IntegerKernelCutoff.lean` 证明：

\[
Q_M(c)
=E_{M,N}^{\mathsf T}Q_N(c)E_{M,N},
\qquad M\le N,
\]

其中 \(E_{M,N}\) 是精确 centered 0/1 嵌入。

因此，只要

\[
Q_N(c)\succ0,
\]

就自动得到

\[
Q_M(c)\succ0,\qquad0\le M\le N.
\]

不再需要额外假设 `hnested`。

## 对当前两条解析路线的接口

下一步不是再证明线性代数，而是分别定义或声明：

\[
K_c^{\mathrm{aux}}(m,n),
\qquad
K_c^{\mathrm{CCM}}(m,n),
\]

并证明两者等于同一个数学核 \(K_c(m,n)\)。

Python 装配中的 `N` 循环只负责枚举 `m,n=-N,...,N`。为了形成完整
proof-carrying 接口，artifact 还应绑定：

- 全局核公式版本；
- `c,m,n` 参数；
- route A 与 route B 的区间；
- 两区间严格重叠；
- cutoff 只控制索引范围的 schema 声明。

## 当前推进

结合 `c=13,N=200` finite closure，可以得到：

\[
Q_M(13)\succ0,\qquad0\le M\le200,
\]

前提是已认证矩阵被识别为某个全局整数核 \(K_{13}\) 的 `N=200`
cutoff。现有索引、source manifest 和解析代码都按这一结构组织，但
具体 digamma/prime/pole 公式尚未在 Lean 中定义。

## 仍然缺失

该 nesting 定理不提供：

- \(N>200\) 的正性；
- \(N\to\infty\) 的统一强制性；
- 无限 Weil 二次型的连续性与有限字典一致性；
- RH。
