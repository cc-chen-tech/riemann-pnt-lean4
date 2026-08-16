# Weil centered principal sections

## 有限结果可以扩大到哪里

固定 \(c\) 时，cutoff-free 装配公式的矩阵元由整数指标 \(m,n\) 决定。
若该公式不额外依赖外层 cutoff \(N\)，则

\[
Q_M(c)
=E_{M,N}^{\mathsf T}Q_N(c)E_{M,N},
\qquad M\le N,
\]

其中 \(E_{M,N}\) 把指标

\[
-M,\ldots,M
\]

嵌入

\[
-N,\ldots,N
\]

的中央连续区块。

## Lean 实现

`CenteredPrincipalSection.lean` 已证明：

- 任意坐标注入都有精确的 0/1 basis matrix；
- 其转置 selector 是精确左逆；
- 半正定性向任意 principal section 传递；
- 严格正定性也向 principal section 传递；
- centered inclusion 保持 Fourier 整数坐标；
- 若矩阵族满足精确 centered nesting，则 \(Q_N\succ0\) 推出所有
  \(Q_M\succ0\)，其中 \(M\le N\)。

## 对 `c=13,N=200` 的含义

一旦把两条装配公式的 nesting identity 接到该定理，当前严格有限证书
将覆盖：

\[
c=13,\qquad 0\le M\le200.
\]

这比“一个 401 阶矩阵正定”更强，因为它同时认证 201 个 centered
finite sections。它仍然不是：

\[
\forall M,\ Q_M(13)\succeq0.
\]

## 尚需连接的公式事实

需要对 auxiliary 和 CCM 两路分别确认：

1. 每个矩阵元只依赖 \(c,m,n\)，不依赖外层 \(N\)；
2. `index_order=[-N,...,N]` 的中央子块正是 `[-M,...,M]`；
3. cutoff-free archimedean、prime 和 pole 三项采用同一索引约定；
4. interval intersection 和对称化不会改变该 nesting identity。

当前 Python 公式从代码结构上满足前两项，但尚未生成绑定 source
artifact 哈希的 nesting certificate，也尚未在 Lean 中实例化具体
`Q c N`。

## 声明边界

完成 nesting artifact 后可声明：

> 严格认证了固定 \(c=13\) 下全部 \(0\le M\le200\) 的 centered finite
> sections。

不能声明所有 \(M\)、无限维 Weil 正性或 RH。
