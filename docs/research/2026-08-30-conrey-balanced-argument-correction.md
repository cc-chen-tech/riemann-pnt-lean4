# Conrey 式 (41)：区分分段变幅与含跳跃变幅

先说结论：8 月 29 日设计中，把零点处的正向 `mπ` 跳跃加入总变幅，
然后只减一次零点重数来计数非零实部 crossing，这个一般性论证不成立。
正确的可用计数引理针对**不含跳跃的分段 argument 变幅**。
本修正不否定已经证明的有限集合、局部解析因子化、连续 logarithm 或
抽象闭曲线定理；它撤回将这些定理直接拼成实际 η 计数证明的解释。

## 1. 两个不同的量

设端点 `U<T` 上 η 非零，内部零点为 `τ₁<⋯<τᵣ`，重数为正整数
`m₁,…,mᵣ`，令 `M=Σmⱼ`。在 `r+1` 个开放互补分量上选择连续
argument `θⱼ`，其左右单侧极限为 `Aⱼ,Bⱼ`。定义

\[
 D_{\mathrm{seg}}=\sum_{j=0}^{r}(B_j-A_j).
\]

每个分量的分支加一个常数 `2kπ` 不改变这个差。若进一步对齐分支，使
每个零点右极限等于左极限加 `mⱼπ`，则这个**含正向跳跃**的总变幅满足

\[
 D_+=D_{\mathrm{seg}}+\pi M.
\tag{1}
\]

这两个量不能共用一个未经说明的 `Δarg` 符号。

## 2. 原文与边界半重数

[Conrey 1983, §4, p. 58](https://aimath.org/~kaur/publications/3.pdf)
明确写出零点处右 argument 为左 argument 加 `nπ`；扫描页已逐字核对。
但 [Conrey 1989, p. 6, 式 (32)](https://aimath.org/~kaur/publications/24.pdf)
使用的 `N*` 把临界线上的零点按半重数计入。这要求重新核对变幅约定，
不能把 1983 年的正跳跃约定直接移植进去。

令 `Noff` 为矩形内严格位于临界线右侧的零点重数，`M` 为左边界零点重数。
假定函数在矩形的邻域内全纯，另外三边及角点非零，且左边界仅有这些
孤立零点。把向上走的左边界在零点附近向右绕开，会在绕行半径趋于零时
给 argument 增加 `mπ`，并把这些边界零点排除在矩形内部；有限半径时，
非零解析因子还有一个趋于零的变幅项。若其余三边的正向变幅为 `E`，
对绕行矩形应用 argument principle 再取极限，给出

\[
 E-(D_{\mathrm{seg}}+\pi M)=2\pi N_{\mathrm{off}},
\qquad
 D_{\mathrm{seg}}=E-2\pi(N_{\mathrm{off}}+M/2).
\tag{2}
\]

所以半重数公式自然对应 `Dseg`；`D+` 对应的是严格内部零点计数。
将 (2) 对实际 `V₁`、`η=HV₁` 的矩形作完整 Lean 特化，仍是后续任务。
式 (32) 的半重数与式 (41) 的计数下界，在采用 `Dseg` 时相容到一个显式
`O(1)` 端点损失：本笔记证明的通用下界是 `Dseg/π-M-1`，并非逐字的
`Dseg/π-M`。

## 3. 对旧一般性论证的反例

取整函数 `F(s)=1+exp(2(s-1/2))`，在线上取

\[
 \gamma(t)=1+e^{2it}=2\cos t\,e^{it},\qquad 0\le t\le n\pi.
\]

它恰有 `n` 个简单零点，端点均为 2，而且

\[
 \Re\gamma(t)=2\cos^2t=0\ \Longrightarrow\ \gamma(t)=0.
\]

因此非零实部 crossing 的点数为 0。每个零自由分量的 argument 导数为 1，
故 `Dseg=nπ`；加上 `n` 个正 `π` 跳跃后 `D+=2nπ`。旧目标会错误地要求

\[
 0\ge D_+/\pi-M-1=n-1,
\]

在 `n≥2` 时矛盾。这反驳的是旧的**一般性拼接引理**，并非 Conrey 定理。

## 4. 正确的开放分量计数

对一个开放零自由分量 `(a,b)`，设连续 logarithm 的相位单侧极限为 `A,B`。
只取**严格位于** `(A,B)` 的半奇整数相位 `π/2+kπ`。由带单侧极限的
中值定理，每个这样的相位在 `(a,b)` 内取到，而且指数恒等式保证该点
确实满足 `Re η=0` 且 `η≠0`。不同相位对应不同点。

令 `x=(A-π/2)/π`、`y=(B-π/2)/π`，这样的整数集合为

\[
 K^\circ(A,B)=\{k\in\mathbb Z:\lfloor x\rfloor<k<\lceil y\rceil\}.
\]

即使端点恰好落在格点上，或者 `B≤A`，也有

\[
 \#K^\circ(A,B)\ge (B-A)/\pi-1.
\tag{3}
\]

对互不相交的 `r+1` 个分量求和，再使用每个 `mⱼ≥1`，得到

\[
 \#\{t\in(U,T):\Re\eta(1/2+it)=0,\ \eta(1/2+it)\ne0\}
 \ge D_{\mathrm{seg}}/\pi-(r+1)
 \ge D_{\mathrm{seg}}/\pi-M-1.
\tag{4}
\]

这里没有重复支付：`M` 支付的正是分量端点的取整损失，而非额外减去已经
包含在总变幅中的正跳跃。也不需要假设相位单调；下降分量在 (3) 的右侧
只贡献一个较弱的非正下界。

### 4.1 实际 η 的拼接可以不做递归相位对齐

将端点 `U,T` 插入已排序的内部零点表，得到 `r+1` 个互不相交的开放
区间。每个区间任取一个连续 logarithm `ℓⱼ` 即可，无须先让相邻分支
满足正向跳跃约定。在零点附近，局部因子化给出两侧 logarithm 模型；
同一非零曲线的两个连续 logarithm 在连通重叠区间上相差固定
`2kπi`，因而局部模型的有限相位极限转移给 `ℓⱼ`。非零端点的处理
则来自端点邻域的连续 logarithm。这样各个 `Aⱼ,Bⱼ` 均已确定，且
任意分支选择都给出相同的 `Bⱼ-Aⱼ`。

计数时先在每个区间为不同严格相位选择不同实际点，再取这些有限点集
的并；区间互不相交保证点数相加。这一步只依赖各分量自身，不依赖
跨零点的全局相位参数。最后单独用绕行矩形积分识别 `Dseg`，避免把
计数步骤与边界重数约定混在一起。此段是后续实际 η 特化的数学施工图，
不是已经完成的 Lean 定理。

## 5. 精确的形式化边界

- 局部相位端点必须与**同一个** `ℓ` 的两侧 `exp = η` 恒等式一起返回。
  仅有“存在连续 `ℓ` 与两个极限”不足以把相位与 η 联系起来。加强后的
  `exists_conreyDegreeOneEta_local_argument_endpoint_limits` 及实际区间
  回归合约已通过定向 Lake 构建（8713 jobs，exit 0），公理依赖仅为
  `propext`、`Classical.choice`、`Quot.sound`。
- `MathlibAux/ArgumentCrossingOpen.lean` 已证明严格格点计数、单侧极限的
  内部 crossing、不同相位到不同实际点的单射，以及互不相交分量的有限
  点集求和。返回的每一点均在 `Ioo a b` 内，满足 `Re g=0` 且 `g≠0`。
- 上述定理连同旧 crossing 回归合约已通过定向 Lake 构建（2518 jobs，
  exit 0）；新定理公理依赖仅为 `propext`、`Classical.choice`、`Quot.sound`。
- 严格格点计数和 `r+1≤M+1` 预算是有限计数步骤，不是式 (32) 的证明。
- 后续仍需对实际排序零点表构造分量及单侧极限，证明分量互不相交并合并
  crossing 点（通用有限集合求和已完成，实际 η 特化未完成），再把实际
  矩形的半重数 argument 变幅与 `Dseg` 相等。
- 式 (38)–(41)、长 mollifier 均方渐近式与真正的 `>2/5` 结论仍未完成。

English summary: the positive-jump variation is not the balanced component
variation. The old generic bridge deletion argument has an entire-function
counterexample. Strict interior levels give a correct componentwise lower
bound; the number of components is paid for by the total zero multiplicity
plus one. The half-weight boundary argument principle must be connected to
this balanced variation, not to the positive-jump endpoint difference.
