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
计数步骤与边界重数约定混在一起。上述实际 η 的有限计数特化现已完成
（见第 6–7 节）；矩形积分识别仍待完成，数学路线见第 8 节。

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
- 实际 η 的完整分量构造、有限相位极限、不交性、重数预算和 ζ 简单零点
  见证合并已全部完成（第 6–7 节）。后续仍需把实际矩形的半重数
  argument 变幅与 `Dseg` 联系起来。
- 式 (38)–(41)、长 mollifier 均方渐近式与真正的 `>2/5` 结论仍未完成。

English summary: the positive-jump variation is not the balanced component
variation. The old generic bridge deletion argument has an entire-function
counterexample. Strict interior levels give a correct componentwise lower
bound; the number of components is paid for by the total zero multiplicity
plus one. The half-weight boundary argument principle must be connected to
this balanced variation, not to the positive-jump endpoint difference.

## 6. 后续推进：实际分量端点与简单零点见证

`ConreyArgumentEndpoints` 已消除分量端点的极限假设。对 `g≠0` 的实际 η，
每个端点的解析阶都有限（非零端点对应零阶）。在左端点右侧、右端点
左侧分别取局部因子 logarithm，与任意既定分量 logarithm 比较；两者在
连通重叠区间上只差一个固定 `2kπi`，因此两个有限相位极限都属于原先
选定的同一个分量 logarithm。端点处 logarithm 的实部可以发散，这不
影响虚部极限；证明没有使用 logarithm 在零点端点的值。

`continuousLog_phase_increment_eq` 进一步证明 `B-A` 与 logarithm 分支
无关，关键是同一个 deck 常数同时加在两端，而非分别选择两个整数。
`ConreyComponentSimpleZeros` 已将任意有限不交零自由 η 分量族的见证点
转化为真实 ζ 简单零点；调用者不再需要提供 logarithm 或相位极限。

这三层分别通过当前定向构建与公理审计（端点 8714 jobs、分支不变性
2517 jobs、实际简单零点见证 8716 jobs；均 exit 0，仅三条标准公理）。

## 7. 全区间的有限分量构造

对内部零点有限集 `K⊂(U,T)`，以 `{U}∪K` 为左端点索引。每个 `u` 对应
`K∪{T}` 中严格大于 `u` 的最小元素 `b(u)`。相邻区间没有内部零点，
不同区间互不相交；任取 `t∈(U,T)\K`，取 `{U}∪K` 中小于 `t` 的最大
元素即可证明它被某个区间覆盖。空 `K` 时自然得到唯一分量 `(U,T)`。
此完整构造已在 `FiniteZeroComponents` 核验（910 jobs，exit 0）。

实际 η 使用 `K = {t∈(U,T):η(1/2+it)=0}`，而重数预算保留既有
`M = N0_eta((U,T])`。于是 `#K≤#zeros((U,T])≤M`，且 `U∉K`，分量数
恰为 `#K+1≤M+1`。若 `T` 是零点，从分量分割集中排除它但仍把其重数
留在 `M` 中只会减弱下界；若 `U` 是零点，已有单侧极限定理仍适用。
`exists_conreyDegreeOneEta_balanced_global_simpleZero_count` 现已将全部
组件组合；仅输入 `g≠0`、`0≤U`、`U<T`，即返回实际内部零点集合、全部
互补分量、同一组 logarithm 的指数恒等式与有限相位极限，以及有限 ζ
简单零点集 `S⊂(U,T)`，满足 `#S≥Dseg/π−M−1`。不再输入任何零点表、
分割、相位极限或分量数量假设。实际全局合约已通过定向构建（8718 jobs，
exit 0），公理依赖仅为 `propext`、`Classical.choice`、`Quot.sound`。
这闭合的是有限计数层，不是矩形 argument 公式或 `>2/5` 定理。

**角点边界：**上述计数允许端点是零点，不代表绕行矩形公式可原样用于
角点零点。后续式 (32) 的特化必须选取非零端点高度，或单独证明角点
修正；计数预算 `M` 与相应矩形定理里的边界重数必须逐项核对。

## 8. 下一步数学路线：主部正则化后的半重数公式

设 `f` 在闭矩形 `[σ,A]×[U,T]` 的邻域内全纯，`σ<A`、`U<T`，其余
三边及四个角点非零。将全部零点分为严格内部零点 `Koff` 与左边界
内部零点 `K0={σ+iτ:U<τ<T}`；重数记为 `mρ`。从 `f'/f` 中减去全部
零点主部，并在可去奇点处延拓，得到全纯余项

\[
 H(z)=\frac{f'(z)}{f(z)}-\sum_{\rho\in Koff\cup K0}\frac{m_\rho}{z-\rho}.
\]

令 `G=H+Σ_{ρ∈Koff}mρ/(z−ρ)`。它在整个矩形边界连续，只有严格内部
的极点。因此有限主部留数定理直接给出
`Im ∮ G = 2π Noff`，不必先构造绕行半圆及其半径极限。

在左边界的非零点，每个边界主部 `1/(σ+it−(σ+iτ))` 纯虚，所以
`q(t)=Re G(σ+it)=Re(f'/f)(σ+it)`。前者在整个 `[U,T]` 连续。对每个
零自由分量的既定相位 `θ`，须先用局部解析 logarithm 与固定 deck
常数证明 `θ'=q`，不能仅由 `θ` 连续而直接求导。再减去连续函数 `q`
的积分原函数，导数为零给出常数；取两侧已证明的有限相位极限，得到

\[
 B_j-A_j=\int_{a_j}^{b_j}q(t)\,dt,
 \qquad D_{\mathrm{seg}}=\int_U^T q(t)\,dt.
\]

最后一个等式使用完整有限分割；漏掉的有限零点集合测度为零。

对左边界零点 `ρ=σ+iτ`，记 `d=A−σ>0`、`r=τ−U>0`、`v=T−τ>0`。
正向的下、右、上三边对 `1/(z−ρ)` 的虚部积分依次为

\[
 \arctan(d/r),\quad
 \arctan(v/d)+\arctan(r/d),\quad
 \arctan(d/v).
\]

利用两次正数倒数的反正切恒等式，其和恰为 `π`。若 `E_f` 是 `f'/f`
在这三边上的虚部积分，左边界在正向矩形中向下行走，因而

\[
 2\pi N_{\mathrm{off}}=(E_f-\pi M)-D_{\mathrm{seg}}.
\]

**不可积性护栏：**只在没有零点的三边上拆开 `G=f'/f−Σ_{K0}mρ/(z−ρ)`。
左边界上的完整复值 `f'/f` 与各边界主部一般不可积，不能对它们错误地
使用积分线性性。左边界始终积分 `G`，或其连续实部迹 `q`。

这一路线已经过独立数学审查。相位导数、端点 FTC、有限积分重组及三边
精确 `π` 恒等式现已完成源码级 Lean 核验；正则化函数的构造、实际三边
积分拆分与内部留数公式的拼接，以及实际 η 矩形特化仍待完成。

## 9. 从连续 logarithm 到实际简单零点的积分下界

`hasDerivAt_continuousLog_of_exp_eq` 仅由 `ell` 连续、邻域内 `exp ell=gamma`
和 `gamma` 在指定点可微，推出 `ell'=gamma'/gamma`。具体地，在 `t0` 处
除以非零值 `gamma(t0)`，局部模型为
`log(gamma(t)/gamma(t0))+ell(t0)`。连续性使 `ell(t)-ell(t0)` 的虚部局部
落在 `(-π,π)`，所以 `log_exp` 保证此模型确实等于原先选定的分支。
这里没有要求原分支或原曲线避开主 logarithm 的割线。

`hasDerivAt_im_continuousLog_vertical` 随之给出向上竖线上的相位导数
`Re(f'/f)`；`continuousLog_phase_increment_eq_integral` 使用有限单侧相位
极限及连续迹 `q` 的可积性，给出 `B-A=∫q`，不需要完整 logarithm 在
零点端点收敛。`sum_intervalIntegral_eq_of_finite_complement` 用两两不交的
完整分量覆盖及有限集合零测度，将这些积分重组为整段积分。

`ConreyBalancedTraceCount` 将以上结果接入实际 η 的全局计数。其显式输入
除 `g≠0`、`0≤U<T` 外，仍包括：`q` 在 `[U,T]` 连续，且仅在 `(U,T)`
内 **η 非零的点**满足 `q=Re(η'/η)`。由此构造真实 ζ 简单零点集
`S⊂(U,T)`，满足

\[
 \#S\ge\frac1\pi\int_U^Tq(t)\,dt
   -N_{0,\eta}((U,T])-1.
\]

该定理不再输入任何分割、logarithm、相位端点或分量数量假设，但也没有
假装已经构造 `q`、证明半重数轮廓公式或得出真正的 `>2/5`。在 η 零点
处强行要求 `q=Re(η'/η)` 不是本接口的条件。

另外，`HorizontalArgument` 中的竖边核原函数和
`threeEdgeArgument_left_boundary_root_eq_pi` 已给出上述三边的精确 `π`
贡献，保留严格角点排除与不拆左边不可积复值积分的护栏。

初次核验因磁盘不足采用无产物的当前源码加合约模式，七条新定理及两项
水平积分回归均通过，仅使用三条标准公理。磁盘恢复后已补齐合约对新
模块的导入与默认 Lake 构建入口，正常独立模块构建成功（8728 jobs，
exit 0）；实际迹计数合约仅使用 `propext`、`Classical.choice` 和
`Quot.sound`。构建覆盖四个新合约、两个水平积分回归合约及实际全局
计数合约。全量 Python 测试同次核验为 546 passed；这不等于完成全库
Lean release-baseline 构建，也不等于完整 Conrey 定理。
