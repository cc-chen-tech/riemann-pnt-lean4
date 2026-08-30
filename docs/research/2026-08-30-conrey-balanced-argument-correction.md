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
将 (2) 对实际 η 的矩形作 Lean 特化现已完成（第 12–13 节）；转为
`V₁`、`η=HV₁` 的完整重数比较和定量边界仍是后续任务。
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
（见第 6–7 节）；第 8 节的矩形积分路线现已在第 12–13 节实现。

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
  见证合并已全部完成（第 6–7 节）。实际矩形的半重数 argument 公式
  也已在显式三边非零条件下接入 `Dseg` 的积分下界（第 12–13 节）。
- 式 (38)–(41)、长 mollifier 均方渐近式与真正的 `>2/5` 结论仍未完成。

English summary: the positive-jump variation is not the balanced component
variation. The old generic bridge deletion argument has an entire-function
counterexample. Strict interior levels give a correct componentwise lower
bound; the number of components is paid for by the total zero multiplicity
plus one. Sections 12–13 connect the half-weight boundary argument identity
to this balanced variation, not to the positive-jump endpoint difference.

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

## 8. 已实现的数学路线：主部正则化后的半重数公式

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
精确 `π` 恒等式现已完成 Lean 核验；给定精确零点表的正则化函数与内部
留数公式也已构造。通用三边积分拆分与留数式的拼接现已完成，实际 η
匹配矩形零点表也已构造（第 12 节）；定量边界估计仍须另行证明。

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

## 10. 两笔边界重数预算如何消去

再次逐页核对 [Conrey 1989，第 6–7 页](https://aimath.org/~kaur/publications/24.pdf)
的式 (32)、(37)、(40)–(41)：式 (32) 的星号计数使用边界半重数，
而式 (37) 的乘积零点计数使用完整重数。不能将后者也替换成半重数。

在第 8 节的同一矩形、同一端点约定下，记
`Nfull = Noff + M`、`Nhalf = Noff + M/2`。一旦半重数轮廓恒等式接通，
已有有限计数式的右侧恰为

\[
 \frac{D_{\mathrm{seg}}}{\pi}-M-1
 =\frac{E_f}{\pi}-2N_{\mathrm{off}}-2M-1
 =\frac{E_f}{\pi}-2N_{\mathrm{full}}-1.
\]

所以两次出现的 `M` 并非重复扣错，也不留下需要另行证明为低阶量的
残项。若在同一零点区域已经证明 `Nfull(f)≤Nfull(f B)`，可直接推出
`#S≥E_f/π−2Nfull(f B)−1`。这也给出一个较短的后续拼接方式：保留
半重数作为轮廓的精确解释，计数接口则直接用完整重数单调性。

这一段是数学恒等式及剩余接口核对，不宣称轮廓拼接或均方渐近式已经
形式化；轮廓的后续实现见第 12–13 节。端点根的排除、`η=H V1` 的非零
因子、矩形到半带的零点区域一致性，以及误差项的定量界仍须由各自
真实定理承担。

## 11. 正则化构造的实现与下一处连接

`MathlibAux.LeftRegularizedLogDeriv` 按第 8 节构造同一个 `G`，返回五项
相互绑定的结论：在矩形去除严格内部零点后解析；在真实非零点等于
`logDeriv f` 减去左边界主部；闭左边界实部迹连续；此迹在真实非零点
等于 `Re(logDeriv f)`；完整边界积分恰为内部重数和乘 `2πi`。

零点集合及解析阶仍是精确输入，但函数 `G` 和连续迹不是输入。位置
条件推出两零点集合不交，并排除其余三边及角点的零点。当前实现已经
通过独立只读审查；正常独立构建 `lake build Test.LeftRegularizedLogDerivContract`
成功（8706 jobs，exit 0），五项联结合约仅使用三条标准公理
`propext`、`Classical.choice`、`Quot.sound`。同次 Python 回归 546 passed。

`threeEdgeArgument_left_principalParts_eq_pi_mul_sum` 进一步将单根 `π`
贡献提升为完整有限主部的 `πM`：逐项证明其余三边连续和可积，再交换
有限和与积分，保留每项自然数权重。空集合和零权重均允许；实际解析
重数的联结由调用方的零点表承担。三边方向始终是下边加右边减上边。
该合约及两个水平积分回归独立构建通过（2677 jobs，exit 0），公理仍
仅三条标准公理，独立只读审查未发现问题。

这一步的后续实现对其余三边应用 `G` 的真实非零点恒等式，减去已证明
的 `πM`，并用同一个 `G` 的左边迹和内部留数式重组，见第 12 节。左边
不作奇异复值积分的分拆。

实际 η 特化要使用与轮廓完全一致的零点表；若通过选取附近的良好
高度来排除角点根，选择过程中应固定原来的 η 参数（包括 `L`），不能
未经误差分析随新高度更改 `L=log T`。端点调整和最终所有大 `T` 的
渐近结论须另行连接。

## 12. 完整半重数公式与实际矩形零点表

`MathlibAux.exists_regularized_trace_half_boundary_argument` 已把第 8 节
全部通用部件连接为同一个存在性结论：构造闭区间上连续的 `q`，证明
其在真实非零点等于 `Re(f'/f)`，并精确满足

\[
 E_f-\int_U^Tq(t)\,dt
 =2\pi\left(\sum_{\rho\in Koff}m_\rho+
                    \tfrac12\sum_{\rho\in K0}m_\rho\right).
\]

三边集合单独证明无零性与可积性，只有这些边上使用积分减法。第四边
使用整个正则化函数 `G`；没有给奇异 `f'/f` 假造可积性。正常独立构建
`Test.HalfBoundaryArgumentPrincipleContract` 成功（8709 jobs，exit 0），
合约公理依赖仅 `propext`、`Classical.choice`、`Quot.sound`。

`exists_conreyDegreeOneEta_rectangle_zero_finset` 进一步从实际 η 的
紧矩形 divisor 支集构造 **全部闭矩形零点**，不是只列出临界线零点。
假设 `g≠0`、`A≥1/2`、`U≥0` 及下左端点 η 非零，左边界过滤集的自然数
解析重数和恰等于既有 `conreyEtaCriticalZeroMultiplicityMassBetween`。
该结果允许 `A=1/2`、空矩形或上端点零点：`T` 两边都保留，而 `U` 由
实际非零假设排除。它没有单独声称这些退化情形适用于轮廓公式。
其独立合约构建成功（8713 jobs，exit 0），仍仅使用三条标准公理。

独立只读审查核对了同一个 `G`、四边方向、半重数系数、完整零点表、
临界点映射单射及端点预算，未发现重要问题。后续轮廓应用仍须明确
`A>1/2`、`U<T` 以及整个上下、右三边的 **η 非零** 条件。

## 13. 实际有限轮廓计数闭合，完整比例仍开放

`exists_conreyDegreeOneEta_simpleZero_finset_of_three_edges` 现仅要求
`g≠0`、`A>1/2`、`0≤U<T`，以及同一闭矩形的整个上下、右三边上 η 非零。
它在证明内部构造全闭矩形实际 η 零点表 `K`，以实部是否等于 `1/2`
分成不交的 `Koff` 与 `K0`；所有严格边界条件和下端点非零性均从同一个
三边假设推出。第 12 节构造的 `q` 随即接入实际 ζ 简单零点积分计数。

由精确的左边界重数恒等式，两笔重数损失合并为

\[
 \#S\ge\frac{E_\eta}{\pi}
        -2\sum_{\rho\in K}\operatorname{ord}_\rho\eta-1.
\]

这里 `S⊂(U,T)` 的每个点均满足真实 `riemannZeta(1/2+it)=0` 且解析阶恰为
1。定理没有输入零点表、正则化迹、连续 logarithm、相位端点或分割。
独立只读审查未发现重要问题；包含三个新合约、实际迹/全局计数和边界
根回归的定向构建成功（8735 jobs，exit 0），新端点仅依赖三条标准公理。

**本节完成时的下一条缺口（现已在第 14–15 节接通）：**把同一 η 矩形的完整重数转入实际 `V1*B` 的完整
重数上界。已有 `η=H V1` 的解析阶等式及 `V1` 到 `V1*B` 的点态重数
单调性可以复用；已有半带 **半重数** 比较不能直接代替此完整重数预算。
若矩形跨过 `Re s=1`，阶等式应使用 `Re s>0, s≠1` 的版本，而非仅适用
于 `Re s<1` 的自然数阶辅助定理。零点表中的点满足 `Im ρ>U≥0`，
因此不是 `s=1`；这不宣称当 `U=0` 时整个闭矩形避开了 `s=1`。

之后仍须衔接固定参数的良好高度、三边积分定量估计、全体大高度的
传递，以及长 mollifier 均方渐近式/DI 输入。没有把这些假设删掉，也
没有将有限轮廓计数宣称为真正的 `>2/5` 定理。

English update: the actual finite contour count is now kernel-checked under
explicit nonvanishing on the other three edges. It constructs all eta zeros,
the regularized trace and genuine zeta simple-zero witnesses, with loss twice
the full rectangle multiplicity. Quantitative estimates and the genuine
Conrey proportion theorem remain open.

## 14. 同一区间的完整 mollified 重数预算

`ConreyMollifiedFullCount` 现已证明从 η 矩形零点到实际 `V1*B` 的完整
重数比较。参数 `g,g0,g1,L,Y,sigma0,P` 及上下高度在整个证明中保持不变。
若 `K` 中每一点满足 `1/2≤Re ρ≤A`、`U<Im ρ≤T`、`η(ρ)=0`，则

\[
 \sum_{\rho\in K}\operatorname{ord}_\rho\eta
 \le N_{\rm full}(V_1B;\,1/2\le\Re\rho\le A,\ U<\Im\rho\le T)
 \le N_{\rm full}(V_1B;\,\Re\rho\ge1/2,\ U<\Im\rho\le T).
\]

输入要求 `g≠0`、`Y≥2`、`P(1)=1` 和第一条不等式中的 `U≥0`。根的
正高度推出 `ρ≠1`，所以使用 `Re ρ>0, ρ≠1` 的 η/V₁ 解析阶等式，
再取自然数阶；随后逐点使用乘积重数单调性和有限集合包含。没有将
整个闭矩形错误地假设为避开 `s=1`，也没有限制 `A<1`。

两个新计数定义都直接对实际产品零点的自然数解析阶求和，临界线根
**不除以二**，且下端点过滤始终是 `U<Im ρ`。产品允许新增边界根；
增加完整重数只使最终下界更弱。半带扩张使用实际零点 membership，
无需把原矩形右边界放在某个人为规范截断以内。

两项精确合约先因目标定理缺失失败，再通过独立正常构建（8786 jobs，
exit 0），均仅依赖三条标准公理。实际有限轮廓的拼接已在第 15 节从
整条底边 η 非零推出 `K` 的严格下高度，没有仅用下左角的非零性。

## 15. 直接连接实际规范简单零点数

`ConreyMollifiedContourCount` 将第 13–14 节连接为

\[
 N_{\rm simple}(T)\ge \frac{E_\eta(A;U,T)}\pi
 -2N_{\rm full}(V_1B;\,1/2\le\Re\rho\le A,\ U<\Im\rho\le T)-1.
\]

左侧直接是 `positiveCriticalLineSimpleZeroCount T`，不是任意定义的
占位计数。将第 13 节构造的 `S` 通过 `t↦1/2+it` 单射嵌入规范集合，
逐项传递 ζ 为零、正高度、临界线条件和自然数解析阶恰为 1。
整条底边 η 非零排除 `Im ρ=U`，使 η 的闭矩形根恰好进入 `(U,T]`
产品预算。三边方向仍为下加右减上，且所有 η 与 mollifier 参数固定。

有界版和半带版都已实现；后者仅利用完整重数随区域扩张单调增加，
得到较弱但仍有效的下界。两者均显式保留 `g≠0`、`Y≥2`、`P(1)=1`、
`A>1/2`、`0≤U<T` 及整个上下、右三边 η 非零条件。

四个定向合约的组合构建成功（8811 jobs，exit 0），新端点仅依赖
`propext`、`Classical.choice`、`Quot.sound`。独立只读审查未发现实际计数
嵌入、完整重数方向或端点遗漏。Python 回归 546 passed。新端点的
111 个本地模块 import 闭包无 Zeta23，外部 import 根仅 Mathlib。

## 16. 下一步数学接口：同一有界矩形的 Littlewood 预算

定量主线优先使用第 15 节的**有界版**。已有
`exists_conreyEquation37SelectedHeights_boundaryRemainder_le` 的右边界为
`A=2 log L`，而半带定义采用另一个存在性定理选出的规范远右边界；
不能把两者等同，也不能把前者的定量误差直接搬到后者。

以下调用定量选择器时，产品特指 `conreyHorizontalJensenProduct Y R L`：
`g=49/100`、`g0=0`、`g1=51/50`、`P=conreyExplicitP`。其条件为
`2≤Y≤exp L`、`0<R≤6/5`、`L≥40000`，并保留选择器给出的固定常数
`Creg,Cmass≥1` 及阈值 `Creg,Cmass≤exp L`。选择器本身还允许 `R=0`，
但下面除以 `d` 的步骤要求 `R>0`。这些条件保证 `sigma0=1/2-R/L>0`。

记外部尺度 `X=exp L`，在选取 `U∈[A+1,A+2]` 和 `T∈[X-1,X]` 期间固定
上述全部产品参数，尤其不把 `L` 改成 `log T`。令

\[
 F=V_1B,\quad d=1/2-\sigma_0=R/L,\quad
 I=\int_U^T\log|F(\sigma_0+it)|\,dt.
\]

据此得到的实际零点特化目标如下（现已在第 17 节实现）：

\[
 2\pi d\,N_{\rm full}(F;\,1/2\le\Re\rho\le A,\ U<\Im\rho\le T)
 \le I+\mathrm{Rem}.
\]

具体构造不是再输入一个“合适的零点表”假设：从整个
`[sigma0,A]×[U,T]` 的紧 divisor 构造全部实际产品零点，并证明过滤
`Re ρ≥1/2` 后的完整自然数阶和正是第 14 节有界计数。上下、右边的
产品非零性排除这些边界的根；左边界允许零点。可从有限零点实部集
选出 `sigma0+epsilon_n<1/2` 的零自由竖线并令其趋于 `sigma0`，使用
已证 `littlewoodRectangle_mass_le_logNormEdges_of_leftBoundaryZeros`。
产品非零也能推出同位置 η 非零，但须明确使用 `η=H V1` 的非零因子。

完整余项保持原定义

\[
 \mathrm{Rem}=-\int_U^T\log|F(A+it)|\,dt
 +H(U)-H(T)+(A-\sigma_0)\int_U^T\Re(F'/F)(A+it)\,dt,
\]

其中 `H(t)=∫_{sigma0}^A (sigma-sigma0) Im(F'/F)(sigma+it) dsigma`。
在上述显式产品及参数范围内，同一高度选择器已提供

\[
 |\mathrm{Rem}|\le 507X/L+2.2\cdot10^{12}L^7+(A-\sigma_0)\pi.
\]

此数值余项界不宣称适用于一般 `g,g0,g1,P`。只给出右边的 argument
界不能省去右边的对数模长积分。
将已证 Littlewood 特化代入已证计数后，精确归一化为

\[
 N_{\rm simple}(T)\ge E_\eta/\pi
 -\frac{I+\mathrm{Rem}}{\pi d}-1.
\]

若再证明 `2I≤(T-U) log C`，第二项即为
`((T-U) log C+2 Rem)/(2 pi d)`。按 `X L/(2 pi)` 归一化，余项代价为
`2 Rem/(R X)`；上述界足以使该代价趋零，**不需要**要求整个余项
为 `o(X/L)`。若均方只得到 `∫_0^X |F|²≤CX`，Jensen 应先保留
`(T-U) log(CX/(T-U))`，再证明 `(T-U)/X→1`，不能提前删除长度差。

还须注意现有 `ConreyLittlewoodMeanSquare` 要求左边整段非零，而
实际左边允许有限零点，不能直接删掉现有定理的非零假设。下一步采用
更直接的指数 Jensen：先以实际有限零点表排除零测集，记 `f=|F|²`，
则 `exp(log f)=f` 几乎处处；已证对数可积性给出 `log f` 可积，连续性
给出 `f` 可积。在整个实轴上对凸函数 `exp` 应用 Jensen，得到
`exp(avg(log f))≤avg(f)`，同时自动推出右侧均值严格正，再取 logarithm。
由 `log |F|²=2 log |F|` 得到精确长度因子 `T-U`。这样无须另加
`epsilon` 正则化及控制收敛层；该连接的 Lean 特化现已在第 19 节完成。

上述数学设计中的实际 Littlewood 特化现已由第 17 节完成；它没有
同时给出 `E_eta` 的定量主项、同一高度上的无权 η argument 控制、长
`theta=571/1000<4/7` mollifier 均方渐近式及 DI 输入仍需真实证明。
已有 `C_explicit<exp(18/25)` 的数值证书并不提供上述均方估计。最终
须再用规范零点数的单调性与 Riemann–von Mangoldt 渐近式将结论传给
每个充分大的外部高度 X，才得到真正的 `>2/5`。

## 17. 实际产品的 Littlewood 上界及规范计数组合

`ConreyMollifiedRectangleZeros` 直接对实际 `F=V1*B` 在正高度紧矩形上
取 divisor 支集，构造全部闭矩形零点 `K`。`sigma0>0`、`U>0` 保证
矩形避开 `s=1`，每个点处的产品解析阶均由 `g≠0`、`Y≥2`、`P(1)=1`
证明为有限值。先证明有限 ENat 阶，再转自然数，没有将无限阶截为零。

仅在整条底边 F 非零的条件下，过滤 `Re ρ≥1/2` 后的完整重数和就
精确等于 `conreyMollifiedV1BoundedFullZeroCountBetween`。零点表层允许
`sigma0=1/2`、上边界零点和空／退化矩形；其 `(U,T]` 约定与既有计数
完全一致。该合约独立构建通过（8787 jobs，exit 0）。

`LittlewoodFiniteZeroTable` 从有限零点表构造一个正间隔 `d0`，使
`x_n=x0+d0/(n+1)` 始终处于 `x0<x_n<critical`，避开所有零点实部，且
趋于 `x0`。左边界根不妨碍构造，而所有 `Re ρ≥critical` 的零点始终
保留。连续范数在紧矩形上的上界再经 `log r≤r` 给出所需对数上界；
没有在零点处使用 logarithm 的连续性。它将无零逼近序列和对数上界
从调用方假设中消去，接入已证的左边界极限定理。合约独立构建通过
（8711 jobs，exit 0）。

`ConreyMollifiedLittlewood` 随后在
`g≠0`、`Y≥2`、`P(1)=1`、`0<sigma0<1/2<A`、`0<U<T` 以及大矩形
上下、右三边实际 F 非零的条件下，证明

\[
 2\pi(1/2-\sigma_0)N_{\rm full}(F;\,1/2\le\Re\rho\le A,\ U<\Im\rho\le T)
 \le \int_U^T\log|F(\sigma_0+it)|\,dt+\mathrm{Rem}.
\]

该结论没有输入零点表、解析阶、无零竖线序列、统一对数上界或左边界
非零性。余项是既有 `littlewoodRectangleNonleftRemainder` 全部原项，
包括右边的对数模长积分及 argument 积分，没有删项或更换边界。

大矩形的三边 F 非零经 `η=H V1` 推出小矩形三边 η 非零。由第 15 节
已证规范计数，进一步得到

\[
 N_{\rm simple}(T)\ge\frac{E_\eta(A;U,T)}\pi
 -\frac{\int_U^T\log|F(\sigma_0+it)|\,dt+\mathrm{Rem}}
        {\pi(1/2-\sigma_0)}-1.
\]

两条实际端点合约独立构建通过（8816 jobs，exit 0）。本节四条新定理
均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。独立只读审查未
发现边界、完整重数、逼近序列或系数方向问题。最终端点的 119 个本地
模块 import 闭包没有 Zeta23，外部 import 根仅 Mathlib。

三个新合约与既有规范计数、有限轮廓回归的最终组合构建也通过
（8820 jobs，exit 0）；全量 Python 回归 546 passed。这里的 Lean
构建是定向验证，不声称重新完成全库 release-baseline 构建。

现有显式参数高度选择器与完整余项界已在第 18 节接入同一组
`L,Y,R,U,T`。左侧 logarithm 的 Jensen 连接也已在第 19 节允许有限零点；
`E_eta` 的定量主项、长 mollifier 均方渐近式及 DI 输入、最终正比例
渐近推导仍未完成。本节是实际有限轮廓／Littlewood 计数链的闭合，
不是完整 Conrey `>2/5`。

## 18. 同参数良好高度与外部尺度的实际计数下界

`ConreySelectedHeightCount` 将第 17 节直接接入定量高度选择器。
先逐项展开定义，证明 `conreyEquation37BoundaryRemainder` 恰好等于
实际产品的完整 `littlewoodRectangleNonleftRemainder`；只交换复数乘法
`it=ti`，两个右边积分均未删除。

选择器中的 `Creg,Cmass≥1` 为绝对常数。取
`L0=40000+Creg+Cmass`，则 `L≥L0` 推出 `L≥40000` 以及
`Creg,Cmass≤L≤exp L`；该阈值独立于 `Y,R`。对于每一组
`2≤Y≤exp L`、`0<R≤6/5`、`L≥L0`，定理实际返回

\[
 U\in[A+1,A+2],\qquad T\in[X-1,X],\qquad U<T,
 \quad A=2\log L,\ X=e^L.
\]

上下两边非零由同一产品的选择器给出。右边使用已有全局实部下界
`Re F(A+it)≥3/10`，其 `1≤t≤X` 条件由返回的高度区间推出。
因此上下、右三边非零不再由调用方提供；左边仍允许零点。
`R/L≤3/100000` 和 `R/L>0` 同时保证 `0<sigma0<1/2`。

记 `B(L)=507X/L+2.2·10^12 L^7+(A-sigma0)π`。由
`Rem≤|Rem|≤B(L)`，除以正数 `πR/L` 后正确减弱第 17 节下界，
再仅对规范计数使用 `N_simple(T)≤N_simple(X)`，得到

\[
 N_{\rm simple}(X)\ge\frac{E_\eta(A;U,T)}\pi
 -\frac{\int_U^T\log|F(\sigma_0+it)|\,dt+B(L)}{\pi R/L}-1.
\]

所有 η、产品、积分和余项始终用相同的 `L,Y,R,U,T`；没有将 `L`
换成 `log T`，也没有将积分区间偷偷扩大到 `[0,X]`。两项精确合约
先因缺少目标定理失败，后通过正常定向 Lake 构建（exit 0）。独立
只读审查未发现边界、参数、阈值或不等号方向问题；Python 全量回归
546 passed，目标清单与依赖链检查通过。新端点的 156 个本地模块
import 闭包无 Zeta23，外部根仅 Mathlib。

新合约与第 17 节三个合约、既有规范计数及有限轮廓合约的最终组合
构建通过（8858 jobs，exit 0）。两条新定理直接打印的公理依赖均仅为
`propext`、`Classical.choice`、`Quot.sound`；生产模块和合约均加入默认
Lake roots。没有声称全库 Lean release-baseline 或 GitHub CI 已通过。

本节消去的是非左三边无零假设，并完成外部尺度的有限计数连接。
左侧实际均方估计和 `E_eta` 的定量主项并没有由此得到；有限零点的
指数 Jensen 连接已在第 19 节完成，长 mollifier/DI 分析仍须完成，
不能据此宣布 40%。

## 19. 允许有限左边界零点的实际均方计数形式

`MathlibAux.LogMeanSquare` 新增几乎处处正值版本。对于 `a<b`，若
`f` 与 `log f` 都可积且 `f>0` 几乎处处，则在有限非零区间测度上
应用凸指数函数的 Jensen。不在零点处使用 `exp(log f)=f`；该等式
只通过 AE 恒等式用于可积性和积分替换。所得
`exp(avg(log f))≤avg(f)` 同时给出 `∫f>0` 和精确长度归一化的对数
均值上界。既有处处非零版本不变，并保留原合约回归。

`ConreyLittlewoodMeanSquare` 将其用于 `f=|F|²`：连续性给出平方范数
可积，输入对数模长可积性结合 `log |F|²=2log |F|` 给出对数平方
范数可积。系数 2 和区间长度没有通过渐近等价删除。

`ConreyMollifiedMeanSquare` 随后对实际产品构造这些输入。在
`g≠0,Y≥2,P(1)=1,0<sigma0≤1/2<A,0<U<T` 与整条底边 F 非零下，
正实部、正高度保证矩形避开极点；实际完整零点表 `K` 投影成有限
异常高度 `Im(K)`，所以竖线上的 F 几乎处处非零。解析函数的已有
竖线对数可积性定理允许孤立零点，从而得到

\[
 M=\int_U^T|F(\sigma_0+it)|^2\,dt>0,\qquad
 2\int_U^T\log|F(\sigma_0+it)|\,dt
 \le (T-U)\log\frac{M}{T-U}.
\]

调用者不再提供有限零点集、AE 非零、对数可积性或均方正性；左边界
内部和顶端允许零点，只有用于既有零表识别的底边条件保留。

`ConreySelectedHeightMeanSquare` 在第 18 节同一组选高上应用此结论。
令 `X=e^L,d=R/L`、`B(L)=507X/L+2.2·10^12 L^7+(A-sigma0)π`，则

\[
 N_{\rm simple}(X)\ge\frac{E_\eta(A;U,T)}\pi
 -\frac{(T-U)\log(M/(T-U))+2B(L)}{2\pi d}-1.
\]

统一阈值、`U∈[A+1,A+2]`、`T∈[X-1,X]`、三边实际非零与 `M>0`
都由定理返回。所有参数和积分高度不变，分母 `2πd` 与余项 `2B`
同时出现，没有漏掉倍数或假设实际均方上界。

三个新精确合约都先因目标定理缺失失败，再通过组合验证；组合命令
还包括旧均方、选高对数形式及实际 Littlewood 合约，共 8862 jobs，
exit 0。四条新定理仅依赖 `propext`、`Classical.choice`、`Quot.sound`。
另补上此前遗漏的 `MathlibAux.LogMeanSquare` 默认 Lake root：初次
旧合约基线因缺少该依赖编译产物失败，补 root 后旧合约正常通过。
独立只读审查未发现 AE、有限零点、可积性、系数或选高一致性问题。
Python 全量回归 546 passed；新端点 160 个本地模块的 import 闭包
无 Zeta23，外部根仅 Mathlib。这里只声称定向 Lean 验证。

**仍未证明：**上式中的实际 `M` 的长 mollifier 均方渐近式／DI 输入，
以及 `E_eta` 的定量主项与最终严格 `>2/5` 的渐近推导。已证的是实际
有限高度的均方计数不等式，不是对实际均方值的估计。

## 20. 下一步数学设计：同组选高的无权 V₁ 变幅

以下尚未实现，已经过独立数学审查。为估计 `η=H V₁` 的三边变幅，
可只在辅助估计中取 `Y=2`。由于 `P(0)=0,P(1)=1`，两项有限
Dirichlet 和给出 `B₂≡1`，从而既有实际产品的 Jensen／Borel 正则
因子接口可用于 V₁。**主均方 M 中的长 Y 绝不替换为 2。**

对辅助 V₁，在基点窗口 `A+1` 和 `X-1` 的相同几何圆盘上抽取
全部零点主部及非零正则因子 `g`。使用基点而非直接使用所选 T，
避免误用接口要求的 `base+1≤X`。原长产品在所选水平线非零，已经
推出 V₁ 在该线段非零，因此主部分解可在整个积分线段使用。

一根的无权虚部核满足
`∫ |Im(x+it-rho)^(-1)| dx≤π`：`t≠Im rho` 时用已证 Poisson 核
积分；`t=Im rho` 时该标量虚部核恒为零，单独处理。不能据此允许
原函数在线段上为零，也不能对奇异的完整复值核误用积分线性性。
补齐有限支集、非负重数及每个标量核可积性后，预期得到

\[
 \left|\int_{1/2}^{A}\Im(V_1'/V_1)(x+it)\,dx\right|
 \le \pi\,\mathrm{mass}+(A-1/2)\,\mathrm{regularBound}.
\]

这不需要重新选高度或用点态倒距离付出额外损失。该积分对应连续
相位的增量，不能换成两个主值 argument 的差。随后还须与 H 因子
及右边界估计组合，真实证明完整 `E_eta` 的定量主项。

H 因子可直接沿原三边估计，无须另换临界线：已有右边界定理
`norm_logDeriv_conreyH_sub_half_log_t_div_two_pi_le` 在 `t≥U≥A+1`
给出与 `(1/2)log(t/(2π))` 相差至多 8；水平 H 项可用已有外圆盘的
对数增长界。预期误差为 `O(T-U)` 加 `L` 的多项式，足以在 `XL`
尺度消失。仍须证明同三边上的 `logDeriv η=logDeriv H+logDeriv V₁`
及各项可积性，再作完整积分组合，不能把这些作为新的接口假设。
