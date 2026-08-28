# Conrey 水平边：先做数学的 Jensen 圆盘设计

## 0. 结论边界

这份说明只处理 Conrey 1989 式 (37) 中两条水平边所需的
Jensen/可容许高度机制。它不声称式 (38)--(41)、长 mollified second
moment 或严格 `> 2/5` 已经完成。

已完成的前置输入是实际乘积

\[
 F_{L,Y,R}(s)=V_1(s)B(s),\qquad
 V_1(s)={49\over100}\zeta(s)+{51\over50L}
 \left(\zeta'(s)+{H'(s)\over H(s)}\zeta(s)\right),
\]

以及移动右边

\[
 A=2\log L,\qquad 1\le t\le e^L,
\]

上的显式非消失和全局对数积分

\[
 \int_1^{e^L}|\log|F(A+it)||\,dt\le {507e^L\over L}.
\]

## 1. 为什么不把下端固定在 `t=1`

以 `A+it` 为中心、能覆盖 `[sigma0,A]` 的单个 Jensen 圆盘半径约为
`A`. 若 `t=1`，该圆盘会碰到 `s=1`，而 `V1` 在这里不能直接作为解析
函数使用。可以改用 completed/regularized carrier，但会引入不必要的
Gamma 正规化账本。

更直接的做法是在

\[
 U_-:=A+1
\]

之后选择下端高度。这样只舍弃高度 `O(log L)=O(log log T)` 的初段。
Hardy/argument-variation 主项仍为 `T log T`；下端的所有多对数误差均为
`o(T/L)`，所以在除以 Littlewood gap `R/L` 后仍为 `o(T)`。

顶部在 `[e^L-1,e^L]` 中选择可容许高度。这样右边中心始终留在已经
证明的全局范围 `1 <= t <= e^L` 内，不需要把右边估计外推到 `e^L+1`。

## 2. 精确圆盘几何

固定

\[
 L\ge 40000,\quad 0\le R\le{6\over5},\quad
 \sigma_0={1\over2}-{R\over L},\quad A=2\log L,
\]

并取任意高度窗口 `[U,U+1]`，满足

\[
 A+1\le U,\qquad U+1\le e^L.
\]

圆心、内半径和外半径定义为

\[
 c=A+i(U+1/2),\qquad
 r=\sqrt{(A-\sigma_0)^2+1/4},\qquad
 \mathcal R=A-1/4.
\]

需要逐项证明：

1. 矩形 `[sigma0,A] x [U,U+1]` 包含于 `closedBall(c,r)`；
2. `0<r<mathcal R`；
3. `closedBall(c,mathcal R)` 中 `Re s>=1/4`；
4. 该外圆盘不含 `s=1`。事实上
   `Im c-mathcal R >= U+1/2-(A-1/4) >= 7/4`；
5. 因而实际的 `F=V1*B` 在整个外圆盘邻域解析，不需换成抽象替身。

半径比不是固定常数：

\[
 \log(\mathcal R/r)\asymp {1\over A}.
\]

所以由一个 `O(L)` 的对数增长上界得到的零点质量是
`O(L A)=O(L log L)`，而不是纸面叙述中的最优 `O(L)`。这个损失完全
可以接受，因为

\[
 L(\log L)^k=o(e^L/L)
\]

对每个固定 `k` 成立。形式化路线因此优先选择不跨过 `Re s=0` 的实际
乘积圆盘，而不为省一个 `log L` 引入 completed carrier。

## 3. 外圆增长预算

在外圆盘上 `Re s>=1/4`，且 `|Im s|` 与窗口高度相差至多 `A`。
以下三个估计要分别证明，不能作为假设塞进最终接口。

### 3.1 mollifier

显式多项式 `P` 在 `[0,1]` 上满足 `|P|<=1`，且 `sigma0<=1/2`，所以
每个系数绝对值至多一。对 `Re s>=1/4`，

\[
 |B(s)|\le\sum_{n\le Y}n^{-1/4}\le Y.
\]

在真正的 Conrey 截断 `2<=Y<=e^L` 下，`log max(1,|B|)<=L`。

仓库中“系数绝对值至多一”的证明目前是
`ConreyMollifierRightEdge` 的 private lemma。形式化增长界时应把这一
有限和事实公开为独立端点，或者在新模块中重证；不能把右边线上
`B=1+O(1/L)` 的定理误用于整个外圆。

### 3.2 zeta 与导数

外圆并不具有固定的实部上界：其最右点约为 `4 log L`。因此先在
`1/4<=Re s<=4` 使用仓库已有的多项式竖直增长，在 `Re s>=4`
使用绝对收敛区的统一 zeta 界。

对导数固定 Cauchy 半径 `delta=1/16`。若中心
`Re s<=63/16`，则 Cauchy 圆落在 `0<=Re w<=4`；由外圆下端
`Im s>=7/4`，该小圆还满足 `|Im w|>=27/16>1`，所以可直接使用
零到四条带的多项式界。若 `Re s>63/16`，则同一小圆完全落在
`Re w>2`，使用绝对收敛区的统一 zeta 界。两段都由仓库已有的
`norm_deriv_riemannZeta_le_of_sphere_norm_bound_avoid_one` 转成导数界。
于是存在固定 `Cz>=1` 使

\[
 |\zeta(s)|+|\zeta'(s)|\le
 C_z(|\operatorname{Im}s|+A+10)^4.
\]

最终产品仍可粗化到六次幂；这里没有必要因 Cauchy 圆额外损失一次
幂。

### 3.3 archimedean 对数导数

需要先把仓库现有的 `logDeriv_conreyH_eq` 从 `Re s>1` 推广到精确的
适用域 `Re s>0` 且 `s!=1`。其证明中的 Gamma 非零、`s!=0` 和
非正整数极点排除只用到 `Re s>0`；线性因子只额外需要 `s!=1`。
推广后仍有

\[
 {H'\over H}(s)={1\over s}+{1\over s-1}
 -{\log\pi\over2}+{1\over2}\psi(s/2)
\]

和 digamma 递推 `psi(z)=psi(z+1)-1/z`。这里 `z=s/2` 只有
`Re z>=1/8`，不能直接套用要求 `Re z>=1/4` 的现有辅助定理；但外圆
几何给出 `|Im s|>=7/4`，故 `|Im z|>=7/8`、`|z^{-1}|<=8/7`，而
`Re(z+1)>=1`，一次递推即可回到标准 digamma 对数界。在外圆离
`s=1` 的虚部距离至少 `7/4` 的条件下得到

\[
 \left|{H'\over H}(s)\right|
 \le C_H\{1+\log(|s|+2)\}.
\]

合并后存在固定 `C>=1`，使外圆上

\[
 |F(s)|\le
 M(L,Y,U):=C\,Y\,(U+A+10)^6(L+2)^2.
\tag{HJ-growth}
\]

当 `Y<=e^L` 且 `U<=e^L` 时，`log M=O(L)`。

这一节的 Lean 依赖账本因此是：公开实际 mollifier 的有限和界；证明
外圆 `Im s>=7/4`；推广 `H'/H` 精确公式；按 `63/16` 分段证明 zeta
及导数增长；最后才装配实际 `V1*B`。其中任何一项缺失时，Task 3
都只能标为未完成。

## 4. 中心下界和 Jensen 质量

圆心在移动右边上。已有高段与低段估计可统一加强为

\[
 |F(A+it)|\ge {1\over6}
 \qquad(1\le t\le e^L,\ L\ge40000).
\tag{HJ-center}
\]

低段已有更强的 `2/5`；高段由高度主项 `>=1/3` 和已证明的乘积误差
界推出 `>=1/6`。

令 `D` 为 `F` 在 `closedBall(c,mathcal R)` 上的解析 divisor。Jensen
给出内圆零点质量的精确界

\[
 N_D(r):=\sum_{|rho-c|\le r}D(rho)
 \le {\log M(L,Y,U)+\log 6\over
          \log(\mathcal R/r)}.
\tag{HJ-mass}
\]

右端随后可粗化为固定常数乘 `L(1+log L)`；在 Lean 中保留
`HJ-mass` 作为第一公共端点，再单独证明尺度粗化，避免把几何损失藏在
大 O 中。

## 5. 可容许高度和水平积分

外圆 divisor 支撑有限。把内矩形零点的虚部组成有限集 `H`. 在
`[U,U+1]` 中选择 `t`，使

\[
 |t-gamma|\ge {1\over4(|H|+1)}\qquad(gamma\in H).
\tag{HJ-sep}

于是整条 `[sigma0,A]+it` 上 `F` 非零。对 divisor 主部，每个零点满足

\[
 \left|\int_{\sigma_0}^{A}
 \operatorname{Im}{d\sigma\over\sigma+it-rho}\right|\le\pi.
\]

所以主部的未加权水平 argument variation 至多 `pi*N_D(r)`。

这里必须明确保留下一项未证义务：还要构造零点移除后的无零解析
因子、选择解析对数，并用 Borel--Caratheodory 控制它的对数导数。
`HJ-growth` 与 `HJ-mass` 本身并不自动给出这个正则部分估计。预期在
内外圆间距约常数而圆半径约 `A` 的几何下，正则部分只有固定多对数
损失；完成该因子分解后，目标才是

\[
 \left|\int_{\sigma_0}^{A}(\sigma-\sigma_0)
 \operatorname{Im}{F'\over F}(\sigma+it)\,d\sigma\right|
 \ll L(1+\log L)^4.
\tag{HJ-horizontal-target}

这是后续计划的目标而非本文已得结论。精确的幂次不参与 2/5 优化；
需要形式化的是它为固定多对数，并证明

\[
 L(1+\log L)^4\le e^L/L
\]

对显式充分大的 `L` 成立。

## 6. 与式 (37) 的拼接边界

分别在底部窗口 `[A+1,A+2]` 和顶部窗口 `[e^L-1,e^L]` 选择高度。
在 `HJ-horizontal-target` 真正证明后，两条水平项合计为
`o(e^L/L)`。已证明的 `507e^L/L` 控制的是移动右边上的
`|log|F||` 积分；它是竖边分部积分产生的模长项所需输入，但
`(37-exact)` 还另有

\[
 (A-\sigma_0)\int_{t_0}^{t_1}\operatorname{Re}{F'\over F}(A+it)\,dt.
\]

沿 `A+it`，`d/dt log|F|=-Im(F'/F)`，而 `Re(F'/F)` 是连续
argument 的导数。因此这一项是右边 argument variation，不是两个端点
的 `log|F|` 差；中心下界和点值上界也不能单独控制它。它必须用右边
`F=1+O(1/L)` 型的定量归一化或等价的连续 argument 控制另行证明，
并且尚未由 `507e^L/L` 的绝对对数积分推出。只有把这项与两条水平项
都闭合后，才能称 `(37-exact)` 的整个
非左边界为 `O(e^L/L)`。

最后除以 gap `R/L` 时必须额外假设固定 `R>0`。当前圆盘几何允许
`R=0`，但式 (37) 的拼接不允许除以零。真正证书取 `R=6/5`，因而该
条件在最终实例化时满足。

这一步仍不提供左边的长 mollified second moment；它只把边界几何从
后续均值定理中完全分离出来。

## 7. 来源与校正

- J. B. Conrey, *More than two fifths of the zeros of the Riemann zeta
  function are on the critical line*, J. reine angew. Math. 399 (1989),
  1--26, DOI `10.1515/crll.1989.399.1`；式 (37) 是 Littlewood/Jensen
  入口。
- Conrey 1983, Section 4 是原文引用的水平 argument 与右边估计模型。
- 原文 `sigma1=log L` 与下一页 `2^{-sigma1} << L^{-1}` 不相容；本仓库
  已用 `A=2 log L` 修复。本文继续使用该校正，不回退到印刷常数。
