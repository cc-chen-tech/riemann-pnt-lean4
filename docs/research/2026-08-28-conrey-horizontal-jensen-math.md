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

仓库中的“系数绝对值至多一”以及实际有限和界现已作为
`ConreyMollifierRightEdge` 的公共端点。外圆增长证明直接使用这些端点；
不能把右边线上 `B=1+O(1/L)` 的定理误用于整个外圆。

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

截至 2026-08-28，本节的实际乘积增长链已经逐项形式化：外圆几何给出
`norm s <= 2H`；一次 digamma 递推给出
`norm (H'/H)(s) <= 10 * (1 + log (H+2))`；随后由已证的 zeta/导数
四次增长和有限 mollifier 界装配出

\[
 |V_1(s)|\le C_1H^5,\qquad
 |V_1(s)B(s)|\le C\,Y\,H^6(L+2)^2.
\]

对应 contract 已核验所有公共端点只依赖标准公理
`propext`、`Classical.choice`、`Quot.sound`。这只完成 `HJ-growth`；下节的
Jensen divisor、可容许高度以及正则部分水平积分仍未因此自动完成。

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

形式化时边界平均取

\[
 M=C\,Y\,(U+A+10)^6(L+2)^2,
 \qquad {1\over6}\le |F(c)|.
\]

由球面点值界先得 `circleAverage log|F| <= log M`，再直接套 Jensen，
因此右端最初出现为

\[
 {\log M-\log(1/6)\over\log(\mathcal R/r)}
 ={\log M+\log6\over\log(\mathcal R/r)}.
\]

这里没有把点值上界直接冒充平均界；中间的 circle-average 单调性依赖
`F` 在整个外圆盘解析。

## 5. 可容许高度和水平积分

这里 `H` 取内圆 `closedBall(c,r)` 的 divisor 支撑的虚部；由 divisor
locality，这等价于把外圆 divisor 支撑限制到内圆，而不能取整个外圆
支撑：Jensen 只控制内圆质量，外环支撑的基数没有由 `HJ-mass` 控制。
由于整个目标矩形包含于内圆，这不会漏掉水平段上的零点。把这些虚部
组成有限集 `H`. 在
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

截至 2026-08-28，内圆质量、内圆支撑的有限性以及满足 `HJ-sep` 的
高度已经对实际乘积形式化。随后下述缓冲因子盘、因子盘质量、好圆、
同一个剥零因子的“实际质量/实际分离”中心与球面估计，以及对应的精确
Borel--Caratheodory 界也已由 Lean 逐项核验。进一步把这些端点与
`m_b<=J`、`delta_J<=delta` 合成为下面显示的 `V(J,delta_J)`，并把
几何因子粗化到常数 `128`，也已经形式化。5.3 的因子盘支撑选高和
带权主部积分的实际质量版本已经完成；同一高度上的正则项和主部积分
也已经装配为实际 `F'/F` 的精确显式界。尚缺的是把该显式界粗化为固定
多对数并证明其为 `o(exp L/L)`。

### 5.1 为什么要再加一个因子盘

不能只在半径 `r` 上剥零后立刻对所得因子使用
Borel--Caratheodory：该定理需要在待控制闭圆盘之外还有一个严格更大的
无零解析圆盘。令

\[
 \Delta=\mathcal R-r,\qquad
 b=r+{3\Delta\over4},\qquad
 a=r+{\Delta\over4},\qquad
 q_1=r+{\Delta\over2}.
\]

利用 `A>=4`、`49/100<=sigma0<=1/2` 直接比较平方，还可得到

\[
 {1\over5}<\Delta<{1\over4}.
\tag{HJ-gap}
\]

于是

\[
 r<a<q_1<b<\mathcal R,\qquad
 a-r=b-q_1=q_1-a={\Delta\over4}.
\tag{HJ-buffer}
\]

在 `closedBall(c,b)` 上剥掉实际乘积 `F` 的全部零点，写成 divisor
`D_b` 和无零解析因子 `g`. 因为 `b>=1`，中心恒等式与
`|F(c)|>=1/6` 给出

\[
 \log|g(c)|\ge -\log 6-\log b\,m_b,
 \qquad m_b:=\sum_\rho D_b(\rho).
\tag{HJ-factor-center}
\]

对半径 `b` 再用一次 Jensen，而不是错误地拿内圆质量控制更大的
因子盘，得到

\[
 m_b\le J:={\log M+\log6\over\log(\mathcal R/b)}.
\tag{HJ-factor-mass}
\]

由于 `mathcal R-b=Delta/4` 为常数量级、`mathcal R` 为 `A` 量级，
这里 `J=O(LA)=O(L log L)`。

### 5.2 好圆与正则因子的对数导数

把 `D_b` 支撑到圆心的距离组成有限集。在 `[a,q1]` 中可选到半径
`q`，使好圆避开全部因子盘零点，而且对圆上每个 `z` 和每个
`rho in supp(D_b)` 都有

\[
 |z-\rho|\ge {\Delta\over16(k+1)}
              \ge \delta_J:={\Delta\over16(J+1)},
\tag{HJ-good-circle}
\]

其中 `k` 是不同径向距离的个数，`k<=m_b<=J`. 由 `HJ-gap`，
`0<delta_J<1`。在好圆上利用
`log|F|<=log M` 和剥零恒等式，得到

\[
 \log|g(z)|\le \log M-\log\delta_J\,m_b
              \le \log M-\log\delta_J\,J.
\tag{HJ-factor-sphere}
\]

将 `HJ-factor-center`、`HJ-factor-sphere` 和 `m_b<=J` 合并，定义

\[
 V:=\log M+\log6+(\log b-\log\delta_J)J.
\]

Borel--Caratheodory 加 Cauchy 的仓库端点随后给出，对
`|z-c|<=r`，

\[
 \left|{g'\over g}(z)\right|
 \le 4\max(V,1){q+r\over(q-r)^2}
 \le 128\max(V,1){\mathcal R\over\Delta^2}.
\tag{HJ-regular-logderiv}
\]

最后一个常数只用了 `q+r<=2*mathcal R` 和
`q-r>=Delta/4`。这里没有把零点圆盘边界当成 Borel 圆；`q<b` 正是
无零解析邻域的余量。

对应公共端点保留了实际乘积的完整 divisor 主部分解，并让同一个
`g` 同时满足以实际 `m_b,delta` 写出的中心下界、球面上界和精确 Borel
不等式。现在同一个 `g` 的公共端点还完成了两次后处理：把实际量同时
替换成 `J,delta_J` 得到上面显示的 `V`，以及把 Borel 几何因子粗化到
常数 `128`。完整类型 contract（不只 `#check`）核验了这些量词和同因子
语义；公理审计只依赖标准公理 `propext`、`Classical.choice`、
`Quot.sound`。这完成的是正则对数导数的一致界，尚未自动给出其带权
积分或与主部的合并。

### 5.3 水平主部不应粗暴平方零点质量

最终高度要对因子盘 `D_b` 的全部虚部重新做有限集选择；只避开内圆
零点不足以控制分解式中来自 `r<|rho-c|<=b` 的主部。可取

\[
 |t-\operatorname{Im}\rho|\ge {1\over4(h+1)}
 \quad(\rho\in\operatorname{supp}D_b),
\tag{HJ-factor-height}
\]

其中 `h<=m_b<=J`. 这保证整条水平段上的分解无奇点。若逐点用
`1/|t-Im rho|`，会产生无谓的 `J^2`；对需要的积分应保留 Poisson
核结构。每个零点满足

\[
 \int_{\sigma_0}^{A}
 \left|\operatorname{Im}{d\sigma\over\sigma+it-\rho}\right|
 \le\pi,
\]

所以带权主部至多

\[
 \pi(A-\sigma_0)m_b\le\pi(A-\sigma_0)J.
\tag{HJ-principal-integral}
\]

截至 2026-08-28，单零点 Poisson 核恒等式、其未加权绝对积分 `<=pi`、
带权积分 `<=pi*(A-sigma0)`、带非负重数的有限支撑汇总、实际 factor
divisor 的 `finsum` 到 Finset 转换，以及对完整因子盘零点虚部重新选择
高度均已形式化。因此 `HJ-principal-integral` 的实际质量版本现已闭合；
此前尚缺的是与正则因子项合并并统一替换为显式质量 majorant `J`。

正则部分用 `HJ-regular-logderiv` 的一致界。于是两部分合并后的精确
目标上界是

\[
 \begin{aligned}
 &\left|\int_{\sigma_0}^{A}(\sigma-\sigma_0)
   \operatorname{Im}{F'\over F}(\sigma+it)\,d\sigma\right|\\
 &\quad\le
 { (A-\sigma_0)^2\over2}\,
 128\max(V,1){\mathcal R\over\Delta^2}
 +\pi(A-\sigma_0)J.
\end{aligned}
\tag{HJ-horizontal-explicit}
\]

截至 2026-08-29，这个同高度的精确端点已经形式化：所选 `t` 同时使
实际乘积在整条水平段上非零；剥零恒等式两侧的水平函数均由解析性和
无零性证明可积；主部与同一个 `g` 的正则项随后在积分层合并。完整类型
contract 直接锁定实际 `F'/F` 的上述结论，公理审计仍只有 `propext`、
`Classical.choice`、`Quot.sound`。这完成 `HJ-horizontal-explicit`，但尚未
完成下一段的多对数粗化。

按 `HJ-gap`，`Delta` 有绝对正常数量级，
`J=O(L log L)`，而 `V=O(L(log L)^2)`；因此右端可安全粗化为
`O(L(1+log L)^5)`。精确的幂次不参与 `2/5` 优化；后续必须形式化的
是某个固定多对数界，并证明它为 `o(e^L/L)`。

为降低形式化脆弱性，可以不用追求上述较尖的幂次。令 `C_r` 是正则
因子端点的增长常数，`C_m` 是因子盘 Jensen 质量端点的增长常数；不把
两个存在常数未经证明地认作相同。对最终充分大的 `L` 分别加入
`C_r<=e^L`、`C_m<=e^L`，并取

\[
 J_m={\log(C_mYH^6(L+2)^2)+\log6\over
          \log(\mathcal R/b)}.
\]

下列宽松链条足够：

1. `H<=3e^(2L)`，故增长对数连同 `log 6` 至多 `25L`；
2. `log(mathcal R/b)>=1/(40L)`。这里用
   `1-(mathcal R/b)^(-1)<=log(mathcal R/b)`、
   `mathcal R-b=Delta/4`、`Delta>1/5` 和 `mathcal R<=2L`；
3. 因而 `0<=J_m<=1000L^2`；
4. 用 `b<=2L`、`Delta>1/5` 以及
   `log x<=x` 粗估 `-log(delta_J)`，可取
   `V(C_r,J_m)<=81,000,000 L^4`；
5. 再用 `A-sigma0<=2L`、`mathcal R<=2L`、`Delta^(-2)<=25`
   代入 `HJ-horizontal-explicit`，得到安全的

\[
 |\text{horizontal}|\le 1{,}100{,}000{,}000{,}000\,L^7.
\tag{HJ-horizontal-coarse}
\]

这个七次幂比真实量级宽松很多，但没有消耗任何新的解析抵消；因为
`L^8/e^L -> 0`，它已经足以推出 `HJ-horizontal-coarse=o(e^L/L)`。
Lean 阶段应逐项保留上述分母下界和两个常数的独立性。

因此完成该因子分解后的目标为

\[
 \left|\int_{\sigma_0}^{A}(\sigma-\sigma_0)
 \operatorname{Im}{F'\over F}(\sigma+it)\,d\sigma\right|
 \ll L(1+\log L)^5.
\tag{HJ-horizontal-target}

这是后续计划的目标而非本文已得结论。需要形式化的是它为固定多对数，
并证明（指数 `5` 可由更粗的固定指数替代）

\[
 L(1+\log L)^5\le e^L/L
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
