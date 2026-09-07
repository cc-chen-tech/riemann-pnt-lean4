# Conrey 实际 Gaussian 积分的完整轮廓分解与两项可忽略误差

本节把前面的核、双射线和 Estermann 公式真正接回原 Gaussian
移位积分。证明右移竖线的确切留数、各个射线项的可积性，得到
实际主项、实际对偶余项以及两份一致快速衰减误差的精确分解。
仍未评价主项的最终渐近，也未证明对偶余项的 DI 谱估计。

这是纸面数学交付，不是 Lean 完成声明。#500、#508 源树不改，
本节在独立后续分支上继续。源公式对应
[Conrey 1989, pp.17–18](https://aimath.org/~kaur/publications/24.pdf)，
但使用前文独立推导的归一化与负扭转符号。

## 1. 固定实际函数，不以代理函数代替 g

沿用 [常数项证明](2026-08-31-conrey-estermann-constant-term.md) 的参数：
`L=log T>=24, 0<delta<1, 0<theta<=1, 2<=Y<=T^theta`，Y 为
整数，`w in [T,2T], |a|,|b|<=3`，以及

\[
 \alpha=a/L,\quad\beta=b/L,\quad\gamma=\alpha+\beta,
 \quad\Delta=T^{1-\delta},\quad s_0=\tfrac12+iw.
\]

令

\[
 c_j(n)=\mu(n)P_j\!\left(\frac{\log(Y/n)}{\log Y}\right),\quad
 \mathcal B_j(s)=\sum_{n\le Y}c_j(n)n^{-s},\quad
 B_j=\sup_{0\le t\le1}|P_j(t)|.
\]

定义实际积分

\[
 g(a,b,w)=\frac1{i\Delta\sqrt\pi}\int_{(1/2)}
 e^{(s-s_0)^2/\Delta^2}\zeta(s+\alpha)\zeta(1-s+\beta)
 \mathcal B_1(s)\mathcal B_2(1-s)\,ds.
 \tag{g-actual}
\]

它正是前面已证明可移位求导、可识别为所选 mollified 均方的那个
函数。竖线向上，全部正实数幂用实对数。

## 2. 把真实竖线右移到 c=3/2

被积函数在 `1/2<=Re s<=3/2` 内唯一可能的极点为
`s=1-alpha`。另一份 zeta 的极点位于 `s=beta`，实部至多1/8，
不在本条带；两份有限 Dirichlet 多项式与高斯权均整。
`s=1-alpha` 严格在条带内部，其余因子在该点正则，因为
`|gamma|<=1/4`。

这里也要检查无限高的横边。用 Estermann 文档给出的 Hurwitz
Euler 求和公式取 x=1，得到实际 zeta 在
`-3/4<=Re z<=7/4, |Im z|>=1` 的统一二次多项式界。
当 `|Im s|>=2` 时，当前两份 zeta 的自变量都落在该域。
两份 mollifier 在该条带上的范数分别不超过
`B_1 Y`、`B_2 Y^(3/2)`；因而高斯权以外的因子由一个固定
`C B_1B_2 Y^(5/2)(1+|Im s|)^4` 控制。

高斯权的范数为

\[
 \exp\!\left(((\Re s-1/2)^2-(\Im s-w)^2)/\Delta^2\right),
\]

所以顶、底横边在高度趋于正、负无穷时都消失。两条竖线上的低
高度部分均避开极点，紧性给界；高处由上述高斯支配可积。
有限矩形留数定理因此合法地给出右移公式。

把 (g-actual) 中的竖线改为 `c=3/2` 得到 `g_c`。注意符号：
右竖线向上、左竖线向下的正向矩形满足
`integral_right-integral_left=2 pi i Res`。所以

\[
 \boxed{g=g_c+E_{\rm pole},}
 \tag{g-shift}
\]

其中确切误差是

\[
 \boxed{E_{\rm pole}=-\frac{2\sqrt\pi}{\Delta}
 e^{(1-\alpha-s_0)^2/\Delta^2}\zeta(\gamma)
 \mathcal B_1(1-\alpha)\mathcal B_2(\alpha).}
 \tag{pole-actual}
\]

这不是仅声明留数很小，而是保留了负号、全部实际函数和归一化。

## 3. 留数误差在同一闭复移位域内一致快速衰减

`zeta(gamma)` 在 `|gamma|<=1/4` 上有绝对界。
又因 `|Re alpha| log Y<=3`，有

\[
 |\mathcal B_1(1-\alpha)|\le e^3B_1(1+\log Y),\qquad
 |\mathcal B_2(\alpha)|\le e^3B_2Y.
\]

`1-alpha-s_0=1/2-alpha-iw` 的实部范数至多3/4，虚部范数
至少 `T-1/4`。同前一文档的高斯平方计算得到

\[
 \boxed{|E_{\rm pole}|\le C B_1B_2\frac{Y\log(2Y)}{\Delta}
       e^{-T^{2\delta}/2}.}
 \tag{pole-uniform}
\]

这是对 a,b,w,Y 的同一一致界，故对每个固定 `M>=0` 也是
`O_(delta,M)(B_1B_2 T^(-M))`。
全部因子对 `|a|,|b|<4` 全纯，因而第7节的 Cauchy 微分处理
同样适用于这个实际留数误差。

## 4. 从 g_c 到实际双射线级数

在 `Re s=3/2` 上，`Re(s+alpha)>1`、`Re(s-beta)>1`。
将实际函数方程
`zeta(1-s+beta)=chi(1-s+beta) zeta(s-beta)` 代入。
两个 zeta Dirichlet 级数绝对收敛；Gamma 的 Euler 粗界与余弦
至多指数线性增长，再乘高斯权给出可积支配。因此可以交换这两个
级数与竖线积分，有限 h,k 和则无收敛问题。精确得到

\[
 g_c=\sum_{h,k\le Y}\frac{c_1(h)c_2(k)}k
 \sum_{m,n\ge1}m^{-\alpha}n^\beta
 J(mnh/k,s_0,\beta,\Delta).
 \tag{gc-J}
\]

这里 n 的指数为正 beta。使用已证明的实际 J 核及双射线换序，
令 `r_0=h/k=H/K` 为约分后的比值、`u=s_0-beta`，得

\[
 g_c=\sum_{h,k\le Y}A_{h,k}(\beta)
 \sum_{\sigma=\pm1}\int_{L_{\sigma\phi}}W_u(v)
 S(\sigma r_0(v-1),\gamma,0;\sigma H/K)\,\frac{dv}{v},
 \tag{gc-rays}
\]

其中

\[
 A_{h,k}(\beta)=\frac{c_1(h)c_2(k)}{k^{1-\beta}h^\beta},\qquad
 W_u(v)=v^u e^{-\Delta^2(\operatorname{Log}v)^2/4}.
\]

对 `v in L_(sigma phi)`，`x_sigma(v)=sigma r_0(v-1)` 在上半
平面，`z_sigma(v)=-2 pi i x_sigma(v)` 在右半平面。
两个有理扭转也分别为正、负；两条射线都向外定向。

## 5. 主项与实际对偶余项各自可积

前一份 Estermann 分解在每个射线点给出

\[
 S(x_\sigma(v),\gamma,0;\sigma H/K)
 =M_\gamma(K,z_\sigma(v))
  +D(0,\gamma,0;\sigma H/K)+R_\sigma(v).
 \tag{pointwise-split}
\]

这里当 `gamma!=0` 时

\[
 M_\gamma(K,z)=K^{\gamma-1}\zeta(1-\gamma)\Gamma(1-\gamma)
 z^{\gamma-1}+K^{-\gamma-1}\zeta(1+\gamma)z^{-1},
 \tag{M-actual}
\]

在 `gamma=0` 取已经证明的可去值
`(gamma_E-2 log K-Log z)/(Kz)`。R_sigma 则是实际对偶积分

\[
 \begin{aligned}
 R_\sigma(v)=\frac1{\pi i}\int_{(3/2)}&z_\sigma(v)^{s-1}
 K^{2s-1-\gamma}(2\pi)^{\gamma-2s}
 \Gamma(1-s)\Gamma(s-\gamma)\Gamma(s)\\
 {}\times\bigl[&\cos\tfrac\pi2(2s-\gamma)
 D(s,-\gamma,0;-\sigma\bar H/K)\\
 &+\cos\tfrac\pi2\gamma\,
 D(s,-\gamma,0;\sigma\bar H/K)\bigr]\,ds.
 \end{aligned}
 \tag{R-actual}
\]

其中 `H Hbar=1 mod K`；`sigma Hbar` 正是 `sigma H` 的逆。
内层积分在每个射线点绝对收敛，已由前文的实际 Gamma/Dirichlet
界证明。不能仅凭逐点收敛就交换它与 v 积分。

为合法分开 (pointwise-split)，先检查 M。对两条射线都有

\[
 |z_\sigma(v)|=2\pi r_0|v-1|\ge2\pi r_0\sin\phi>0,
 \qquad |\arg z_\sigma(v)|<\pi/2.
 \tag{z-away}
\]

`M_gamma(K,z)` 对 `|gamma|<1` 全纯（0处按合流延拓）。在圆
`|gamma|=1/3` 上，zeta、Gamma 系数均有绝对界，并有

\[
 |M_\gamma(K,z)|\le C K^{-2/3}
 (|z|^{-2/3}+|z|^{-4/3}+|z|^{-1}).
\]

由最大模原理，此界也控制 `|gamma|<=1/4`。
再用 (z-away)，即得对全部 r>0 的有限统一上界
`C_(K,r_0,phi)`。因此 `W_u(v)M_gamma(K,z_sigma(v))` 相对于
`|dv/v|` 绝对可积，因为 log-Gaussian 控制两端的所有实幂。

常数项的可积性及精确评价由前文 (G-exact) 给出。
实际 S 的加权绝对可积性则来自已证明的双射线求和界，可以统一
取其中的 `q=2`。故由 (pointwise-split) 及三角不等式，
`W_u(v)R_sigma(v)` 也绝对可积。

这个论证没有把前文固定角隙的 R-sector-bound 误用成整条射线
的统一界。它也没有声称 s,v 双重积分绝对可积，或允许把其顺序
颠倒；后续核估计仍须为所需的进一步换序另给支配。

## 6. 真实 g 的完整精确分解

现在可以定义实际、各自绝对可积的两项

\[
 \begin{aligned}
 \mathcal M(a,b,w)&=\sum_{h,k\le Y}A_{h,k}(\beta)
 \sum_{\sigma=\pm1}\int_{L_{\sigma\phi}}
 W_u(v)M_\gamma(K,z_\sigma(v))\,\frac{dv}{v},\\
 \mathcal E(a,b,w)&=\sum_{h,k\le Y}A_{h,k}(\beta)
 \sum_{\sigma=\pm1}\int_{L_{\sigma\phi}}
 W_u(v)R_\sigma(v)\,\frac{dv}{v}.
 \end{aligned}
\]

结合 (g-shift)、(gc-rays)、(pointwise-split)，得到

\[
 \boxed{g=\mathcal M+\mathcal E+E_0+E_{\rm pole}.}
 \tag{g-decomposition}
\]

E_0 是常数项文档中给出的实际有限和，而不是任意误差代理。
前文已评价它的 Gaussian 积分。两份已经关闭的误差合计满足

\[
 |E_0+E_{\rm pole}|\le
 C B_1B_2\frac{Y^2\log(2Y)}\Delta e^{-T^{2\delta}/2}
 =O_{\delta,M}(B_1B_2T^{-M})\quad(M\ge0).
 \tag{closed-errors}
\]

这是同一闭复移位双圆盘和全部 w,Y 上的实际一致估计。
没有将 mathcal E 一同放入这个小误差符号。

## 7. 与既定移位微分算子的接口是恒等式，不是新假设

对每个固定 T,Y,w,phi，mathcal M、mathcal E 都对
`|a|,|b|<4` 全纯。具体地，在任意紧子双圆盘上，
`|gamma|<1/3`；对 M 使用半径1/2的 gamma 圆得到统一界。
对 S 使用 `q=2` 的双射线绝对求和界，取允许实部范围中最大的
两个实幂来控制 `|v^u|`；log-Gaussian 在两端均可积。
D(0) 在此固定有限模数范围也局部一致有界。
于是 R=S-M-D(0) 继承可积支配，积分全纯定理适用。
这些支配常数可以依赖固定 T；它们不是对 T 的均方渐近估计。

所以可以对 (g-decomposition) 施加
`mathcal D=(1+(51/50)partial_a)(1+(51/50)partial_b)`。
对 (closed-errors) 在 `a=b=-6/5` 周围取半径1/2的两份
Cauchy 圆，得到

\[
 \left|\mathcal D(E_0+E_{\rm pole})\bigm|_{a=b=-6/5}\right|
 \le\frac{5776}{625}\,
 C B_1B_2\frac{Y^2\log(2Y)}\Delta e^{-T^{2\delta}/2}.
\]

取 P_1=P_2 为既定实 profile 时，前面已证明的实际移位微分识别
把分解式左端的 `mathcal D g` 接为真实 Gaussian mollified 均方。
其余精确剩项是 `mathcal D mathcal M` 与 `mathcal D mathcal E`；
必须实际评价前者、控制后者后，才可能宣布均方主项成立。

## 8. 当前证明边界

纸面上现在已有从实际 g 出发的合法轮廓分解，以及留数项和
Estermann 常数项的一致快速衰减。它关闭了前一检查点列出的
g 移线及整射线分项可积性问题。

未完成的是：mathcal M 的所需统一渐近及外层算术主项匹配；
mathcal E 的实际核估计与 DI 谱估计（包括进一步换序及双重和的
范围控制）；完整均方、去平滑、整数截断归一化和简单零点比例。
没有新增已验证 Lean 定理，也不宣称真正 Conrey >2/5 已完成。
