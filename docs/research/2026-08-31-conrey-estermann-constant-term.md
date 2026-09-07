# Conrey 实际 Estermann 常数项：统一 K 界与 Gaussian 快速衰减

这里补齐一个实际误差项，而不是再增加条件接口：从周期 zeta 的
真实函数方程证明小移位下 `D(0,alpha,beta;H/K)` 的统一
`K log(2K)` 界，再精确计算它在双射线 Gaussian 分解中的贡献。
在既定 Conrey 参数下，该项及所需一阶混合微分确实比任意负幂小。

本节为纸面证明，尚未写成 Lean。#500 和 #508 的源 SHA 分别保持
`47c92840`、`1b6f1055` 不变；本节位于独立后续分支。

源目标核对 [Conrey 1989, Lemma 4, p.15 及式(60), p.18](https://aimath.org/~kaur/publications/24.pdf)。
沿用已重新推导的 [实际 Estermann 归一化](2026-08-31-conrey-estermann-normalization.md)，
特别保留负射线的负有理扭转，不沿用相应印刷符号差异。

## 1. 实际函数与统一界的精确量词

沿用实际 Hurwitz zeta `Z(u,x)`、周期 zeta
`F(u,x)=sum_(n>=1) e(nx)n^(-u)` 的解析延拓，以及

\[
 D(s,\alpha,\beta;H/K)
 =\sum_{m,n\ge1}m^{-s-\alpha}n^{-s-\beta}e(mnH/K)
\]

的实际亚纯延拓。初始 Dirichlet 级数仅在各自绝对收敛域使用。
全部正实数幂用实对数，`e(x)=exp(2 pi i x)`。

存在绝对常数 `C_D>0`，使对所有 `A>=0`、整数 `K>=1,H`
满足 `gcd(H,K)=1`，以及复数移位满足

\[
 |\alpha|,|\beta|\le
 \min\left(\frac14,\frac A{\log(2K)}\right),
 \tag{small-shifts}
\]

都有

\[
 \boxed{|D(0,\alpha,\beta;H/K)|
       \le C_D e^{2A}K\log(2K).}
 \tag{D0-bound}
\]

因此也有通常的 `O_(A,epsilon)(K^(1+epsilon))`，但这里保留更
明确的对数损失。`K=1` 单独包含，避免使用 `1/log K`。

## 2. Hurwitz 的两份紧参数界

记

\[
 B(u,x)=Z(u,x)-\frac1{u-1},
\]

其中 `u=1` 处按可去奇异延拓定义 B，不是把两个无穷值相减。
存在绝对常数 `C_0,C_1`，使

\[
 |Z(u,x)|\le C_0\quad(|u|\le1/4,\ 1\le x\le2),\qquad
 |B(u,x)|\le C_1\quad(|u-1|\le1/4,\ 1\le x\le2).
 \tag{compact-bounds}
\]

这不是额外的解析界假设。用前一文档已给出的实际 Euler 求和公式

\[
 Z(u,x)=\frac{x^{1-u}}{u-1}+\frac12x^{-u}
 +\frac u{12}x^{-u-1}
 -\frac{u(u+1)}2\int_0^\infty
 B_2(\{t\})(x+t)^{-u-2}\,dt
\]

即可直接证明。余积分的范数至多
`x^(-Re u-1)/(6(Re u+1))`。第一个参数域中
`Re u+1>=3/4, |u-1|>=3/4`，全部项一致有界。
第二个域中 `Re u+1>=7/4`，唯一待处理项是

\[
 \frac{x^{1-u}-1}{u-1}
 =-\log x\int_0^1x^{t(1-u)}\,dt.
\]

它在 `u=1` 也有意义，范数不超过 `log(2) 2^(1/4)`。
其余各项和余积分同样有一致界，得到 (compact-bounds)。

## 3. 周期 zeta 在零移位处必须先合并极点

对 `0<x<1, |beta|<=1/4`，周期 zeta 的实际函数方程在
`beta!=0` 时给出

\[
 F(\beta,x)=(2\pi)^{\beta-1}\Gamma(1-\beta)
 \left[E_+(\beta)Z(1-\beta,x)
       +E_-(\beta)Z(1-\beta,1-x)\right],
 \quad E_\pm(\beta)=e^{\pm i\pi(1-\beta)/2}.
 \tag{periodic-FE}
\]

这是 Mathlib 的 `HurwitzZeta.expZeta_one_sub` 所证明的实际
一维公式。不能在 `beta=0` 直接对两个 Hurwitz 极点分别取界。
用平移恒等式

\[
 Z(1-\beta,x)=x^{\beta-1}-\frac1\beta+B(1-\beta,1+x)
\]

及 `1-x` 的对应式，得到括号内的表达式

\[
 \begin{aligned}
 &E_+(\beta)x^{\beta-1}+E_-(\beta)(1-x)^{\beta-1}
 -\frac{2\sin(\pi\beta/2)}\beta\\
 &\qquad+E_+(\beta)B(1-\beta,1+x)
       +E_-(\beta)B(1-\beta,2-x).
 \end{aligned}
 \tag{pole-cancelled}
\]

其中正弦商在0的可去值为 `pi`，且

\[
 \frac{2\sin(\pi\beta/2)}\beta
 =\pi\int_0^1\cos(\pi t\beta/2)\,dt
\]

给出全闭圆盘上的界 `pi exp(pi/8)`。两个 `E` 的范数不超过
`exp(pi/8)`，`(2pi)^(beta-1) Gamma(1-beta)` 在此固定紧圆盘
也有绝对上界；结合 (compact-bounds)，得绝对常数 `C_F` 使

\[
 |F(\beta,x)|\le C_F\left[
 x^{\Re\beta-1}+(1-x)^{\Re\beta-1}+1\right].
 \tag{F-bound}
\]

(pole-cancelled) 在0全纯，周期 zeta 对非整数 x 也在0全纯，故
由去奇异延拓，(F-bound) 包含 `beta=0`。它不含 `1/|beta|`
或 `1/Re beta`；这正是复移位圆盘统一性所需要的。

若 `K>=2, 1<=j<=K-1`，并且 beta 满足 (small-shifts)，则
`K^|Re beta|<=e^A`，因此

\[
 |F(\beta,j/K)|
 \le C'_F e^A\left(\frac K j+\frac K{K-j}\right).
 \tag{F-rational-bound}
\]

整数相位则使用 `F(beta,0)=zeta(beta)`，由 (compact-bounds)
直接有界，而不把 `j=0` 塞进上式。

## 4. 一次有限和及调和级数给出 D0-bound

在初始绝对收敛域按 m 的模 K 剩余类分组，再作实际亚纯延拓，得

\[
 D(0,\alpha,\beta;H/K)
 =\sum_{r=1}^{K}A_r(\alpha)F(\beta,rH/K),\qquad
 A_r(\alpha)=K^{-\alpha}Z(\alpha,r/K).
 \tag{D0-finite}
\]

平移 Hurwitz 的第一项，得到

\[
 A_r(\alpha)=r^{-\alpha}
       +K^{-\alpha}Z(\alpha,1+r/K),
 \qquad |A_r(\alpha)|\le(1+C_0)e^A.
 \tag{A-bound}
\]

因为 `1<=r<=K` 且 `|Re alpha| log K<=A`，这个界对全部 r
同时成立。`r=K` 时直接为 `K^(-alpha) zeta(alpha)`。

对 `K>=2`，乘以 H 在非零模 K 剩余类上是置换，故将
(F-rational-bound) 求和得到

\[
 \sum_{r=1}^{K-1}|F(\beta,rH/K)|
 \le 2C'_F e^A K\sum_{j=1}^{K-1}\frac1j
 \ll e^A K\log(2K).
\]

再乘 (A-bound)，并加上 r=K 的有界项，即证 (D0-bound)。
`K=1` 时 `D(0,alpha,beta;H)=zeta(alpha)zeta(beta)`，扩大同一
绝对常数即可包含。证明也覆盖负 H，因为置换论证不依赖其符号。

注意这个步骤使用的是一次有限和和模 K 置换；对原来的双重有限
Hurwitz 和直接逐项取界会给出不必要的 K 平方损失。

## 5. 双射线上的 Gaussian 常数积分必须先精确评价

固定 `Delta>0`、复数 `u`，以及 `0<phi<pi/2`。令两条射线
`L_(sigma phi)` 从原点向外，`sigma=+1,-1`。定义

\[
 G_\sigma(u,\Delta)=\int_{L_{\sigma\phi}}
 v^u e^{-\Delta^2(\operatorname{Log}v)^2/4}\,\frac{dv}{v}.
\]

主值 `Log` 在两条射线及它们与正实轴之间的扇形内一致。
参数化 `Log v=t+i sigma phi`，被积函数变成整函数
`exp(u xi-Delta^2 xi^2/4)` 在水平线上的积分。
对高度介于0与 `sigma phi` 的有限矩形用 Cauchy 定理；两条竖边
的范数由 `C exp(Re(u)t-Delta^2 t^2/4)` 控制，在两端趋零。
实轴和水平线积分都绝对可积，故可移回实轴。
再用复 Gaussian 积分，得到精确等式

\[
 \boxed{G_\sigma(u,\Delta)
 =\frac{2\sqrt\pi}{\Delta}\exp(u^2/\Delta^2).}
 \tag{G-exact}
\]

它不依赖 sigma 或 phi。这里是复数 `u^2`，不是 `|u|^2`；因此

\[
 |G_\sigma|=\frac{2\sqrt\pi}{\Delta}
 \exp\!\left(\frac{(\Re u)^2-(\Im u)^2}{\Delta^2}\right).
 \tag{G-modulus}
\]

必须在精确评价之后取绝对值。先对射线被积函数取范数，会丢失
`exp(-(Im u)^2/Delta^2)` 这份真实振荡相消。

## 6. 对接实际有限 mollifier：常数项的完整表达式

取 `L=log T>=24`、`0<delta<1`、`0<theta<=1`，
整数 `2<=Y<=T^theta`，`T<=w<=2T`，并令

\[
 \Delta=T^{1-\delta},\quad s_0=\tfrac12+iw,\quad
 \alpha=a/L,\quad\beta=b/L,\quad\gamma=\alpha+\beta,
 \qquad |a|,|b|\le3.
\]

在本节中 a,b 是放大后的复移位，alpha,beta 为真实 zeta 移位；
不要把它们与前四节的独立一般移位混淆。

取实际有限系数
`c_j(n)=mu(n) P_j(log(Y/n)/log Y)`，记
`B_j=sup_(0<=t<=1) |P_j(t)|`；P_j 为固定实多项式，故
`|c_j(n)|<=B_j`。既定 profile 的 B_j 可取1，但本证明不需要它。

对 `1<=h,k<=Y`，令 `d=gcd(h,k), H=h/d, K=k/d`。
前一份实际双射线分解的常数项恰为

\[
 \begin{aligned}
 E_0(a,b,w;T,Y)={}&
 \sum_{h,k\le Y}\frac{c_1(h)c_2(k)}{k^{1-\beta}h^\beta}
 \sum_{\sigma=\pm1}
 D(0,\gamma,0;\sigma H/K)\,G_\sigma(s_0-\beta,\Delta).
 \end{aligned}
 \tag{E0-actual}
\]

没有再乘 `1/(i Delta sqrt(pi))` 或 `1/(2 pi)`：前者已经在
J 核变换中消去，当前射线积分的归一化正是 (G-exact)。
负射线的 D 扭转为负，但两份 Gaussian 常数积分相同。
有限求和与已经绝对可积的每个常数积分可直接交换。

现在逐项核对 (D0-bound) 的使用条件：

\[
 |\gamma|\le6/L\le1/4,\qquad
 |\gamma|\log(2K)\le(6/L)(\log2+\log Y)<7.
\]

所以对所有 h,k、a,b 同时可取 `A=7`。另外

\[
 \left|\frac1{k^{1-\beta}h^\beta}\right|
 =\frac1k\exp(\Re\beta\log(k/h))\le\frac{e^3}{k},
 \qquad K\le k.
\]

而 `|Re(s_0-beta)|<=3/4`、`|Im(s_0-beta)|>=T-1/4`，
在 `T>=2` 时有

\[
 (\Re(s_0-\beta))^2-(\Im(s_0-\beta))^2
 \le-\tfrac12T^2.
\]

应用 (G-modulus)、(D0-bound) 并对至多 `Y^2` 对 h,k 求和，得
一个绝对常数 C，使

\[
 \boxed{|E_0(a,b,w;T,Y)|
 \le C B_1B_2\frac{Y^2\log(2Y)}{\Delta}
       \exp(-\tfrac12T^{2\delta}).}
 \tag{E0-uniform}
\]

此界同时对闭移位双圆盘、`w in [T,2T]`、全部允许整数 Y 和
`0<phi<pi/2` 成立。角度的一致性来自精确等式，不声称射线
被积函数的绝对值有同样的角度一致衰减。

## 7. 真正的快速衰减及所需混合微分

对任意固定 `M>=0, delta in (0,1)`，(E0-uniform) 给出

\[
 E_0=O_{\delta,M}(B_1B_2T^{-M})
 \tag{E0-flat}
\]

且保留上一节全部一致性。一个直接证明是用 `Y<=T`、
`Delta>=1`、`log(2Y)<=T`（当前 `T>=exp(24)`），将前因子
压成 `C B_1B_2 T^3`；再选整数 `n` 使 `2 delta n>=M+3`。
`exp(v)>=v^n/n!` 给出
`exp(-T^(2delta)/2)<=n! 2^n T^(-2delta n)`，即得所需界。
本步骤没有消耗 DI 估计中的待证幂次节省。

还需确保之后的微分算子不会破坏这个误差。由 (D0-finite) 及
pole-cancelled 表达式，实际 D(0,gamma,0) 在 `|gamma|<1/2`
全纯；正底数幂和 (G-exact) 对移位也全纯。因此 (E0-actual)
对 `|a|,|b|<4` 全纯（`L>=24` 时 `|gamma|<1/3`）。
在 `a=b=-6/5` 周围取两份半径 `1/2` 的 Cauchy 圆，它们全部
位于已控制的 `|a|,|b|<=3` 内。若 F(T) 为 (E0-uniform) 的
右侧，则

\[
 |E_0|\le F(T),\quad |\partial_aE_0|,|\partial_bE_0|\le2F(T),
 \quad|\partial_a\partial_bE_0|\le4F(T).
\]

故既定 `kappa=51/50` 对应的算子满足

\[
 \left|(1+\kappa\partial_a)(1+\kappa\partial_b)E_0
       \bigm|_{a=b=-6/5}\right|
 \le\frac{5776}{625}F(T).
 \tag{E0-differentiated}
\]

特别地，实际常数项在接到先前已识别的 mollified 均方时仍是
`O_(delta,M)(B_1B_2 T^(-M))`。这里先对独立复移位求导，再在
负实移位处评价；没有错误地对已经取共轭的表达式作全纯求导。

## 8. 当前推进了什么、还没有推进什么

本节新完成的纸面步骤是：

- 对实际 D(0) 的小复移位给出统一 `K log(2K)` 界；
- 证明真实双射线常数项在全部 Conrey 参数范围内一致快速衰减；
- 证明该快速衰减在所需的一阶混合微分算子下仍成立。

它不是完整 Gaussian/Estermann 分解的最终渐近式。同一检查点的
[实际 Gaussian 轮廓分解](2026-08-31-conrey-gaussian-contour-decomposition.md)
另行证明从实际 g 移线得到 J 级数的留数误差及整射线分项可积性。
仍须处理极点主项 M 的统一渐近评价、真正对偶余项 E 的核与 DI
谱估计、完整均方、去平滑、整数截断归一化和最终简单零点计数。
这里的 E_0 只是其中一个明确的实际加项，不能覆盖这些剩余项。

原生化可复用 `HurwitzZeta.expZeta_one_sub` 及复 Gaussian 积分。
零移位处的可去奇异、紧参数 Hurwitz 界、有限剩余类分解、统一
常数与实际有限和的组装仍须写成 Lean 并验证。本节未运行 Lean，
也没有改动任何已冻结 PR 的源树。
