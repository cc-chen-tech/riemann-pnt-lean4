# Conrey 实际 Gaussian 主项：双射线精确评价与统一算术化

这里评价 #510 留下的实际主项，不增加一个假设主项已经成立的
接口。先将两条射线化成 Gamma 商的 Gaussian 平均，再证明带有
移位零因子的统一误差，最后接回原来的有限 gcd 算术和。
误差在合流移位处也受控，并可通过所需混合微分。

本节为纸面数学，尚未原生化到 Lean。#500、#508、#510 的源树
均不改；当前基线为 #510 的 `d505714b`。
主项核对应 [Conrey 1989, pp.18–19, (59), (63)–(64)](https://aimath.org/~kaur/publications/24.pdf)。
以下独立推导两条射线的合并表达式，不把单条射线的渐近直接翻倍，
也不采用原文 (64) 的乘法 `1+o(1)` 来处理可能为零的主项。

标准一维公式参照 [Euler beta 积分](https://dlmf.nist.gov/5.12.E1)、
[Gamma 反射公式](https://dlmf.nist.gov/5.5.E3) 和
[digamma 级数](https://dlmf.nist.gov/5.7.E6)。本节所需的带误差
Gamma 商估计在第4节直接证明，不额外假设一个 Stirling 估计。

## 1. 保持实际参数、算术系数和剩项

沿用 [实际 Gaussian 轮廓分解](2026-08-31-conrey-gaussian-contour-decomposition.md)：

\[
 L=\log T\ge24,\quad 0<\delta<1,\quad \Delta=T^{1-\delta},
 \quad T\le w\le2T,\quad s_0=\tfrac12+iw,
 \quad\alpha=a/L,\quad\beta=b/L,\quad\gamma=\alpha+\beta,
 \quad |a|,|b|\le3.
\]

整数 `2<=Y<=T^theta, 0<theta<=1`，系数
`c_j(n)=mu(n) P_j(log(Y/n)/log Y)`，`|c_j(n)|<=B_j`。
记 `u=s_0-beta`；每对 h,k 的约分量为
`d=gcd(h,k), H=h/d, K=k/d, r_0=h/k=H/K`。
两条射线 `L_(sigma phi)` 均向外，`0<phi<pi/2`。

实际主项为

\[
 \mathcal M=\sum_{h,k\le Y}\frac{c_1(h)c_2(k)}{k^{1-\beta}h^\beta}
 \sum_{\sigma=\pm1}\int_{L_{\sigma\phi}}W_u(v)
 M_\gamma(K,z_\sigma(v))\,\frac{dv}{v},
\]

其中

\[
 \begin{split}
 W_u(v)&=v^u e^{-\Delta^2(\operatorname{Log}v)^2/4},\qquad
 z_\sigma(v)=-2\pi i\sigma r_0(v-1),\\
 M_\gamma(K,z)&=K^{\gamma-1}\zeta(1-\gamma)\Gamma(1-\gamma)z^{\gamma-1}
              +K^{-\gamma-1}\zeta(1+\gamma)z^{-1}.
 \end{split}
\]

最后一式在 gamma=0 取前文证明的可去值。前文已经证明
`g=mathcal M+mathcal E+E_0+E_pole`；这里不改变实际对偶余项
mathcal E，也不将它包含在以下主项误差中。

## 2. 简单极点的两条射线合计是精确常数

用正向环扇形，其下射线向外、上射线向内。被积函数
`W_u(v)/(v(v-1))` 在扇形内只有 v=1 的简单极点，留数为1。
内、外圆弧由 log-Gaussian 控制趋零，因此

\[
 \int_{L_{-\phi}}\frac{W_u(v)}{v-1}\frac{dv}{v}
 -\int_{L_{+\phi}}\frac{W_u(v)}{v-1}\frac{dv}{v}=2\pi i.
\]

因为 `z_sigma^(-1)=sigma i/(2 pi r_0(v-1))`，得到

\[
 \boxed{\sum_{\sigma=\pm1}\int_{L_{\sigma\phi}}
       W_u(v)z_\sigma(v)^{-1}\,\frac{dv}{v}=r_0^{-1}.}
 \tag{simple-exact}
\]

它不是单条射线各自等于一半的断言。

## 3. 分数次幂的精确 Gamma 商平均

对满足 `Re z>0, Re(z+gamma)<1, |gamma|<1/2` 的参数，定义

\[
 Q_\gamma(z)=\frac1{2\cos(\pi\gamma/2)}
 \left\{\frac{\Gamma(z)}{\Gamma(z+\gamma)}
       +\frac{\Gamma(1-z-\gamma)}{\Gamma(1-z)}\right\},
 \qquad Q_0(z)=1.
 \tag{Q-actual}
\]

Gamma 商在分母 Gamma 有极点时用整函数 `1/Gamma` 理解；实际
Conrey 参数中的四个 Gamma 自变量实部均为正，不需要此扩充。
定义

\[
 \mathcal H_\gamma(u,\Delta)
 =\frac1{\sqrt\pi\Delta}\int_{\mathbb R}
        e^{-t^2/\Delta^2}Q_\gamma(u+it)\,dt.
 \tag{H-actual}
\]

在当前参数内有精确恒等式

\[
 \boxed{\Gamma(1-\gamma)
 \sum_{\sigma=\pm1}\int_{L_{\sigma\phi}}
 W_u(v)z_\sigma(v)^{\gamma-1}\frac{dv}{v}
 =(2\pi)^\gamma r_0^{\gamma-1}\mathcal H_\gamma(u,\Delta).}
 \tag{fractional-exact}
\]

证明先取 `Re gamma>0`。逐条将射线移到正实轴的上、下边界。
v=1 附近绕开半径 epsilon 的小圆弧，其范数是
`O(epsilon^(Re gamma))`，故消失。零点与无穷远处仍用
log-Gaussian 消除圆弧。对实 v<1 和 v>1，两种分支相位分别是
`exp(+-i pi(gamma-1)/2)`，求和都等于 `2 sin(pi gamma/2)`。
于是去掉尺度 `(2pi r_0)^(gamma-1)` 后的两射线和为

\[
 2\sin(\pi\gamma/2)
 \left(\int_0^1+\int_1^\infty\right)
 v^{u-1}e^{-\Delta^2\log^2v/4}|v-1|^{\gamma-1}\,dv.
 \tag{boundary-sum}
\]

这里正实数 `|v-1|` 的复幂使用实对数。
代入真正的 Gaussian Fourier 恒等式

\[
 e^{-\Delta^2\log^2v/4}
 =\frac1{\sqrt\pi\Delta}\int_{\mathbb R}
    e^{-t^2/\Delta^2}v^{it}\,dt.
\]

本次 Fubini 是绝对的：取范数后 t 积分为归一化 Gaussian，
v 积分为
`int_0^infinity v^(Re u-1)|v-1|^(Re gamma-1) dv`，它在
`Re u>0, Re gamma>0, Re(u+gamma)<1` 时有限。
把无穷区间令 x=1/v，再分别用 beta 积分，得到

\[
 \left(\int_0^1+\int_1^\infty\right)
 v^{z-1}|v-1|^{\gamma-1}dv
 =\Gamma(\gamma)
 \left\{\frac{\Gamma(z)}{\Gamma(z+\gamma)}
       +\frac{\Gamma(1-z-\gamma)}{\Gamma(1-z)}\right\}.
\]

最后用
`Gamma(gamma) Gamma(1-gamma)=pi/sin(pi gamma)`，精确留下
`1/(2 cos(pi gamma/2))`，即 (fractional-exact)。

负实部及零移位不是通过不收敛的边界积分处理。第4节将给出
Gamma 商在竖向上的局部一致多项式界，所以 (H-actual) 全纯。
原射线因避开 v=1，积分也对移位全纯。对连通双圆盘
`|a|,|b|<4`，`Re u>1/3`、`Re(u+gamma)<2/3`、
`|gamma|<1/3`；由全纯恒等定理从 `Re gamma>0` 的开子集延拓。
因此 (fractional-exact) 包含负移位以及 gamma=0，后者也与
(simple-exact)、`mathcal H_0=1` 一致。

## 4. 带移位零因子的 Gamma 商估计

需要的不是一个含未知移位依赖常数的 `Gamma ratio ~ z^(-gamma)`。
我们保留 gamma=0 时误差严格为零这一事实。

### 4.1 从 Euler 求和给出 digamma 余项

对 `Re z>0`，digamma 级数等价于

\[
 \psi(z)=\lim_{N\to\infty}
 \left(\log N-\sum_{n=0}^{N-1}\frac1{n+z}\right).
\]

对 `f(x)=1/(x+z)` 作一次带端点的 Euler 求和，并取极限，得

\[
 \psi(z)=\operatorname{Log}z-\frac1{2z}
       +\int_0^\infty\frac{B_1(\{x\})}{(x+z)^2}\,dx,
 \qquad B_1(t)=t-\tfrac12.
 \tag{psi-remainder}
\]

该积分绝对收敛。因为 `|B_1|<=1/2`，当 `|Im z|>=1` 时

\[
 \int_0^\infty\frac{dx}{|x+z|^2}
 \le\int_0^\infty\frac{dx}{x^2+(\Im z)^2}
 =\frac\pi{2|\Im z|}.
\]

所以在任意实部有界、且留在右半平面的竖带内，
`psi(z)=Log z+O(1/|Im z|)`，常数可统一选择。
低高度部分则由紧性和 Gamma 在右半平面无零点给界。

### 4.2 对移位积分，而不是对估计猜测求导

沿 z 到 z+gamma 的线段，若全段在右半平面，有

\[
 \frac{\Gamma(z)}{\Gamma(z+\gamma)}
 =\exp\left(-\gamma\int_0^1\psi(z+q\gamma)\,dq\right).
 \tag{ratio-integral}
\]

在实际闭移位域以及下述大高度区间，整段实部至少1/8。
(psi-remainder) 和沿线段的 Log 差分给出

\[
 \frac{\Gamma(z)}{\Gamma(z+\gamma)}
 =z^{-\gamma}(1+\epsilon(z,\gamma)),\qquad
 |\epsilon(z,\gamma)|\le C\frac{|\gamma|}{|\Im z|}
 \quad(|\Im z|\ge2).
 \tag{ratio-uniform}
\]

使用 `|exp(v)-1|<=|v| exp(|v|)` 可直接得出此式；没有除以
gamma，也未丢掉分子中的 `|gamma|`。

对低高度紧集也用 (ratio-integral)。结合高高度的主值相位界，
得到对实际参数、全部实 t 的粗界

\[
 |Q_\gamma(u+it)-1|
 \le C|\gamma|(1+|w+t|)^{1/4}\log(2+|w+t|).
 \tag{Q-global}
\]

具体地，两个 Gamma 商分别写成 `exp(-gamma A)`，其中
`|A|<=C+log(2+|w+t|)`；再用上面的指数差分不等式，
给出右侧的四分之一次幂。分母余弦在 `|gamma|<=1/4` 上远离0，
且 `1/cos(pi gamma/2)-1=O(|gamma|^2)`。这也说明该界包含
gamma=0。对 `|a|,|b|<4` 的任意紧子双圆盘重复同一证明，
以稍大的固定幂次代替1/4，即得第3节需要的全纯积分支配。

## 5. Gaussian 平均的统一逼近

当 `|t|<=w/2`，写 `lambda=w+t>=w/2`。
两个 Gamma 商的分子参数分别是

\[
 z=\tfrac12-\beta+i\lambda,\qquad
 1-z-\gamma=\tfrac12-\alpha-i\lambda.
\]

用 (ratio-uniform)，再用
`Log z=log lambda+i pi/2+O(1/lambda)` 及第二个参数的
负相位式，精确的余弦分母给出

\[
 Q_\gamma(u+it)=\lambda^{-\gamma}(1+\epsilon_t),\qquad
 |\epsilon_t|\le C|\gamma|/\lambda.
 \tag{Q-central}
\]

沿正实区间对 `x^(-gamma)` 积分其导数，有

\[
 |\lambda^{-\gamma}-w^{-\gamma}|
 \le C|\gamma|w^{-\Re\gamma}|t|/w.
\]

以 `e^(-t^2/Delta^2)/(sqrt(pi) Delta)` 加权，使用其总质量1
和一阶绝对矩 `Delta/sqrt(pi)`，故中心区间贡献至多

\[
 C|\gamma|w^{-\Re\gamma}(1+\Delta)/w.
 \tag{H-central-error}
\]

尾区间保留相同移位因子。由 (Q-global) 及
`|w^(-gamma)-1|<=C |gamma| w^(1/4) log w`，在 `|t|>w/2`
有

\[
 |Q_\gamma(u+it)-w^{-\gamma}|
 \le C|\gamma|(1+|t|)^{1/2}.
\]

又有

\[
 e^{-t^2/\Delta^2}
 \le e^{-w^2/(8\Delta^2)}e^{-t^2/(2\Delta^2)},
\]

所以尾部 Gaussian 平均至多
`C |gamma| (1+Delta)^(1/2) exp(-w^2/(8 Delta^2))`。
因为实际 `|gamma|<=6/L`、`w<=2T`，有 `w^(-Re gamma)<=e^7`。
合计得到绝对常数 C 下的闭域一致界

\[
 \boxed{|\mathcal H_\gamma(u,\Delta)-w^{-\gamma}|
 \le C|\gamma|\left(T^{-\delta}
                  +T^{1/2}e^{-T^{2\delta}/8}\right).}
 \tag{H-uniform}
\]

记括号中的实函数为 `eta_delta(T)`。对每个固定 delta>0，
`eta_delta(T)=O_delta(T^(-delta))`：指数项用
`exp(x)>=x^n/n!`，选择 `2 delta n>=1/2+delta` 即可。

这一步没有逼近 `w` 为 `T`，没有令 phi 随 T 变化，也没有使用
待证 DI 估计。角度一致性来自精确核表达式。

## 6. 实际有限算术和与精确主项

定义两个实际有限和

\[
 \begin{split}
 S_+(\alpha,\beta)&=\sum_{h,k\le Y}
 \frac{c_1(h)c_2(k)d^{1+\gamma}}{h^{1+\beta}k^{1+\alpha}},\\
 S_-(\alpha,\beta)&=\sum_{h,k\le Y}
 \frac{c_1(h)c_2(k)d^{1-\gamma}}{h^{1-\alpha}k^{1-\beta}}.
 \end{split}
 \tag{S-finite}
\]

由 (simple-exact)、(fractional-exact) 和 `Kr_0=H`，逐项代数
化简，得到对 gamma!=0 的精确等式

\[
 \boxed{\mathcal M=\zeta(1+\gamma)S_+
       +(2\pi)^\gamma\mathcal H_\gamma(u,\Delta)
            \zeta(1-\gamma)S_-.}
 \tag{M-exact}
\]

例如分数次幂项的权重为
`k^(beta-1)h^(-beta)H^(gamma-1)
 =d^(1-gamma)h^(alpha-1)k^(beta-1)`，
简单极点项的权重为
`k^(beta-1)h^(-beta)H^(-1)K^(-gamma)`。
这两个权重给出 (S-finite)，没有省略 gcd 或互素化因子。

令实际算术主表达式

\[
 \mathcal A=\zeta(1+\gamma)S_+
       +(w/(2\pi))^{-\gamma}\zeta(1-\gamma)S_-.
 \tag{A-actual}
\]

它只是原来明确的有限算术和，不是新设的未知主项接口。
对任一 h,k，`S_-` 的权重是 `S_+` 的权重乘 `(HK)^gamma`，
所以其括号可写成

\[
 \zeta(1+\gamma)+(2\pi HK/w)^\gamma\zeta(1-\gamma).
\]

两个极点在 gamma=0 消去。若 gamma=0、beta=-alpha，则

\[
 \mathcal A=
 \sum_{h,k\le Y}c_1(h)c_2(k)\frac d{hk}(h/k)^\alpha
 \left[\log\frac{wd^2}{2\pi hk}+2\gamma_E\right].
 \tag{A-coalescent}
\]

因此 mathcal A 全纯于前述开双圆盘，不能把两份 zeta 单独在
gamma=0 评价。mathcal M 的全纯性已经证明，(M-exact) 也按
整体可去延拓在合流处理解。

## 7. 无 Y 幂次损失的主项误差

实际小移位使

\[
 |S_-|\le e^6B_1B_2\sum_{h,k\le Y}\frac{\gcd(h,k)}{hk}
 \le e^6B_1B_2(1+\log Y)^3.
 \tag{gcd-majorant}
\]

最后一步按 d=gcd(h,k) 分组，放宽互素限制后为
`sum_(d<=Y) d^(-1)(sum_(H<=Y/d) H^(-1))^2`，再用调和级数界。
此放宽只用于误差上界，没有改变 (S-finite) 中的实际有限和。

在 `|gamma|<=1/4` 上，`gamma zeta(1-gamma)` 按可去延拓一致
有界。因此 (H-uniform) 的 `|gamma|` 正好消除潜在极点损失：

\[
 \boxed{|\mathcal M-\mathcal A|
 \le C B_1B_2(1+\log Y)^3\eta_\delta(T)
 =O_\delta\!\left(B_1B_2(1+\log Y)^3T^{-\delta}\right).}
 \tag{M-uniform}
\]

先在 gamma!=0 证明，再用整体全纯性延拓到 gamma=0。
绝对常数 C 对全部允许 a,b,w,Y,phi 同时有效；大 O 中的常数
可以依赖固定 delta。这里没有 `1/|a+b|`，也没有 `Y^2` 损失。

## 8. 接回实际 g 与所需混合微分

结合 #510 的两个已关闭误差，定义实际差值
`R_main=mathcal M-mathcal A`，就有

\[
 \boxed{g=\mathcal A+\mathcal E+R_{\rm main}+E_0+E_{\rm pole}.}
 \tag{g-arithmetic}
\]

R_main 满足 (M-uniform)，另外两项满足 #510 的
`C B_1B_2 Y^2 log(2Y)/Delta * exp(-T^(2delta)/2)` 界。
所以对于固定 delta>0，完整已控误差统一为

\[
 g-\mathcal A-\mathcal E
 =O_\delta\!\left(B_1B_2(1+\log T)^3T^{-\delta}\right).
 \tag{g-controlled-error}
\]

mathcal E 是原实际对偶积分，仍未得到所需的长 mollifier
渐近误差界，绝不能从 (g-controlled-error) 中删除。

R_main 对 `|a|,|b|<4` 全纯，且 (M-uniform) 在
`|a|,|b|<=3` 一致成立。对既定算子
`mathcal D=(1+(51/50)partial_a)(1+(51/50)partial_b)`，
在 `a=b=-6/5` 周围取两份半径1/2的 Cauchy 圆，得到

\[
 |\mathcal D R_{\rm main}|_{a=b=-6/5}
 \le\frac{5776}{625}\,C B_1B_2(1+\log Y)^3\eta_\delta(T).
\]

另两份误差也已证明同样的 Cauchy 因子。因此实际 Gaussian
mollified 均方被化为 `mathcal D mathcal A+mathcal D mathcal E`
以及明确一致趋零的误差，而不是仅给出一个不能微分的逐点渐近。

## 9. 当前剩余工作与交付边界

本节在纸面上关闭 #510 所列的主项射线积分统一渐近，保留精确
有限算术和及零移位合流。同一检查点的
[profile 主项连接](2026-08-31-conrey-gaussian-profile-main-term.md)
进一步处理 (S-finite) 的算术渐近以及当前局部整数截断的归一化。
这些结论没有控制实际对偶余项。

下一步仍需要真正的对偶核/DI 估计、进一步 Fubini 与 dyadic
范围控制。其后仍有完整均方、全局去平滑及相应截断、简单零点
比例，以及本批数学的 Lean 原生化验证。
本节不宣称完整严格 Conrey >2/5 或独立 Selberg 路线已经完成。
