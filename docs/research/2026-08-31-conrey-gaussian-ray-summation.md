# Conrey 双相位核：射线旋转与无限求和的合法交换

本节接续 [Gaussian–Mellin 核证明](2026-08-31-conrey-gaussian-mellin-kernel.md)，
证明其在真实 `m,n` 双重 Dirichlet 求和中的下一步：先逐项旋转相位，
然后在正确半平面的射线上利用指数衰减建立绝对 Fubini。
这是固定参数的实际恒等式，不假设 Estermann 展开或谱估计。

核对来源是 [Conrey 1989, pp.17–18，式 (55) 前后](https://aimath.org/~kaur/publications/24.pdf)。
本证明不引用其中未重新推导的 `o_delta(1)`，也不声称完成从实际
`g` 移线至 `c` 的留数估计。本节尚未原生化到 Lean。

## 1. 单相位核及旋转方向

固定 `Delta>0, rho>0, 0<phi<pi/2`，复数 `z`。对
`sigma` 取 `+1` 或 `-1`，令

\[
 F_\sigma(v)=v^z e^{-\Delta^2(\operatorname{Log}v)^2/4}
 e(\sigma\rho v),\qquad e(w)=\exp(2\pi i w).
\]

所有复幂使用主值对数。记 `L_(sigma phi)` 为从原点向外的射线
`v=r exp(i sigma phi), r>0`。有精确恒等式

\[
 \int_0^\infty F_\sigma(v)\frac{dv}{v}
 =\int_{L_{\sigma\phi}}F_\sigma(v)\frac{dv}{v}.
 \tag{rotate}
\]

证明取截断环扇形 `epsilon<=|v|<=R`，角度在 `0` 与
`sigma phi` 之间。其邻域避开原点和主值支割线，`F_sigma(v)/v`
全纯。对其中 `v=r exp(i theta)`，因为 `sigma sin(theta)>=0`，

\[
 |e(\sigma\rho v)|=e^{-2\pi\sigma\rho r\sin\theta}\le1.
\]

记 `h=Re z`、`b=Im z`。在任一半径为 `r` 的圆弧上，

\[
 |F_\sigma(v)|\le
 r^h\exp\!\left(|b|\phi+\Delta^2\phi^2/4
                         -\Delta^2\log^2r/4\right).
\]

圆弧积分的范数至多是右边乘 `phi`，因为 `|dv/v|=|d theta|`。
当 `r->0+` 或 `r->infinity` 时它都趋于零：在 `x=log r`
下，`h x-Delta^2 x^2/4 -> -infinity`。实轴与射线积分的绝对
可积性也由同一 log-Gaussian 界得到。对截断轮廓使用 Cauchy 定理
再取两端极限，即得 (rotate)。两个射线都向外定向，负相位没有
额外负号。

更精确地，在射线上有

\[
 |F_\sigma(r e^{i\sigma\phi})|
 =A_\sigma r^h e^{-\Delta^2\log^2r/4}
 e^{-2\pi\rho r\sin\phi},\quad
 A_\sigma=\exp(-\sigma\phi b+\Delta^2\phi^2/4).
 \tag{ray-norm}
\]

参数化时 `dv/v=dr/r`；`v^z` 的相位因子已包含在 `A_sigma`
中，不可再另乘伸缩 Jacobian。

## 2. 双重级数的可积支配

现在固定 `r_0>0`，复数 `gamma`，记 `p=Re gamma`，并在第1节
逐项取 `rho=m n r_0`，`m,n>=1`。令

\[
 a_0=2\pi r_0\sin\phi>0.
\]

任选实数 `q>max(1,1-p)`。实函数 `x^q e^{-x}` 在正半轴的
最大值为 `C_q=(q/e)^q`，故

\[
 \sum_{m,n\ge1}m^{-p}e^{-a_0mnr}
 \le C_q a_0^{-q}r^{-q}
       \Bigl(\sum_{m\ge1}m^{-(p+q)}\Bigr)
       \Bigl(\sum_{n\ge1}n^{-q}\Bigr)
 =C_q a_0^{-q}r^{-q}\zeta(p+q)\zeta(q).
 \tag{double-majorant}
\]

两个实正值 zeta 因子这里只是收敛的 p 级数，因为 `p+q>1,q>1`。
本界适用于每个 `r>0`；可以先对有限部分和取界再单调取极限。

由 (ray-norm) 与 (double-majorant)，

\[
 \begin{aligned}
 &\sum_{m,n\ge1}\int_0^\infty
 \left|m^{-\gamma}(r e^{i\sigma\phi})^z
 e^{-\Delta^2(\log r+i\sigma\phi)^2/4}
 e(\sigma mnr_0r e^{i\sigma\phi})\right|\frac{dr}{r}\\
 &\quad\le
 A_\sigma C_q a_0^{-q}\zeta(p+q)\zeta(q)
 \frac{2\sqrt\pi}{\Delta}
 \exp\!\left((h-q)^2/\Delta^2\right)<\infty.
 \end{aligned}
 \tag{absolute-Fubini}
\]

最后一步再次用 `x=log r` 的实高斯积分。由此严格得到

\[
 \begin{aligned}
 &\sum_{m,n\ge1}m^{-\gamma}
 \int_0^\infty v^z e^{-\Delta^2\log^2v/4}
 e(\sigma mnr_0v)\frac{dv}{v}\\
 &=\int_{L_{\sigma\phi}}v^z e^{-\Delta^2(\operatorname{Log}v)^2/4}
 \left(\sum_{m,n\ge1}m^{-\gamma}e(\sigma mnr_0v)\right)\frac{dv}{v}.
 \end{aligned}
 \tag{sum-rotate}
\]

解释次序很重要：每一项先由 (rotate) 等于射线积分；
(absolute-Fubini) 再证明这些积分构成的级数绝对收敛，并允许在
射线上交换积分与级数。这里**没有**声称实轴的双重级数被积函数
绝对可积，也没有在实轴上交换无限求和。

## 3. 和实际 J 级数对接：检查 n 的幂和外因子

取固定正整数 `h_0,k_0`，令 `r_0=h_0/k_0`，以及复数
`alpha,beta,s_0`。令 `z=s_0-beta, gamma=alpha+beta`。
在核证明的条件 `1<c<2, Re beta<c` 下，逐项 (J-kernel) 给出

\[
 m^{-\alpha}n^{\beta}J(mnr_0,s_0,\beta,\Delta)
 =r_0^{-\beta}m^{-(\alpha+\beta)}
 \int_0^\infty v^{s_0-\beta}e^{-\Delta^2\log^2v/4}
 \{e(mnr_0v)+e(-mnr_0v)\}\frac{dv}{v}.
 \tag{term-match}
\]

这里第一行必须是 `n^beta`，不是 `n^(-beta)`：它来自函数方程后
`zeta(s-beta)` 的 Dirichlet 级数，并且恰与 `(mn)^(-beta)`
中的 `n^(-beta)` 抵消。结合 (sum-rotate) 得到

\[
 \boxed{\begin{aligned}
 &\sum_{m,n\ge1}m^{-\alpha}n^\beta J(mnr_0,s_0,\beta,\Delta)\\
 &=r_0^{-\beta}\sum_{\sigma=\pm1}
 \int_{L_{\sigma\phi}}v^{s_0-\beta}
 e^{-\Delta^2(\operatorname{Log}v)^2/4}
 \left(\sum_{m,n\ge1}m^{-(\alpha+\beta)}
 e(\sigma mnr_0v)\right)\frac{dv}{v}.
 \end{aligned}}
 \tag{J-series}
\]

两侧所显示的级数均按上述论证绝对收敛。有限外层 `h_0,k_0`
求和可再直接相加。特别地，若原系数为 `b(h_0)b(k_0)/k_0`，
乘 `r_0^(-beta)` 后即是
`b(h_0)b(k_0)/(k_0^(1-beta) h_0^beta)`，与原文对应。

如果还要从 `Re s=c` 的竖线积分直接展开双重 Dirichlet 级数，
一个充分条件是 `c+Re alpha>1` 且 `c-Re beta>1`。
此时绝对值中的两级数为 `sum m^(-c-Re alpha)` 与
`sum n^(-c+Re beta)`，可与核文第6节的高斯可积界相乘。
这是竖线上交换所需的额外条件；不能把核引理仅有的
`c-Re beta>0` 偷换成 zeta 的绝对收敛条件。

## 4. 精确交付边界

已在纸面证明的是从实际单核到双射线双重级数的精确恒等式，以及
每一次交换的绝对可积依据。没有把级数命名为抽象函数再假设分解。
本节也没有使用或改动 #500 的冻结左边界源树。

实际 Estermann 变换、极点主项及余项的逐点分解，已在后续
[归一化证明](2026-08-31-conrey-estermann-normalization.md) 中补齐纸面推导。
尚未完成的步骤包括：

- 从实际 `g` 移动 `s` 竖线时的全部解析性、留数及统一误差；
- 整条 Gaussian 射线上主项、常数项及余项的分项积分与统一评价；
- 适用于所选长 mollifier 的核估计和 DI 谱估计；
- 最终统一移位均方、去平滑、整数截断归一化及简单零点比例。

尤其 (absolute-Fubini) 的常数含
`exp(-sigma phi Im z+Delta^2 phi^2/4)` 与 `sin(phi)^(-q)`。
这只是固定参数收敛证明；不可将其宣称为当 `T` 趋于无穷时足够小
的误差，也未证明可取 `phi->0` 后交换无限求和。
