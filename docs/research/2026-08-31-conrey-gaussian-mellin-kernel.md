# Conrey Gaussian–Mellin 核：正阻尼、合法交换与去阻尼

这里给出实际 Gamma/余弦核的完整有限参数积分恒等式。关键是先加入
正阻尼，使双重积分绝对可积，再分别证明两侧在去阻尼时的可积支配。
这补齐真实 Gaussian/Estermann 分解之前的一个解析步骤，不假设任意
代理核，也不把最终均方主项或 Deshouillers–Iwaniec 估计作为输入。

这是纸面数学证明，尚无本核的新 Lean 实现或验证。既有有限轮廓契约
也仍待资源窗口；#500 的源 SHA `47c92840` 不变。

公式核对 [Conrey 1989, Lemma 3, p.14](https://aimath.org/~kaur/publications/24.pdf)
的渲染原页。这里明确只取实际应用所需的正实数 `y`，不沿用未指定
负实数幂分支的 `y != 0` 表述。下面给出自足推导，不引用该引理为假设。

## 1. 参数、幂分支和结论

固定实数 `1<c<2, Delta>0, y>0`，复数 `s_0,beta`，满足
`Re beta<c`。所有正实数底数的幂以实对数定义；其他复幂使用主值
`Log`。记 `e(x)=exp(2 pi i x)`，竖线向上，且

\[
 \chi(1-q)=2(2\pi)^{-q}\Gamma(q)\cos(\pi q/2).
\]

定义

\[
 J(y,s_0,\beta,\Delta)
 =\frac1{i\Delta\sqrt\pi}\int_{(c)}
 e^{(s-s_0)^2/\Delta^2}\chi(1-s+\beta)y^{-s}\,ds.
 \tag{J-def}
\]

要证明的实际等式为

\[
 \boxed{J=y^{-\beta}\int_0^\infty
 v^{s_0-\beta}e^{-\Delta^2\log^2v/4}
 \{e(-yv)+e(yv)\}\,\frac{dv}{v}.}
 \tag{J-kernel}
\]

两边均绝对可积。证明只使用 `c-Re beta>0`；保留原文的 `1<c<2`
以匹配后续应用，而不扩大本次交付范围。注意归一化为
`1/(i Delta sqrt(pi))`，不是逆 Mellin 常见的 `1/(2 pi i)`。

## 2. 复 Laplace 公式及其可积性

固定 `q`，令 `a=Re q>0`。当 `Re lambda>0` 时，

\[
 \int_0^\infty u^{q-1}e^{-\lambda u}\,du
 =\Gamma(q)\lambda^{-q}.
 \tag{Laplace}
\]

其绝对值由 `u^(a-1) exp(-(Re lambda)u)` 控制，原点因 `a>0`
可积，无穷远因指数衰减可积。为不暗中引用端点旋转，证明如下：

1. 正实数 `lambda` 时，由 Euler 积分及正实数伸缩直接得到公式。
2. 在任意右半平面点 `lambda_0` 的充分小邻域中，
   `Re lambda>=sigma=Re lambda_0/2>0`。积分及其 `lambda` 导数
   分别由 `u^(a-1) exp(-sigma u)`、`u^a exp(-sigma u)` 控制。
   因而左边对 `lambda` 全纯。右边也在该半平面全纯。
3. 两个全纯函数在正实轴相等，且正实轴在连通右半平面中有聚点；
   恒等定理给出整个右半平面的等式。

此外 Euler 积分直接给出，不需要 Stirling 公式：

\[
 |\Gamma(a+i\tau)|\le\Gamma(a)\qquad(a>0,\ \tau\in\mathbb R).
 \tag{Gamma-crude}
\]

此处右边是正实 Gamma 值。这个粗界与后面的高斯权合用已经足够。

## 3. 高斯逆 Mellin 恒等式

对任意 `x>0` 有

\[
 \frac1{i\Delta\sqrt\pi}\int_{(c)}
 e^{(s-s_0)^2/\Delta^2}x^s\,ds
 =x^{s_0}e^{-\Delta^2\log^2x/4}.
 \tag{Gaussian}
\]

写 `s_0=A+iB, s=c+it, d=c-A, ell=log x`，再取 `r=t-B`。
积分绝对可积，参数化后恰为

\[
 \frac{e^{d^2/\Delta^2+c\ell+iB\ell}}{\Delta\sqrt\pi}
 \int_{\mathbb R}e^{-r^2/\Delta^2}
 e^{ir(\ell+2d/\Delta^2)}\,dr.
\]

实高斯 Fourier 积分使积分部分等于
`Delta sqrt(pi) exp(-Delta^2 (ell+2d/Delta^2)^2/4)`。
展开平方后，指数为 `s_0 ell-Delta^2 ell^2/4`，得到 (Gaussian)。
这同时检查了全部 `i`、`2 pi`、`Delta` 和复中心的归一化。

## 4. 固定正阻尼后的绝对 Fubini

对 `epsilon>0` 定义 `lambda_+=epsilon+2 pi i`、
`lambda_-=epsilon-2 pi i`，并在 (J-def) 中将 `chi(1-s+beta)`
替换成

\[
 K_\varepsilon(s-\beta)
 =\Gamma(s-\beta)
   \{\lambda_+^{-(s-\beta)}+\lambda_-^{-(s-\beta)}\},
\]

得到 `J_epsilon`。令 `a=c-Re beta>0`。由 (Laplace)，对每个
`s=c+it`，两个加项对应 `u^(s-beta-1) exp(-epsilon u)e(-u)`
与 `u^(s-beta-1) exp(-epsilon u)e(u)` 的积分。

对每个符号，未除归一化因子的双重被积函数的绝对值恰为

\[
 y^{-c}e^{(c-A)^2/\Delta^2}
 e^{-(t-B)^2/\Delta^2}u^{a-1}e^{-\varepsilon u}.
\]

其 `dt du` 积分为

\[
 y^{-c}e^{(c-A)^2/\Delta^2}
 \Delta\sqrt\pi\,\Gamma(a)\varepsilon^{-a}<\infty.
 \tag{Fubini-bound}
\]

故此时 Fubini 完全合法。该界依赖 `epsilon`，只用于固定阻尼时的
交换，不用于 `epsilon -> 0`。交换后对 `x=u/y` 应用 (Gaussian)：

\[
 J_\varepsilon=\int_0^\infty
 u^{-\beta}(u/y)^{s_0}e^{-\Delta^2\log^2(u/y)/4}
 e^{-\varepsilon u}\{e(-u)+e(u)\}\,\frac{du}{u}.
\]

正实数代换 `u=yv` 得到

\[
 J_\varepsilon=y^{-\beta}\int_0^\infty
 v^{s_0-\beta}e^{-\Delta^2\log^2v/4}
 e^{-\varepsilon yv}\{e(-yv)+e(yv)\}\,\frac{dv}{v}.
 \tag{J-damped}
\]

特别地，`lambda_+` 给负相位，`lambda_-` 给正相位。

## 5. 核侧的去阻尼与绝对界

令 `H=Re(s_0-beta)`。因为 `epsilon,y,v>0`，(J-damped) 的
被积函数（相对于 `dv`）由不依赖 `epsilon` 的函数

\[
 2y^{-\Re\beta}v^{H-1}e^{-\Delta^2\log^2v/4}
\]

控制。代换 `x=log v` 并配方：

\[
 \int_{\mathbb R}e^{Hx-\Delta^2x^2/4}\,dx
 =\frac{2\sqrt\pi}{\Delta}e^{H^2/\Delta^2}<\infty.
\]

故控制收敛使右边趋向 (J-kernel) 的右边，并给出

\[
 |\text{右边}|\le
 \frac{4\sqrt\pi}{\Delta}y^{-\Re\beta}
 e^{(\Re(s_0-\beta))^2/\Delta^2}.
 \tag{J-absolute}
\]

这里两个相位贡献的因子 `2` 已包含在 `4 sqrt(pi)/Delta` 中。

## 6. 竖线侧的去阻尼：高斯压过指数线性增长

在 `s=c+it` 上写 `q=s-beta=a+i tau`，其中
`tau=t-Im beta`。主值幂满足

\[
 |\lambda_\pm^{-q}|
 =|\lambda_\pm|^{-a}e^{\tau\arg\lambda_\pm}
 \le(2\pi)^{-a}e^{\pi|t-\Im\beta|/2}.
\]

这是因为 `a>0`、`|lambda_+/-|>=2 pi` 及
`|arg lambda_+/-|<pi/2`。结合 (Gamma-crude)，归一化后的竖线
被积函数在所有 `epsilon>0` 下一致由

\[
 \frac{2y^{-c}\Gamma(a)(2\pi)^{-a}}{\Delta\sqrt\pi}
 e^{(c-A)^2/\Delta^2}
 e^{-(t-B)^2/\Delta^2+(\pi/2)|t-\Im\beta|}
 \tag{line-majorant}
\]

控制。此函数可积：令 `r=t-B`，用
`|t-Im beta|<=|r|+|B-Im beta|`，并在 `r>=0` 与 `r<=0`
分别配方，二次负指数控制一次正指数。

当 `epsilon -> 0+` 时，`lambda_+/- -> +/-2 pi i`，极限点
均避开主值 `Log` 的支割线。逐点有

\[
 K_\varepsilon(q)\longrightarrow
 \Gamma(q)(2\pi)^{-q}
 \{e^{-i\pi q/2}+e^{i\pi q/2}\}
 =2(2\pi)^{-q}\Gamma(q)\cos(\pi q/2)=\chi(1-q).
\]

因此控制收敛使左边趋向 (J-def)，同时证明 (J-def) 绝对可积。
结合第5节即证 (J-kernel)。此证明没有移动 `s` 轮廓，不产生留数，
也没有在边界 `arg lambda=+/-pi/2` 直接使用绝对 Laplace 积分。

## 7. 后续使用边界与原生化清单

本结论是实际核恒等式，覆盖所需复移位、复高斯中心及任意固定
正 `Delta,y`。但必须区分下列三件事：

- 两侧单个核均绝对可积；未经阻尼的 `u,t` 双重积分一般并不绝对
  可积，因为其绝对值包含无衰减的 `u^(a-1)`。不能省略第4–6节。
- (J-absolute) 丢失竖线的 `y^(-c)` 衰减。它本身不允许把后续
  无限 `m,n` Dirichlet 求和移进实轴 `v` 积分；有限 `h,k` 求和
  无此问题。实际 Estermann 分解需要另做射线旋转及求和支配。
- 本结论没有证明长均方主项、其统一移位误差、DI 谱估计、去平滑
  或最终简单零点比例。因此不能据此宣布 Conrey `>2/5` 已完成。

现有源码可复用部分（本次只读，未启动 Lean）：

1. `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean` 的
   `Complex.Gamma_eq_integral` 和
   `integral_cpow_mul_exp_neg_mul_Ioi` 已给 Euler 积分和正实数
   Laplace 系数；复系数半平面的局部可积导数及恒等定理仍需连接。
2. `Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean`
   已有复高斯积分；应用需明确转换成第3节的归一化。
3. `HardyTheorem/SelbergComplexGaussianMellin.lean` 中已有严格开角
   `phi<pi/2` 的旋转 Mellin 等式；不可直接当作端点 `phi=pi/2`
   结果。本证明采用正阻尼和高斯支配，端点处理独立列明。
4. 新的原生证明必须落实固定阻尼 Fubini、两侧各自的控制收敛、
   正实数代换和精确相位，不能以一个假设 `J-kernel` 的接口代替。

资源窗口放行后先验收已有有限轮廓交付，再按数学依赖推进本核。
