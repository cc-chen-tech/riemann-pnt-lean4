# Conrey 实际 Gaussian 均方到同一 mollifier 的 dyadic 区间均方

本节证明一个直接的非负积分去平滑引理，并用于同一参数 T、
同一整数 Y、同一 mollifier 的实际均方。它只需要 Gaussian
均方的两个端点值，不需要另外证明未平滑 integrand 的点态小界。

结合本检查点中明确引用 DI/Weil 定理的
[实际对偶余项证明](2026-08-31-conrey-actual-di-remainder.md)，
得到同一函数在[T,2T]上的纸面均方渐近。
本文不将其误认成固定全局 mollifier 在[0,T]上的均方；
后者以及整条链的原生 Lean 验证仍需实际处理。

## 1. 一般的非负 Gaussian 平滑

固定 Delta>0，定义归一化实 Gaussian 核

\[
 \phi_\Delta(x)=\frac1{\Delta\sqrt\pi}e^{-x^2/\Delta^2},
 \qquad\int_{\mathbb R}\phi_\Delta(x)dx=1.
\]

令 F:R->[0,infinity) 可测，a<b 为实数。设

\[
 G(w)=\int_{\mathbb R}F(t)\phi_\Delta(t-w)dt,
 \qquad K_{a,b}(t)=\int_a^b\phi_\Delta(t-w)dw.
\]

假设 G(a)、G(b) 有限且 G 在[a,b]上可积。所有被积函数非负，
因此 Tonelli 定理无需预先假设 F 在整条实线上可积，即给出

\[
 \int_a^bG(w)dw=\int_{\mathbb R}F(t)K_{a,b}(t)dt<\infty.
 \tag{smoothed-interval}
\]

## 2. 示性函数误差由两个端点核支配

对 x>=0，直接换元 r=x+y 并用 `(x+y)^2>=x^2+y^2`，得到

\[
 \int_x^\infty\phi_\Delta(r)dr
 \le e^{-x^2/\Delta^2}\int_0^\infty\phi_\Delta(y)dy
 =\frac{\Delta\sqrt\pi}{2}\phi_\Delta(x).
 \tag{tail-endpoint}
\]

若 a<=t<=b，则 `1-K_(a,b)(t)` 是分别越过 a,b 的两个 Gaussian
尾质量之和；若 t<a 或 t>b，则 K_(a,b)(t) 不超过最近端点的
外侧尾质量。利用核的偶性，三种情况共同给出

\[
 \boxed{|\boldsymbol1_{[a,b]}(t)-K_{a,b}(t)|
 \le\frac{\Delta\sqrt\pi}{2}
 [\phi_\Delta(t-a)+\phi_\Delta(t-b)].}
 \tag{indicator-bound}
\]

闭区间端点的取值也满足该式；改变两个点的示性值不影响积分。
右侧乘以 F 后可积，因为 G(a)、G(b) 有限。
结合 (smoothed-interval)，先得 F 在[a,b]上可积，再取积分差，得到

\[
 \boxed{\left|\int_a^bF(t)dt-\int_a^bG(w)dw\right|
 \le\frac{\Delta\sqrt\pi}{2}[G(a)+G(b)].}
 \tag{desmooth-endpoints}
\]

这是真实不等式，不以未知未平滑积分作为右侧输入。
不需要在区间外截断 F，也没有留下另一个待估的 Gaussian 尾。

## 3. 应用到同一 T 的真实 Conrey integrand

取已经固定的参数

\[
 \theta=571/1000,\quad R=6/5,\quad k=51/50,\quad
 L=\log T,\quad Y=\lfloor T^\theta\rfloor,
 \quad\sigma_0=1/2-R/L,
 \quad P(x)=(84x+15x^3+x^5)/100.
\]

定义同一个有限多项式

\[
 \mathcal B_Y(s)=\sum_{n\le Y}\mu(n)
 P\!\left(\frac{\log(Y/n)}{\log Y}\right)n^{-s},
\]

和同一个实际非负函数

\[
 F_T(t)=\left|\left(\zeta(\sigma_0+it)+\frac{k}{L}\zeta'(\sigma_0+it)\right)
 \mathcal B_Y(1/2+it)\right|^2.
 \tag{F-actual}
\]

参数 T 在这里固定，t、w 只是积分变量。特别地不能将 Y 改成
`floor(w^theta)`，也不能把 L 换成 log w。
有限 mollifier 和避开极点的实际 zeta 给出可测性；此前
[Gaussian 求导证明](2026-08-31-conrey-gaussian-differentiation.md)
已经证明全高度多项式增长与 Gaussian 支配，故所需 G_T(w) 都有限。

取固定且足够小的 delta>0、`Delta=T^(1-delta)`。
本检查点的实际算术/核证明与 #512 的主项接合给出

\[
 \sup_{T\le w\le2T}|G_T(w)-\mathfrak C|\le e_T,
 \qquad e_T\longrightarrow0,
 \tag{Gaussian-uniform}
\]

其中

\[
 G_T(w)=\int_{\mathbb R}F_T(t)\phi_\Delta(t-w)dt,
\]

而 mathfrak C 是既有 `conreyExplicitMeanSquareIntegral` 的同一个
实际双积分。这里的 (Gaussian-uniform) 来自本检查点引用 DI 与
Weil 定理后对真实 E 的估计，不是额外假设一个抽象均方输入。

将 (desmooth-endpoints) 用于 a=T、b=2T，得到定量不等式

\[
 \left|\frac1T\int_T^{2T}F_T(t)dt-\mathfrak C\right|
 \le e_T+\sqrt\pi\frac\Delta T(\mathfrak C+e_T).
 \tag{dyadic-mean-error}
\]

因 `Delta/T=T^(-delta)->0`，结论是

\[
 \boxed{\frac1T\int_T^{2T}
 \left|\left(\zeta(\sigma_0+it)+(k/L)\zeta'(\sigma_0+it)\right)
 \mathcal B_Y(1/2+it)\right|^2dt=\mathfrak C+o(1).}
 \tag{dyadic-mean-actual}
\]

这是未平滑的真实 dyadic 区间均方，使用的 profile、整数截断、
移位和微分系数均与 Gaussian 结论完全相同。

## 4. 没有自动获得的全局结论

全局计数链若要求 `int_0^T F_T`，不能将上式对 dyadic 尺度
直接相加：把参数 T 换成 T/2，会同时改变 Y、L、sigma_0 和
mollifier 系数，因而改变被积函数。

下一步必须证明固定全局参数下的低高度控制与分块转移，或把
零点计数链准确局部化到可使用 (dyadic-mean-actual) 的区间；
具体哪种实现能接入现有计数模块，需要实际审计而非改名。
DI、Weil 及这些纸面步骤的自证/原生 Lean 验证仍未完成，
最终严格 >2/5 的简单临界线零点比例也仍不能宣布。
