# 固定参数半段上的真实 Conrey V1 均方

先说结论：不改变整数 cutoff、移位或 mollifier，在 `[T/2,T]`
上可以直接把已证 Gaussian 均方转成真实 `V1 B` 的均方。
这一局部结论不需要固定全局 mollifier 在低高度的积分估计。

本文基于源 SHA `5b1a00fb1f9f97fbced093ded4b4d6f89164ba9e` 的
[实际 DI 余项证明](2026-08-31-conrey-actual-di-remainder.md)及其上游。
它沿用其中明确列出的已发表 DI84 Lemma 1 和经典 Weil 定理，
没有独立重证这些深输入，也没有新增或执行 Lean 证明。
以下是这些输入下的纸面推导，不是新的条件接口。

## 1. 全部函数使用同一个 T

固定

\[
 L=\log T,\quad \theta=571/1000,\quad Y=\lfloor T^\theta\rfloor,
 \quad R=6/5,\quad k=51/50,\quad\sigma_0=1/2-R/L,
 \quad P(x)=(84x+15x^3+x^5)/100.
\]

令 `b(n)=mu(n) P(log(Y/n)/log Y)`，定义

\[
 \mathcal B_Y(s)=\sum_{1\le n\le Y}b(n)n^{-s},\qquad
 B_T(s)=\sum_{1\le n\le Y}b(n)n^{\sigma_0-1/2-s},
 \qquad V_T(s)=\zeta(s)+(k/L)\zeta'(s).
\]

因此逐项有 `B_T(sigma_0+it)=mathcal B_Y(1/2+it)`。
原生对象分别是 `conreyMollifier Y sigma0 conreyExplicitP` 和
`conreyExplicitV L`，没有用另一个高度重新定义系数。

另取原生 `conreyH`，并令

\[
 V_{1,T}(s)=\frac{49}{100}\zeta(s)
       +\frac{k}{L}\left(\zeta'(s)+\frac{H'(s)}{H(s)}\zeta(s)\right),
 \qquad H(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2).
 \tag{V1-actual}
\]

这是 `conreyDegreeOneV1 (49/100) 0 (51/50) L`，在本文矩形上
`H` 解析且非零。`49/100+k/2=1` 是下一步的精确归一化。

## 2. Gaussian 中心从 [T,2T] 扩展到 [T/2,T]

这一步不是将旧定理的 T 换成 T/2。仍取原来的
`Delta=T^(1-delta)`、射线角 `phi=1/T`、`L=log T`、Y 和移位域。
只将中心 w 的允许范围改为 `[T/2,T]`。逐项检查如下。

1. [Gaussian 求导](2026-08-31-conrey-gaussian-differentiation.md)
   的定义和微分恒等式对任意实 w 成立。紧中心区间的统一支配可直接
   用于 `[T/2,T]`，无需修改实际被积函数。
2. [常数项](2026-08-31-conrey-estermann-constant-term.md)及
   [移线极点](2026-08-31-conrey-gaussian-contour-decomposition.md)
   的精确公式不变。原先 `|Im u|>=T-1/4` 改成
   `|Im u|>=T/2-1/4`。当 T>=8、`|Re u|<=3/4` 时，
   `Re(u^2)<=-T^2/8`；极点处同理。因此两份误差分别仍不超过
   `C Y^2 log(2Y)/Delta`、`C Y log(2Y)/Delta` 乘
   `exp(-T^(2delta)/8)`，依旧比任意固定负幂小。
3. [主项 Gamma 商](2026-08-31-conrey-gaussian-main-term-evaluation.md)
   的中心区仍取 `|t|<=w/2`。此时 `w+t>=T/4`，故商的相对误差
   和幂函数差分中 `1/w` 至多改为 `2/T`。尾部的
   `exp(-w^2/(8Delta^2))` 现在不超过 `exp(-T^(2delta)/32)`。
   误差仍带有完整 `|gamma|` 因子，因而不破坏 zeta 极点的抵消。
4. [算术主项](2026-08-31-conrey-gaussian-profile-main-term.md)
   的有限 gcd 和根本不依赖 w。所用
   `log(w/(2pi T))` 在 `[1/2,1]` 的比值范围仍一致有界；于是
   `(w/(2pi))^(-(a+b)/L)=exp(-a-b)(1+O(1/L))`，
   与同一整数 Y 的归一化误差均不变。
5. [真实核界](2026-08-31-conrey-dual-kernel-fubini.md)中，w
   只进入角度因子 `exp(-sigma phi Im u+Delta^2 phi^2/4)`。
   `|phi Im u|<=2+O(1/T)` 仍成立，其余径向估计和选线
   `UV>=TN` 不变。有限移线的四相位留数仍逐块精确抵消；
   单独估计留数时，上述快速衰减常数改为1/8即可。
6. 实际 Type I/DI 算术块、全部硬 cutoff、gcd 层和系数范数都
   不含 w。故实际 E 及其 Cauchy 导数沿用原来完全相同的幂预算。

这些检查同时保留了固定复移位邻域上的一致性。
特别地没有要求 `Y<=(T/2)^theta`；算术证明中的尺度一直是 T。
选定足够小的固定正 `delta,eta,epsilon` 后，DI 余项仍为 o(1)。

记

\[
 F_T(t)=|V_T(\sigma_0+it)B_T(\sigma_0+it)|^2,
 \quad Z_T(t)=|\zeta(\sigma_0+it)B_T(\sigma_0+it)|^2,
 \quad\phi_\Delta(x)=\frac{e^{-x^2/\Delta^2}}{\Delta\sqrt\pi}.
\]

于是存在同一个 `e_T>=0`、`e_T->0`，使对全部 `w in [T/2,T]`：

\[
 |\!\int_{\mathbb R}F_T(t)\phi_\Delta(t-w)dt-\mathfrak C|\le e_T,
 \qquad
 |\!\int_{\mathbb R}Z_T(t)\phi_\Delta(t-w)dt-\mathfrak C_0|\le e_T.
 \tag{two-Gaussian-means}
\]

第一常数是已选 `conreyExplicitMeanSquareIntegral`。
第二式不是另加一个 Q=1 均方假设：直接将已经控制了真实 E 的
移位 Gaussian 恒等式在 `a=b=-R` 求值，不作移位微分，即得

\[
 \mathfrak C_0=1+\theta^{-1}\int_0^1\!\int_0^1
 e^{2Ry}[P'(x)+R\theta P(x)]^2\,dx\,dy<\infty.
 \tag{C0-actual}
\]

## 3. 同时去平滑两个真实平方

[端点核去平滑引理](2026-08-31-conrey-dyadic-desmoothing.md)
适用于任意 a<b，取 `a=T/2,b=T`。对 `F_T,Z_T` 分别使用
(two-Gaussian-means)，其积分误差均为 `O(Delta)+o(T)`。
`Delta/T->0`，所以

\[
 \frac2T\int_{T/2}^T F_T(t)dt=\mathfrak C+o(1),\qquad
 \frac2T\int_{T/2}^T Z_T(t)dt=\mathfrak C_0+o(1).
 \tag{two-local-means}
\]

不需要估计丢失单位区间上的点态峰值，也没有未知的低高度尾项。

## 4. 真实 V1 与 V 的局部 L2 差

由 (V1-actual) 直接相减，得到

\[
 (V_{1,T}-V_T)(s)B_T(s)
 =\frac{k}{L}\left(\frac{H'(s)}{H(s)}-\frac L2\right)\zeta(s)B_T(s).
 \tag{same-function-difference}
\]

已有 `ConreyShiftedH` 的真实复范数界，在 `0<sigma_0<=1/2,t>=3` 上给出

\[
 \left|\frac{H'}H(\sigma_0+it)-\frac12\log\frac{t}{2\pi}\right|\le10.
\]

在 `[T/2,T]` 上，`|log t-L|<=log 2`。因此令固定常数
`K=k(10+(log 2+|log(2pi)|)/2)`，有

\[
 |(V_{1,T}-V_T)B_T|(\sigma_0+it)\le(K/L)\sqrt{Z_T(t)}.
 \tag{local-pointwise-difference}
\]

这也等于已有 `ConreyV1Approximation` 取
`a=1-log(2)/L` 的结果；允许 a 随 L 变化，因为该有限不等式对
每个合规 a 都成立。它不是先固定 a 再交换两个未获一致性的极限。

积分 (local-pointwise-difference) 的平方，并用 (two-local-means)，
得到差的 L2 范数平方 `O(T/L^2)`。令 `X=V_T B_T`、
`D=(V_{1,T}-V_T)B_T`，对真实恒等式
`|X+D|^2-|X|^2=2 Re(X conjugate(D))+|D|^2` 积分并用 Cauchy：

\[
 \left|\int_{T/2}^T|V_{1,T}B_T|^2dt-\int_{T/2}^T|V_TB_T|^2dt\right|
 \le2\|X\|_2\|D\|_2+\|D\|_2^2=O(T/L).
\]

所有乘积沿同一条 `sigma_0+it` 取值；区间可积性来自解析性和
有限多项式，也由已有实际均方模块保证。因此

\[
 \boxed{\frac2T\int_{T/2}^T
 |V_{1,T}(\sigma_0+it)B_T(\sigma_0+it)|^2dt=\mathfrak C+o(1).}
 \tag{V1-half-interval-mean}
\]

这是本节新增的真实均方结论。固定全局 `B_T` 在 `[0,T]` 上的
均方仍未由此证明；[局部计数后求和](2026-08-31-conrey-local-simple-count.md)
会说明最终比例为何可以不依赖那个额外命题。
