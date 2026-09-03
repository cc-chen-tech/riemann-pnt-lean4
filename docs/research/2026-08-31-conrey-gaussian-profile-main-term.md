# Conrey 实际主项接回既定 profile：有限算术和、整数截断与混合微分

本节将新得到的实际 Gaussian 主项与已有纸面算术证明接合。
结论是实际移位积分等于既定显式 profile 主项、原来的实际对偶
余项，以及一致趋零的误差。**对偶余项尚未控制，故完整均方
渐近和 Conrey 严格 >2/5 定理仍未完成。**

这里不增加条件接口；直接使用前面已给出的有限轮廓/Volterra
证明和外层卷积论证，并核对新的整数截断是否满足其全部参数。
这是纸面数学后续，没有新增已验证 Lean 定理。

## 1. 固定同一个实际 mollifier 和参数邻域

取

\[
 \theta_0=571/1000,\qquad R=6/5,\qquad k=51/50,
 \quad L=\log T,\quad Y=\lfloor T^{\theta_0}\rfloor,
 \quad H_Y=\log Y,\quad \theta_Y=H_Y/L.
\]

T 足够大，Y>=2。仍用实际整数 mollifier 系数

\[
 c_j(n)=\mu(n)P_j\!\left(\frac{\log(Y/n)}{\log Y}\right)
 \quad(1\le n\le Y),
\]

其中 P_j 为固定实多项式、`P_j(0)=0`。
取闭双圆盘

\[
 \mathscr D_-:\ |a+R|,|b+R|\le21/40,
 \qquad \mathscr D_+:\ |a-R|,|b-R|\le21/40.
\]

实际移位 `alpha=a/L, beta=b/L`。这是已有算术证明的两个邻域。
注意

\[
 \theta_Y\le\theta_0,\qquad
 \theta_0(R+21/40)=39399/40000<1.
\]

因而全域上 `|alpha|,|beta|<1/H_Y`，且两个移位各自远离0。
在负双圆盘上还有 `|a+b|>=27/20`。
同时 `|a|,|b|<=69/40<3`，故新 Gaussian 主项证明的所有一致界
在这里适用。取 `Delta=T^(1-delta)`，`0<delta<1` 固定，
高度范围仍为 `T<=w<=2T`。

## 2. 算术渐近对整数 Y 的实际适用性

令实际有限和

\[
 \Sigma_Y(\xi,\eta)=\sum_{h,k\le Y}
 \frac{c_1(h)c_2(k)\gcd(h,k)^{1+\xi+\eta}}
      {h^{1+\xi}k^{1+\eta}}.
\]

[有限轮廓与 Volterra 证明](2026-08-31-conrey-finite-contour-assembly.md)
对任意 `H>=H_0, |xi|<=1/H, 1<=X<=exp H` 给出真实内层和

\[
 G_{j,d}(\xi)=
 \frac{\xi P_j(t_d)+P_j'(t_d)/H}{F(d,1+\xi)}
 +O_{P_j}\!\left(B_d[H^{-2}\ell^2+H^{-1}\ell X^{-b_0}]\right),
\]

其中 `ell=log H, X=Y/d, t_d=log X/H`，
`b_0=kappa/(16ell)>0`，`B_d=prod_(p|d)(1+p^(-(1-2/ell)))`。
统一常数先于 d、X、xi 选择，且包含 X=1 和整数端点。
现在取 `H=H_Y`，便有 `Y=exp H_Y` **精确成立**，而不是
将实数 y 的 profile 与整数 Y 的 profile 误认成相等。

这份内层误差不大于原算术证明使用的
`O(B_d H^(-2) ell^2 [1+H(d/Y)^b_0])`。
[算术主项证明](2026-08-30-conrey-arithmetic-main-term-proof.md)
中的精确 Möbius/gcd 分解、卷积平均、Euler 因子双移位抵消以及
边界层加权和，均只使用 H、`Y=exp H` 和 `|xi|,|eta|<=1/H`。
它们不依赖 theta 是固定常数；本节又有 `theta_Y` 有界且远离0。
因此其逐项论证确实给出

\[
 \boxed{\Sigma_Y(\xi,\eta)=\frac1{H_Y}\int_0^1
 (P_1'+\xi H_YP_1)(P_2'+\eta H_YP_2)\,dx
 +O_{P_1,P_2}(H_Y^{-2}(\log H_Y)^5).}
 \tag{Sigma-Y}
\]

该结论在所需的正、负双圆盘上一致。这里完整保留加性误差，
即使 profile 积分为零也有效。纸面内层证明已重新建立所需
解析输入；其原生 Lean 实现仍未完成，不能混同。

## 3. 将真正的两个有限和代入，而不是对接口命名

由 [主项评价](2026-08-31-conrey-gaussian-main-term-evaluation.md)，
实际算术表达式是

\[
 \mathcal A=
 \zeta(1+\gamma)\Sigma_Y(\beta,\alpha)
 +(w/(2\pi))^{-\gamma}\zeta(1-\gamma)
                   \Sigma_Y(-\alpha,-\beta),
 \qquad\gamma=(a+b)/L.
 \tag{A-Sigma}
\]

系数 P_1、P_2 的顺序始终不变；第一份仅交换两个移位，第二份
将两个移位取负。它们分别在 D_- 和 D_+ 上，故 (Sigma-Y) 均适用。
定义固定有限区间积分

\[
 J_\theta(x,y)=\int_0^1
     (P_1'(v)+\theta xP_1(v))
     (P_2'(v)+\theta yP_2(v))\,dv.
\]

在负双圆盘，`|gamma|` 同时上、下界为常数乘 `1/L`。
Hurwitz 的可去有限部分给出
`zeta(1+gamma)=1/gamma+O(1)`、
`zeta(1-gamma)=-1/gamma+O(1)`。
(Sigma-Y) 中主项为 O(1/L)，误差乘 zeta 至多花费 O(L)。
因此一致地

\[
 \mathcal A=
 \frac{J_{\theta_Y}(b,a)
 -(w/(2\pi))^{-(a+b)/L}J_{\theta_Y}(-a,-b)}
 {\theta_Y(a+b)}
 +O_{P_1,P_2}\!\left(\frac{(\log L)^5}{L}\right).
 \tag{A-first}
\]

这里 `H_Y` 与 L 可比；相关常数独立于 w 和双圆盘中的移位。
这是使用远离 `a+b=0` 的固定 Cauchy 邻域，而不是假设整个
Gaussian 积分只对这种移位才存在。

## 4. w 的替换和整数 cutoff 的归一化误差

因为 `w/T in [1,2]`，实数 `log(w/(2pi T))` 有绝对界，所以

\[
 (w/(2\pi))^{-(a+b)/L}
 =e^{-a-b}\left[1+O(1/L)\right]
\]

在 D_- 上一致。分母 `a+b` 远离0，这给 (A-first) 新增 O(1/L)
的加性误差。

整数截断也有明确的有限误差：对 `T^theta_0>=2`，

\[
 0\le\theta_0-\theta_Y
 =\frac1L\log\frac{T^{\theta_0}}{\lfloor T^{\theta_0}\rfloor}
 \le\frac{2T^{-\theta_0}}L.
 \tag{floor-bound}
\]

且最终 `theta_Y>=theta_0/2`。在这段固定正 theta 区间及 D_- 上，
`[J_theta(b,a)-exp(-a-b)J_theta(-a,-b)]/[theta(a+b)]`
对 theta 的导数有统一界：J 是 theta 的二次多项式，所有
有限区间积分固定，theta 和 a+b 均远离0。
所以可将 theta_Y 换成 theta_0，代价为 `O(T^(-theta_0)/L)`。

记

\[
 \mathcal G(a,b)=
 \frac{J_{\theta_0}(b,a)-e^{-a-b}J_{\theta_0}(-a,-b)}
      {\theta_0(a+b)}.
 \tag{G-quotient}
\]

于是

\[
 \boxed{\mathcal A=\mathcal G
 +O_{P_1,P_2}\!\left(\frac{(\log L)^5}{L}\right)}
 \tag{A-profile}
\]

在 D_- 及全部 w 上一致。这关闭的是当前局部 Gaussian 模型中
`Y=floor(T^theta_0)`、`log Y` 的归一化问题；没有借此声称
已完成全局去平滑或所有随 T 变化的积分换极限。

## 5. 把 profile 写成真正整函数

精确分部积分给出

\[
 J_\theta(b,a)-J_\theta(-a,-b)
 =\theta(a+b)P_1(1)P_2(1),
\]

其中用到 `P_1(0)=P_2(0)=0`。又
`(1-exp(-a-b))/(a+b)=int_0^1 exp(-(a+b)t)dt`，所以

\[
 \boxed{\mathcal G(a,b)=P_1(1)P_2(1)
 +\frac1{\theta_0}\int_0^1\!\int_0^1
 e^{-(a+b)t}
 (P_1'(x)-a\theta_0P_1(x))
 (P_2'(x)-b\theta_0P_2(x))\,dx\,dt.}
 \tag{G-entire}
\]

这给出 (G-quotient) 在 a+b=0 处的整延拓，也使后续微分可以
直接在紧区间内进行；不是另设一个满足假设的主项函数。

## 6. 实际 Gaussian 均方的主常数和精确未闭合项

将 (A-profile) 代入前一文档的实际分解，在 D_- 上得到

\[
 \boxed{g(a,b,w)=\mathcal G(a,b)+\mathcal E(a,b,w)+\mathcal R_T(a,b,w),}
 \tag{g-profile}
\]

这里 E 完全是 #510 定义的实际双射线对偶积分，R_T 是实际差值，
并且已经证明

\[
 \sup_{(a,b)\in\mathscr D_-,\ T\le w\le2T}|\mathcal R_T|
 \le C_{P_1,P_2,\delta}
 \left(\frac{(\log L)^5}{L}+(1+L)^3T^{-\delta}\right)
 \longrightarrow0.
 \tag{R-profile}
\]

所有函数在该闭双圆盘的邻域全纯。半径1/2的 Cauchy 圆完全
位于外半径21/40以内，故对 `D=(1+k partial_a)(1+k partial_b)`
在 a=b=-R 求值，R_T 的范数上界只乘 `5776/625`。

取实际已选多项式
`P_1=P_2=P=(84x+15x^3+x^5)/100`，则 `P(1)=1`。
对 (G-entire) 真正求导，主常数为

\[
 \boxed{\mathfrak C=
 1+\frac1{\theta_0}\int_0^1\!\int_0^1 e^{2Rt}
 \left[(1-kt)P'(x)
       +\theta_0\{R(1-kt)-k\}P(x)\right]^2dx\,dt.}
 \tag{C-actual}
\]

利用前文已经证明的实际移位求导与同一 mollifier 识别，得到

\[
 \begin{split}
 &\frac1{\Delta\sqrt\pi}\int_{\mathbb R}e^{-(t-w)^2/\Delta^2}
 \left|\left(\zeta(\sigma_0+it)+(k/L)\zeta'(\sigma_0+it)\right)
             \mathcal B(1/2+it)\right|^2dt\\
 &\qquad=\mathfrak C+
       [D\mathcal E]_{a=b=-R}
 +O_{P,\delta}\!\left(\frac{(\log L)^5}{L}+(1+L)^3T^{-\delta}\right),
 \qquad\sigma_0=\tfrac12-R/L.
 \end{split}
 \tag{MS-with-dual}
\]

算子符号为加，指数微分产生 `1-kt`，profile 微分产生 `-k theta_0 P`。
微分时两个复移位独立，最后才在负实移位识别模平方。

此处平方括号逐字对应现有 `conreyExplicitKernel x t`：
`Q(t)=1-kt`、`Q'(t)=-k`，所以它是
`Q(t)P'(x)+theta_0 Q'(t)P(x)+theta_0 R Q(t)P(x)`。
因而 (C-actual) 正是现有 `conreyExplicitMeanSquareIntegral` 的
同一个双积分定义。这个源码对应关系把纸面主项接回原有显式常数；
它不把显式常数的已知界当作 `D mathcal E` 的估计，也不是本轮
新执行的 Lean 验证。

## 7. 不能跨越的剩余证明边界

(MS-with-dual) 在纸面上把实际 Gaussian 均方的主项完全接回
既定显式 profile，并证明其余已控误差一致趋零。它不意味着
`D mathcal E=o(1)`；该项仍是实际核/DI、进一步 Fubini 和 dyadic
范围估计必须处理的对象。

因此完整长 mollifier 均方、从 Gaussian 到全局区间的去平滑、
最终简单零点比例，以及这些纸面步骤的 Lean 原生化仍未完成。
当前局部模型的整数截断误差已处理，不应再将它列为本节缺口；
也不应反过来把该处理当作所有全局截断问题都已完成。
