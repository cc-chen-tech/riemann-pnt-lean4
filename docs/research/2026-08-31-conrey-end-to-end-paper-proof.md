# Conrey 严格超过五分之二：同一实际函数上的端到端纸面证明

先说结论：将已经写出的实际 Weil、谱公式、DI11 S=1、算术主项
和局部计数证明接合，得到实际简单临界线零点的严格 `>2/5`
比例。本文给出接合的完整参数选择和极限论证，不再以“假设最终
均方／计数成立”为数学前提。这是经典 Conrey 路线的纸面证明
汇总，不是新文献定理，也不是已完成的原生 Lean 证明。

所有被引用的本库证明固定在源 SHA
`ad3cf930b653335ea54ab7ce77652903432231ca`（#548）。本文仅在
独立后继分支新增一篇 Markdown；冻结祖先不改。这里的完成层级
是纸面数学链，最终 Lean 目标、最终 SHA 构建和 main 集成仍分开。

## 1. 定理、重数和实际固定参数

令

\[
 N(T)=\sum_{\substack{\rho\text{ 非平凡零点}\\0<\Im\rho\le T}}
                  \operatorname{ord}_\rho\zeta,
 \qquad
 N_s(T)=\#\{\rho:\zeta(\rho)=0,\ \Re\rho=1/2,
                    \ 0<\Im\rho\le T,\ \operatorname{ord}_\rho\zeta=1\}.
\]

分母有解析重数，分子是实际简单零点，不是全部临界线零点。
两者恰是源码 `riemannZeroCount`、`positiveCriticalLineSimpleZeroCount`
的定义，均使用 `0<Im rho<=T`。本篇纸面证明的是

\[
 \boxed{\exists c>2/5\ \exists T_0\ \forall T\ge T_0,
                                      \quad cN(T)\le N_s(T).}
 \tag{actual-final-target}
\]

对每个充分大的实 T，始终取同一组参数

\[
 L=\log T,\quad\theta=571/1000,\quad Y=\lfloor T^\theta\rfloor,
 \quad R=6/5,\quad k=51/50,\quad\sigma_0=1/2-R/L,
 \qquad P(x)=(84x+15x^3+x^5)/100.
\]

写 `b_Y(n)=mu(n)P(log(Y/n)/log Y)`，定义实际有限多项式

\[
 \mathcal B_Y(s)=\sum_{n\le Y}b_Y(n)n^{-s},\qquad
 B_T(s)=\sum_{n\le Y}b_Y(n)n^{\sigma_0-1/2-s},
 \qquad V_T(s)=\zeta(s)+(k/L)\zeta'(s).
\]

于是逐项精确有 `B_T(sigma_0+it)=mathcal B_Y(1/2+it)`。
另取 `H(s)=s(s-1)pi^(-s/2)Gamma(s/2)/2` 和

\[
 V_{1,T}(s)=\frac{49}{100}\zeta(s)+\frac{k}{L}
                      \left(\zeta'(s)+\frac{H'(s)}{H(s)}\zeta(s)\right),
 \qquad \eta_T=HV_{1,T}=\frac{49}{100}\xi+\frac{k}{L}\xi'.
\]

这固定了与有限轮廓证明相同的实际函数，且 `49/100+k/2=1`。
不同 T 的函数可以不同；同一 T 内的所有积分、选高和计数不换函数。

## 2. 深输入的实际证明链，不再保留 DI／Weil 黑箱

以下引用的是固定源树中的证明，不是引用 PR 标签作数学理由。
旧文档的“尚未证明”是各次冻结时的历史边界，下面列出其消解位置。

| 所需输入 | 实际证明与适用范围 |
|---|---|
| 任意整数模数 Weil 界 | [素数 Stepanov 证明](2026-08-31-conrey-prime-weil-stepanov-proof.md)及[素数幂／CRT](2026-08-31-conrey-kloosterman-prime-power-proof.md)，给 `tau(q)sqrt(q gcd(a,b,q))`，含 q=1 |
| 普通谱大筛 | [二次 Kloosterman 界](2026-08-31-conrey-kloosterman-quadratic-large-sieve.md)、[几何核](2026-08-31-conrey-bessel-geometric-sums.md)、[全纯谱](2026-08-31-conrey-petersson-holomorphic-spectral-proof.md)、[Maass 谱](2026-08-31-conrey-maass-poincare-discrete-sieve.md)、[全部连续谱](2026-08-31-conrey-eisenstein-continuous-sieve.md)，当前宽度1尖点 infinity、0/1，含实尺度 N>=1/2 |
| 真实测试核公式 | [全谱完备性](2026-08-31-conrey-spectral-completeness-prekuznetsov.md)、[Bessel 反演](2026-08-31-conrey-bessel-test-kernel-inversion.md)、[同号／异号跨尖点公式](2026-08-31-conrey-actual-signed-kuznetsov.md)，保留全纯补项和所有 Eisenstein 尖点 |
| 异常谱 | [差核](2026-08-31-conrey-compensated-small-scale-kernel.md)、[固定层数](2026-08-31-conrey-fixed-level-exceptional-sieve.md)、[层数互换](2026-08-31-conrey-exceptional-level-reciprocity.md)、[区间模逆包络](2026-08-31-conrey-interval-kloosterman-envelope.md)、[区间异常谱](2026-08-31-conrey-interval-exceptional-sieve.md)，区间强化为 sqrt(N)X，而非 NX |
| 当前 DI11 | [变化尺度核](2026-08-31-conrey-smooth-scale-spectral-kernel.md)及[实际 S=1 证明](2026-08-31-conrey-actual-di11-s1-proof.md)，一般光滑权重、区间 m 系数、任意 b(n,r) |
| 当前 DI84 型矩形界 | [算术 completion](2026-08-31-conrey-di-arithmetic-completion.md)，从上一行推导，含 determinant 零项、Poisson 零频、全部尾项 |

DI11 的同一个预算是

\[
 |\mathcal S|\ll_\epsilon(CMNR)^\epsilon F\sqrt M\|b\|_2,
 \quad
 F^2=R\frac{(RC^2+MN+MC^2)(RC^2+MN+NC^2)}{RC^2+MN}
                                      +C^3\sqrt{R(R+N)}.
 \tag{actual-spectral-budget}
\]

其混合尖点模数是 `c sqrt(r)`，几何和为 `Kl_c(m bar(r),±n)`。
异常权重取 `1+R/N`，没有把 N>R 时小于1的参数传入固定层数
定理。旧 completion 权重在 c=1 可非零；DI11 证明第8节将该点
按 `Kl_1=1` 单独控制，再对 c>=2 作光滑分割。因此此次依赖消解
包括最低模数和 dyadic 单点，不仅是大尺度的形式相似。

这些证明使用通常的有限域、多项式、复分析、Fourier／Mellin、
Hilbert 空间与局部椭圆理论工具；并非只靠初等不等式。它们实际
构造了本路线的曲面谱对象和估计，没有把 DI、Weil、曲面谱完备性
或 tempered 假设另列为尚待输入的深定理。相应工具的 Lean
实现仍是机器端必须面对的工作，不能从纸面引用关系推断已存在。

## 3. 实际 Gaussian 主项和一个同时有效的损失参数选择

令 `alpha=a/L,beta=b/L`，在闭双圆盘
`|a+R|,|b+R|<=21/40` 上工作。移位始终独立，微分完成后才令
`a=b=-R`。主项证明使用的正双圆盘也有同一半径。

[实际 Gaussian 求导](2026-08-31-conrey-gaussian-differentiation.md)、
[轮廓分解](2026-08-31-conrey-gaussian-contour-decomposition.md)、
[主项评价](2026-08-31-conrey-gaussian-main-term-evaluation.md)和
[profile 接合](2026-08-31-conrey-gaussian-profile-main-term.md)给出
同一个真实移位积分

\[
 g(a,b,w)=\mathcal G(a,b)+\mathcal E(a,b,w)+\mathcal R_T(a,b,w),
\]
\[
 \mathcal G(a,b)=1+\theta^{-1}\int_0^1\!\int_0^1e^{-(a+b)y}
              (P'(x)-a\theta P(x))(P'(x)-b\theta P(x))\,dx\,dy,
\]
\[
 \sup|\mathcal R_T|\ll
             (\log L)^5/L+(1+L)^3T^{-\delta},\qquad\Delta=T^{1-\delta}.
 \tag{actual-main-and-remainder}
\]

这里算术内层已经由[有限轮廓／Volterra](2026-08-31-conrey-finite-contour-assembly.md)
证明，外层由[卷积平均](2026-08-30-conrey-arithmetic-main-term-proof.md)
证明；没有继续把 Conrey 1983 Lemma 10 作为未展开输入。
整数 cutoff 用 `H_Y=log Y`，`Y=exp(H_Y)` 精确成立；
`theta(R+21/40)<1` 保证所需移位域，且
`0<=theta-H_Y/L<=2T^(-theta)/L` 控制最终替换。

[真实核／Fubini](2026-08-31-conrey-dual-kernel-fubini.md)、
[有限块移线](2026-08-31-conrey-dual-dyadic-contour.md)、
[Type I](2026-08-31-conrey-actual-mobius-type-i.md)和
[实际 DI 余项](2026-08-31-conrey-actual-di-remainder.md)，现在使用
第2节已证明的输入，给出

\[
 |\mathcal E|\ll_{\epsilon,\eta}(1+\log Y)^3Y^{2\eta}
 T^{5/2+\eta+\epsilon}\Delta^{-7/2}(T/\Delta)^\eta
                              (T^{1/2}Y^{7/8}+Y^{7/4}).
 \tag{actual-dual-error}
\]

此处 gcd 层的 1/g、两种逆元相位、硬乘积 cutoff 和无限 N 的
衰减均保留；N 和使用 `epsilon<eta`。四相位的有限移线留数
逐块精确相消，不是把每条无限 Dirichlet 级数搬到左线。

为消除“各节小量是否能同时选择”的疑问，固定

\[
 \mu=\frac12-\frac{7\theta}{8}=3/8000,\qquad
                  \delta=\eta=\mu/32,\quad\epsilon=\mu/64.
 \tag{one-fixed-parameter-choice}
\]

于是 `0<epsilon<eta<=1/8`、`0<delta<1`、`theta<4/7<8/13`。
代入 (actual-dual-error)，两项的主幂为 `-mu,-2mu`，共同正损失为

\[
 \Lambda=7\delta/2+(1+\delta+2\theta)\eta+\epsilon
                         <7\mu/32<\mu/2.
\]

因此 `sup|mathcal E|<< (1+L)^3T^(-mu/2)->0`。所有阈值，包括
`L>=16/eta`、约数系数的微小移位损失和内层 H_Y 门槛，均只需
将最终 T_0 增大，彼此没有矛盾。这里固定参数只为接合证明，
没有优化原指数或更换 mollifier。

所有误差在闭双圆盘邻域全纯。半径1/2的 Cauchy 圆位于其中，
所以算子 `D=(1+k partial_a)(1+k partial_b)` 对误差的上界只乘
`(1+2k)^2=5776/625`。对实际 G 求导，得到同一个常数

\[
 \mathfrak C=1+\theta^{-1}\int_0^1\!\int_0^1 e^{2Ry}
       [(1-ky)P'(x)+\theta\{R(1-ky)-k\}P(x)]^2\,dx\,dy\ge1.
 \tag{actual-mean-square-constant}
\]

它就是源码 `conreyExplicitMeanSquareIntegral`，不是另选的代理。
真实 Gaussian 均方遂为 `mathfrak C+o(1)`，一致于中心区间。

## 4. 同一参数半段上的 V1 均方

[局部 V1 证明](2026-08-31-conrey-local-v1-mean.md)第2节已逐项
核对：保持 T、L、Y、Delta、射线角1/T不变，只把中心允许范围
改为 `[T/2,T]`，上述主项和余项界仍一致成立。
不作移位微分还给同一函数 `|zeta B_T|^2` 的 Gaussian 均值
`mathfrak C_0+o(1)`，其中 mathfrak C_0 是该文写出的有限积分。

对非负函数 F，[端点核去平滑](2026-08-31-conrey-dyadic-desmoothing.md)
实际证明了

\[
 \left|\int_a^bF(t)dt-\int_a^b(F*\phi_\Delta)(w)dw\right|
 \le\frac{\Delta\sqrt\pi}{2}
                 ((F*\phi_\Delta)(a)+(F*\phi_\Delta)(b)).
\]

所以同一个 `V_TB_T` 和 `zeta B_T` 在 `[T/2,T]` 的均方分别为
`mathfrak C+o(1)`、`mathfrak C_0+o(1)`。又实际 H 的有限估计给
`|(H'/H)(sigma_0+it)-L/2|<=K` 于该半段，K 固定。由

\[
 (V_{1,T}-V_T)B_T=(k/L)(H'/H-L/2)\zeta B_T
\]

得差的 L2 范数平方 `O(T/L^2)`。Cauchy 控制交叉项为 `O(T/L)`，故

\[
 \boxed{\frac2T\int_{T/2}^T
             |V_{1,T}(\sigma_0+it)B_T(\sigma_0+it)|^2dt
                                          =\mathfrak C+o(1).}
 \tag{actual-local-V1-mean}
\]

不需要同一全局 mollifier 在 `[0,T]` 的均方；本证明不主张它已得到。

## 5. 从有限轮廓返回局部的实际简单零点

取 `A=2log L`、`F=V_{1,T}B_T`。
[局部计数证明](2026-08-31-conrey-local-simple-count.md)调用源码的
任意单位窗口选高定理，得到

\[
 u\in[T/2,T/2+1],\quad v\in[T-1,T],\quad\ell=v-u=T/2+O(1)>0.
\]

三条非左边上的实际非消失已经证明；左边允许有限个零点，且
log 范数可积。完整非左边预算为

\[
 B_T^*=507T/L+2200000000000L^7+(A-\sigma_0)\pi.
\]

同一 eta 的三边变幅满足 `E_eta>=ell L/2-O(T)-O(L^7)`。
有限轮廓定理实际构造 `S subset (u,v)`，每点对应一个简单
临界线零点，且 `#S>=E_eta/pi-2N_eta,full-1`。阶数相加、
Littlewood 和 Jensen 在同一矩形上给出

\[
 \#S\ge\frac{E_\eta}{\pi}
    -\frac{\ell\log(I_2/\ell)+2B_T^*}{2\pi(R/L)}-1,
 \qquad I_2=\int_u^v|F(\sigma_0+it)|^2dt>0.
 \tag{actual-local-finite-count}
\]

这里保留完整重数损失和端点损失1；没有使用已被否定的正跳跃
计数。源码依据是 `ConreyFiniteContourCount`、
`ConreyMollifiedFullCount`、`ConreyMollifiedLittlewood`、
`ConreyMollifiedMeanSquare`。其定理的非消失、参数范围等前提
均由本段选高与实际边界估计满足，不是新的最终计数假设。

由非负积分限制及 (actual-local-V1-mean)，
`0<I_2/ell<=(T/(2ell))(mathfrak C+o(1))=mathfrak C+o(1)`。
仅需这个上界，不需控制选高时删去单位段中的峰值。
因为 `mathfrak C>=1`，log 的连续性／单调性允许代入上式。
`B_T^*L=O(T)+O(L^8)=o(TL)`，于是

\[
 \boxed{\#S\ge\frac{T\log T}{4\pi}(\kappa-o(1)),
          \quad S\subset(T/2,T),\qquad
          \kappa=1-\log\mathfrak C/R.}
 \tag{actual-local-simple-witness}
\]

局部长度是 T/2，不能把三边变幅的主项写成 T L/2。

## 6. 有限分块、RVM 和严格余量

先固定正整数 J。对 `T_j=X/2^j`、`0<=j<J` 应用上一节。
每段使用自己的固定函数，返回的却都是同一个 zeta 的真实
简单零点有限集，分别位于互不相交的开区间
`(X/2^(j+1),X/2^j)`。所以可直接合并有限见证集，得到

\[
 N_s(X)\ge\frac{X\log X}{2\pi}
                    (\kappa(1-2^{-J})-o_J(1)).
 \tag{finite-witness-union}
\]

J 固定后每个 T_j 趋于无穷，有限个误差共同趋零，且
`log T_j/log X->1`。没有使用随 X 增长的 J，也没有通过相减
两个全局下界推断局部下界。公共 dyadic 端点因开区间不会重复。

源码的同一个积分已精确评价为

\[
 \mathfrak C=-\frac{7119751197749681}{5935545000000000}
       +\frac{43767545344030157}{148388625000000000}e^{12/5}
                       <e^{18/25}.
\]

对应 `ConreyExplicitIntegralBridge` 的精确恒等式及严格指数界。
因此 `kappa>1-(18/25)/(6/5)=2/5`。

对任意 `0<c<kappa`，先选 `c<d<kappa`，再选固定 J 使
`d<kappa(1-2^(-J))`。式 (finite-witness-union) 对全部充分大的
实 X 给 `N_s(X)>=d X log X/(2pi)`。另一方面，已有实际 RVM
定理 `exists_abs_riemannZeroCount_sub_mainTerm_le_log` 给

\[
 N(X)=\frac{X}{2\pi}\log\frac{X}{2\pi}-\frac{X}{2\pi}
                    +O(1+\log(X+6))
       \sim\frac{X\log X}{2\pi}.
\]

因为 `d/c>1`，增大门槛后 `cN(X)<=d X log X/(2pi)<=N_s(X)`。
c<=0 则直接由两计数非负处理。由此证明每个 `c<kappa` 的
eventual 实际计数下界。最后取 `c=(2/5+kappa)/2`，即得
(actual-final-target)，不是只在某个高度子序列上的结论。

## 7. 数学结论与机器验收必须分开

本篇接合后，纸面链不再留下未证的 DI／Weil 输入或最终均方
假设。原刊[Conrey 1989](https://aimath.org/~kaur/publications/24.pdf)
用于核对简单零点目标及经典路线；本证明的输入是上述逐项重建的
估计和本库实际有限计数／RVM 结果，不经 Zeta23 的转接。

但冻结源树的原生最终桥仍是

```lean
theorem conreyTwoFifthsSimpleZerosTarget_of_explicit_analytic_lower_bound
    (h : conreyExplicitAnalyticLowerBound) :
    conreyTwoFifthsSimpleZerosTarget
```

该 h 尚无无条件原生证明。第2--6节的纸面结果不能直接代入 Lean，
也不能靠公理、`sorry` 或一个同名假设“消除”它。机器端仍需：

1. 原生化有限轮廓拼接、Volterra／卷积与实际 Gaussian 主项；
2. 原生化本链实际 Weil、谱构造、大筛、DI11 和实际余项估计；
3. 原生化同参数去平滑、V1 转移、局部见证求和与最终组合；
4. 在最终活动 SHA 验证全部适用模块和契约，再由唯一集成负责人
   验证最终 main 集成树。源验证不等于集成验证。

Selberg 的独立主线在当前源树的 `SelbergStrictCancellationZeroCover.lean`
中另有无参数定理
`HardyTheorem.selberg_odd_zero_proportion_target_proved_mainline`。它不由
本篇新增，也不是本次新跑过的 Lean 结果。旧目标文字中的状态不能
替代当前源码与各自最终 SHA 的验证记录。

本次仅文档交付，独立数学审查与 Python 回归分别记录。未获专属
资源窗口前不启动 Lean/Lake 或依赖加载；即使本篇 Ready for review，
也不宣布原生 Conrey 目标或整条长期任务完成。

### English summary

The reconstructed Weil and S=1 DI11 inputs now join the actual Gaussian
moment, integer-cutoff arithmetic main term, local V1 transfer and finite
simple-zero witnesses. One fixed choice of all loss parameters gives a
uniform decaying dual remainder. Fixed finite dyadic unions and the actual
multiplicity-weighted RVM count yield every eventual proportion below
1-log(C)/R, strictly exceeding two fifths. This is an end-to-end paper
proof of the classical result, not a new native Lean theorem: the explicit
analytic lower-bound hypothesis in the current final bridge remains to be
proved in Lean and validated on the final integration tree.
