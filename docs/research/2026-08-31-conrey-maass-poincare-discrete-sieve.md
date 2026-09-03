# Conrey 的 DI 谱路线：实际非全纯 Poincare 内积与离散 Maass 大筛

先说结论：本篇从实际非全纯 Poincare 级数证明其 L2 延拓、准确
Gram 内积及 Maass 系数配对，再用 Bessel 不等式和已证几何模数和，
完成当前两个尖点的离散 Maass 谱大筛。普通大筛中的异常特征值也
包含在内，不依赖一个未经证明的正性/谱公式接口。

推导中同时证明模曲面尖点特征值的经典下界 lambda>=3/16。
**这是拉普拉斯谱隙，不是 Selberg 的临界线零点正比例定理。**
本篇不证明 Eisenstein 连续谱 Plancherel、完整 Kuznetsov 等式，
也不证明 DI11 所需的 X 放大异常谱估计。因此仍不是完整 DI11 或
原生 Conrey 严格 `>2/5` 的完成声明。

冻结基点 `37fcccac52be01204e8247447a90ffec80584df3`。
只新增纸面证明，不改 Lean、Lake、契约或任何冻结源树。
方法属于经典 Selberg/Poincare/DI 路线，不主张新的谱定理。

## 1. 实际对象与所证明的大筛

令 q 为正整数，Gamma=Gamma_0(q)，`e(t)=exp(2 pi i t)`，
`dmu=dxdy/y^2`，L2 内积第一变量线性且不除以面积。
初始在 Re s>1 定义

\[
 U_m(z;s)=\sum_{\gamma\in\Gamma_\infty\backslash\Gamma}
               (\operatorname{Im}\gamma z)^s e(m\gamma z),\qquad m\ge1.
 \tag{actual-Maass-Poincare}
\]

Maass 尖点形式 u 是实际的光滑 Gamma 不变 L2 函数，满足
`Delta u=lambda u`、`Delta=-y^2(partial_x^2+partial_y^2)`，且每个
尖点的水平常数项恒为0。取其 L2 正交归一特征函数 u_j，写

\[
 \lambda_j=1/4+r_j^2,\qquad
 u_j(z)=\sqrt y\sum_{n\ne0}\rho_j(n)
            \mathsf K_{ir_j}(2\pi|n|y)e(nx).
 \tag{actual-Maass-normalization}
\]

后面证明 lambda_j>=3/16，所以可选 `r_j>=0` 为实数，或
`r_j=i nu_j, 0<nu_j<=1/4`。cosh(pi r_j) 在两种情况下都为正实数。
不假设这些特征函数张成整个 L2；连续谱不被偷偷删除。

本篇证明，对 K>=1、实数 N>=1/2、复系数 a 支撑在 N<n<=2N，
以及当前 DI 应用所需尖点 infinity、0、1 的宽度1归一化，

\[
 \boxed{\sum_{|r_j|\le K}\frac1{\cosh(\pi r_j)}
       \left|\sum_{N<n\le2N}a_n\rho_{j,\mathfrak a}(n)\right|^2
   \ll_\epsilon\left(K^2+\frac{N^{1+\epsilon}}q\right)\|a\|_2^2.}
 \tag{discrete-Maass-large-sieve}
\]

这就是 DI Theorem 2 的离散式 (1.29) 在当前两个实际尖点上的范围。
其中未放大的异常谱已经包含；需要 X^(2 nu_j) 放大的其他异常谱
命题不由这一式自动完成。

## 2. 不借助谱分解的 L2 值延拓

以下使用已经纸面证明的任意模数 Weil 界

\[
 |\operatorname{Kl}_c(m,n)|\le\sqrt m\,\tau(c)\sqrt c
 \quad(m\ge1,\ n\in\mathbb Z).
 \tag{fixed-m-Weil}
\]

### 2.1 全部尖点上的真实分解

固定整数矩阵 sigma=[[a,b],[v,u]] in SL_2(Z)。前篇已经证明
gamma sigma 的下行 (c,d) 遍历互素整数行，条件准确为
`uc-vd=0 mod q`；非零行取 c>0，零行仅在 q|v 时存在。
对非零行，`gamma sigma z=alpha/c-1/[c(cz+d)]`，alpha 是 d 模 c
的逆元。于是初始 Re s>1 时

\[
 U_m(\sigma z;s)=\mathbf1_{q\mid v}y^se(mz)
                         +y^s L_{\sigma,s}(z)+y^s R_{\sigma,s}(z),
 \tag{scalar-Poincare-split}
\]

\[
 L_{\sigma,s}(z)=\sum_{c>0}c^{-2s}
      \sum_{\substack{d\in\mathbb Z\ (d,c)=1\\uc-vd\equiv0(q)}}
       e(m\bar d/c)|z+d/c|^{-2s},
\]

\[
 R_{\sigma,s}(z)=\sum_{c>0}
      \sum_{\substack{d\in\mathbb Z\ (d,c)=1\\uc-vd\equiv0(q)}}
       e(m\bar d/c)|cz+d|^{-2s}
         \left\{e\left(\frac{-m}{c(cz+d)}\right)-1\right\}.
\]

这是权重0对象，没有上一篇权重2的 j 因子；所有幂的底数均为
正实数，以实对数定义复幂。

在 s 的紧集、y>=y_0>0 上，差值因子由
`C_(m,y_0)/(c|cz+d|)` 主化。若 alpha=Re s>0，则余项连同 y^s
由下式控制：

\[
 C y^\alpha\sum_{c\ge1}\frac1c
                     \sum_{d\in\mathbb Z}|cz+d|^{-2\alpha-1}.
\]

整数行的单调积分比较给出局部一致收敛；当 y>=1 时为
`O(y^(-alpha))`，统一于任意固定 s 紧集。因此该余项本身全纯依赖 s。

### 2.2 首项的精确同余完成

令

\[
 I_s(\xi,y)=\int_{\mathbb R}(t^2+y^2)^{-s}e(-\xi t)dt,
\]

\[
 T_{c,\sigma}(n)=\sum_{\substack{d\bmod qc\ (d,c)=1\\uc-vd\equiv0(q)}}
                   e(m\bar d/c+nd/(qc)).
\]

将 d 按模 qc 分组并周期化，初始得到

\[
 L_{\sigma,s}(x+iy)=\frac1q\sum_{n\in\mathbb Z}e(nx/q)I_s(n/q,y)
                          \sum_{c\ge1}c^{-2s}T_{c,\sigma}(n).
 \tag{scalar-leading-Poisson}
\]

前篇第4.2节已对有限角色检测逐项证明

\[
 T_{c,\sigma}(n)=
  \sum_{\substack{\ell\bmod q\\n-\ell vc\equiv0(q)}}
      e(\ell uc/q)\operatorname{Kl}_c\left(m,\frac{n-\ell vc}{q}\right),
 \qquad |T_{c,\sigma}(n)|\le q\sqrt m\,\tau(c)\sqrt c.
 \tag{proved-all-cusp-completion}
\]

这里复用的是同一有限和恒等式，不是假定一种新的加权谱输入。
对任何 alpha_0>3/4，c 和由 `sum tau(c)c^(1/2-2alpha_0)` 主化。
该级数收敛，因为对 p>1，`sum tau(c)c^(-p)=zeta(p)^2`。

缩放 t=yh，并对 h 分部积分两次。在 s 的紧集且 Re s>1/2 时，
`(1+h^2)^(-s)` 及其两阶导数的 L1 范数一致有界，所以

\[
 |I_s(\xi,y)|\le C y^{1-2\operatorname{Re}s}(1+|\xi|y)^{-2}.
 \tag{scalar-Fourier-majorant}
\]

它使 (scalar-leading-Poisson) 的 c,n 双重和在 Re s>3/4
局部一致收敛，并全纯依赖 s。零频没有被去掉：
`I_s(0,y)=sqrt(pi)Gamma(s-1/2)y^(1-2s)/Gamma(s)`，在此半平面解析。

### 2.3 全部尖点的 L2 主化

对 y>=1，`sum_n(1+|n|y/q)^(-2)<=C(1+q/y)`。因此在任何
s 紧集中，若 alpha=Re s>3/4，延拓后的实际函数满足

\[
 |U_m(\sigma(x+iy);s)|
 \le C\{y^\alpha e^{-2\pi my}+y^{1-\alpha}+y^{-\alpha}\}.
 \tag{all-cusp-L2-growth}
\]

平方再乘双曲测度 y^(-2)dy，尾部由可积的 `C y^(-2alpha_0)`
控制，其中 alpha_0>3/4 为该紧集的实部下界。Gamma 有有限指数，
基本域由紧核与有限个尖点条组成，故这给出整个基本域的 L2 主化。
局部全纯性和该主化允许把 s 的 Cauchy 积分公式放进 L2，证明

\[
 \boxed{s\longmapsto U_m(\cdot;s)\ \text{在 Re }s>3/4
       \text{ 为全纯的 }L^2(\Gamma\backslash\mathbb H)\text{ 值函数。}}
 \tag{actual-L2-continuation}
\]

初始级数的 Gamma 不变性由解析唯一性保留。这里不是只延拓某个
标量系数，更不是假设存在一个 L2 证书。所有尖点主化是显式的。

## 3. 实际 Maass 形式、Fourier 展开与配对

### 3.1 从微分方程到系数归一化

在宽度 w 的尖点，水平 Fourier 展开把 Delta u=lambda u 变成
每个非零整数频率的修正 Bessel 方程。写 lambda=1/4+r^2，
它的衰减解准确为 `sqrt(y) K_(ir)(2 pi |n|y/w)`。

本篇使用的标准归一化可直接从

\[
 \mathsf K_\nu(z)=\int_0^\infty e^{-z\cosh h}\cosh(\nu h)dh
             \quad(\operatorname{Re}z>0)
 \tag{Macdonald-general-order}
\]

识别：对 z 两次求导、对 h 分部积分给出修正 Bessel 方程；
令 h=v/sqrt(x) 并用 Gaussian 主化，得到正实轴渐近
`K_nu(x)~sqrt(pi/(2x))e^(-x)`，统一于 nu 的紧集。
第二独立解由降阶公式 `K_nu(x) integral dx/(x K_nu(x)^2)` 构造，
在足够大的 x 上呈 e^x/sqrt(x) 增长。尖点处的 L2 条件逐频排除
该增长解，常数项则由尖点定义为0。这证明了第1节所写的归一化。

还需实际控制无穷频率：在足够高的一条固定水平线上，Fourier
系数被该线上 u 的上确界控制；上面的 K 渐近把 rho(n) 至多控制
在 `C sqrt(|n|)exp(C|n|)`。再升高 y 后，K 因子的指数衰减给出
u 及所需一阶导数的局部一致指数衰减。有限个尖点加紧核说明 u
在整个 H 上有界。

在截断基本域上分部积分，配对边抵消，尖点边界因该衰减趋于0，得

\[
 \lambda\|u\|_2^2=\int_{\Gamma\backslash\mathbb H}
                              (|u_x|^2+|u_y|^2)dxdy.
 \tag{Maass-energy}
\]

因此非零尖点形式有 lambda>0；lambda=0 会强制 u 为常数，再由
尖点条件强制为0。不同实特征值的形式由同一分部积分正交。

### 3.2 配对的实际 Gamma 积分

先在 Re s>1 展开内积。u 有界，而展开后的竖条在 y 接近0时由
`C y^(Re s-2)` 主化，在无穷处有 e^(-2 pi my)，所以 unfolding
绝对合法。水平积分提取第 m 项。若 `s-1/2` 的实部大于 |Im r|，
剩下的 Macdonald 积分给出

\[
 \boxed{\langle U_m(\cdot;s),u\rangle
  =\overline{\rho_u(m)}\,
     \frac{\sqrt\pi\,\Gamma(s-1/2+ir)\Gamma(s-1/2-ir)}
          {(4\pi m)^{s-1/2}\Gamma(s)}.}
 \tag{actual-Maass-pairing}
\]

其常数可自行核对：对 Re a>|Re nu|，先使用
(Macdonald-general-order) 和绝对 Fubini，得到

\[
 \int_0^\infty x^{a-1}e^{-x}\mathsf K_\nu(x)dx
   =\Gamma(a)\int_0^\infty\frac{\cosh(\nu h)}{(1+\cosh h)^a}dh
   =\frac{\sqrt\pi\Gamma(a+\nu)\Gamma(a-\nu)}
           {2^a\Gamma(a+1/2)}.
 \tag{Gamma-Macdonald-integral}
\]

第二个等号令 h=2v，再将偶积分写成整条实线上的指数积分，
代 t=e^(2v) 得 Beta(a+nu,a-nu)，最后用 Gamma 倍乘式。
代 a=s-1/2、x=2 pi my 即为 (actual-Maass-pairing)。

### 3.3 由 L2 延拓实际推出 3/16 谱隙

若 0<lambda<3/16，则 r=i nu，其中 1/4<nu<1/2。
令 s_0=1/2+nu>3/4。配对等式先在 Re s>1 成立，再由第2节的
L2 全纯性延至实数 s>s_0。s 降到 s_0 时，左侧有有限极限，但
右侧 Gamma(s-1/2-nu) 有简单极点；其他 Gamma 因子和分母均有限
且非零。因此每个正整数 m 都有 rho_u(m)=0。

若 u 不是实值，取其实部或虚部中一个非零实值特征函数，它仍有
同一特征值。对实值形式，负频是正频的复共轭，且常数项为0。
所有正频为0于是强制 u=0，矛盾。故

\[
 \boxed{\lambda_j\ge3/16,\qquad
       r_j\in[0,\infty)\ \text{或}\ r_j=i\nu_j,
                                  \ 0<\nu_j\le1/4.}
 \tag{proved-cuspidal-spectral-gap}
\]

边界 s=3/4 不在延拓区域内，所以没有错误地排除 lambda=3/16。
这证明的是模曲面谱隙，与本任务最终要证明的 zeta 零点数量不同。

### 3.4 有界谱区间中只有有限个正交尖点形式

这也可在不证明连续谱分解的情况下完成。对 lambda<=L 的有限
正交特征函数线性组合，(Maass-energy) 给出能量不超过 L 倍范数平方。
在宽度 w 的尖点用水平零均值的 Poincare 不等式，得

\[
 \int_{y>Y}|u|^2\frac{dxdy}{y^2}
    \le\left(\frac{w}{2\pi Y}\right)^2
                  \int_{y>Y}|u_x|^2dxdy
    \le\frac{C L}{Y^2}\|u\|_2^2.
 \tag{uniform-Maass-cusp-tail}
\]

紧核上的 L2 范数和一阶导数均有界，所以由局部 Rellich 紧性取得
L2 收敛子列；这一初等紧性可用有限张坐标图、光滑分割及矩形上的
Fourier 截断证明，高频尾由一阶导数范数控制。再用上式压小全部
尖点尾，就得到整体 L2 紧性。无限个单位正交向量的距离恒为
sqrt(2)，矛盾。因此每个有界特征值区间仅有有限总重数。

可以对每个实际特征空间取正交归一基，得到覆盖所有尖点
特征函数的可数族。这里没有声称它张成 L2 中的连续谱部分。
后面的 Bessel 不等式也只需有限个正交向量，不依赖这个完备性声明。

## 4. Poincare 级数的准确 Gram 内积

### 4.1 初始展开与真正的二维积分

先令 Re s_1,Re s_2>1，记
`G_(m,n)(s_1,s_2)=<U_m(s_1),U_n(conjugate(s_2))>`。
初始 Poincare 级数的绝对值和在基本域上有界：非零下行部分在
尖点为 O(y^(1-Re s))，零下行有指数衰减。因此绝对 unfolding
和 Fubini 都可用。水平 Fourier 展开后得到

\[
 G_{m,n}(s_1,s_2)=
   \delta_{m,n}\frac{\Gamma(s_1+s_2-1)}{(4\pi n)^{s_1+s_2-1}}
       +\sum_{q\mid c}c^{-2s_1}\operatorname{Kl}_c(m,n)
                                      \mathcal I_c(s_1,s_2),
 \tag{initial-Gram}
\]

其中完整积分为

\[
 \mathcal I_c(s_1,s_2)=\int_0^\infty\int_{\mathbb R}
    y^{s_1+s_2-2}(x^2+y^2)^{-s_1}
    \exp\!\left[-2\pi i\left(n(x-iy)+\frac{m}{c^2(x+iy)}\right)\right]
                                      dxdy.
 \tag{actual-geometric-double-integral}
\]

这是原刊 B(y,m,n,s_1) 积分的全部被积式，未使用一个待证变换核。

### 4.2 极坐标推导半圆 Macdonald 表示

置 x+iy=r exp(i theta)，0<theta<pi。Jacobian 为 r，而两个
指数项合成
`exp(-2 pi v(nr+m/(c^2r)))`，其中
`v=sin(theta)+i cos(theta)=i exp(-i theta)`。
幂次准确为 `r^(s_2-s_1-1) sin(theta)^(s_1+s_2-2)`。

该二维积分事实上在 Re s_1,Re s_2>1/2 就绝对收敛。若
alpha_j=Re s_j，角度积分的绝对值由

\[
 \int_0^\pi\sin(\theta)^{\alpha_1+\alpha_2-2}
       e^{-C(r+r^{-1})\sin\theta}d\theta
       \le C'(r+r^{-1})^{-(\alpha_1+\alpha_2-1)}
\]

控制。用 sin(theta) 与端点距离可比、再缩放一个 Gamma 积分即得。
乘径向幂后，在 r 接近0为 O(r^(2alpha_2-2))，在无穷为
O(r^(-2alpha_1))，分别可积。因此不是在条件收敛双积分中换序。

对 0<theta<pi，Re v>0，令径向变量
`r=sqrt(m/n)/c * exp(h)`，直接由 (Macdonald-general-order) 得

\[
 \int_0^\infty r^{s_2-s_1-1}
       e^{-2\pi v(nr+m/(c^2r))}dr
   =2\left(\frac{m}{nc^2}\right)^{(s_2-s_1)/2}
                    \mathsf K_{s_1-s_2}(4\pi\sqrt{mn}\,v/c).
\]

随着 theta 从0增至pi，v 从 i 经1到 -i，方向向下；
`dv/v=-i dtheta`，且 `v+v^(-1)=2 sin(theta)`。
改为向上的右单位半圆 gamma（-i 到 i），得到

\[
 \boxed{\mathcal I_c(s_1,s_2)=
 -i2^{3-s_1-s_2}c^{s_1-s_2}(m/n)^{(s_2-s_1)/2}
  \int_\gamma\mathsf K_{s_1-s_2}(4\pi\sqrt{mn}\,v/c)
                  (v+v^{-1})^{s_1+s_2-2}\frac{dv}{v}.}
 \tag{proved-polar-Macdonald-transform}
\]

半圆内部的 v+v^(-1) 为正实数，复幂用其真实对数；端点按可积极限。
这给出原刊 Lemma 4.1 的所有 c、m/n、2 和 i 因子。

### 4.3 模数求和及 L2 内积的延拓

还需对 c 趋于无穷控制 Macdonald 虚轴边界，不能只在固定 c 处
使用积分恒等式。沿用前篇的半射线平移：对 z=x exp(i phi)，
将 h 射线移到 `h=w-i phi`，则
`Re(z cosh(w-i phi))>=x sinh(w)`。短连接段有限；这给出
在 nu 的紧集、0<x<=1、|phi|<=pi/2 上的统一界

\[
 |\mathsf K_\nu(xe^{i\phi})|
      \le C(1+|\log x|)x^{-|\operatorname{Re}\nu|}.
 \tag{small-argument-boundary-majorant}
\]

具体地，新半射线上 `|cosh(nu(w-i phi))|<=C exp(|Re nu|w)`；
在 w=log(2/x) 处分段，前段用长度乘最大值，后段令 h=x exp(w)
并用 e^(-h/4) 主化，即得上式。x 位于正紧区间时的边界控制
同理得到。以上也证明端点连续性，未引用未经处理的虚轴积分表示。

将此界代入 (proved-polar-Macdonald-transform)，再用
(fixed-m-Weil)，c 级数在 s_1,s_2 紧集上的主化为

\[
 C\sum_c\tau(c)(1+\log c)c^{1/2-2\min(\operatorname{Re}s_1,
                                                   \operatorname{Re}s_2)},
\]

在两实部都大于3/4时可求和。半圆的端点幂次也一致可积，因为
`Re(s_1+s_2)-2>-1`。左侧 G 是 L2 值全纯函数的配对，按第二参数
的共轭约定对 s_1,s_2 都全纯。逐变量使用解析唯一性，将
(initial-Gram) 延至两实部都大于3/4。

特别地，对所有实 t，令 s_1=1+it、s_2=1-it，得到实际 L2 内积

\[
 \boxed{\langle U_m(1+it),U_n(1+it)\rangle
  =\frac{\delta_{m,n}}{4\pi n}
    -2i(n/m)^{it}\sum_{q\mid c}\frac{\operatorname{Kl}_c(m,n)}{c^2}
         \int_\gamma\mathsf K_{2it}(4\pi\sqrt{mn}\,v/c)\frac{dv}{v}.}
 \tag{actual-critical-Gram}
\]

这里称为 Gram 内积，不称为完整 Kuznetsov 谱等式；它的证明
尚未把整个 L2 分解为尖点谱和 Eisenstein 连续谱。

## 5. 从实际配对到非负谱权：只用 Bessel 不等式

先令 N 为正整数，b 支撑在 I_N=(N,2N]，定义真实 L2 向量

\[
 V_b(t)=\sum_n b_n n^{1/2+it}U_n(1+it).
\]

把 (actual-critical-Gram) 乘系数求和，(n/m)^(it) 被准确抵消，得

\[
 4\pi\|V_b(t)\|_2^2
  =\|b\|_2^2-2i\sum_{q\mid c}\frac1c
       \sum_{m,n}b_m\overline{b_n}\operatorname{Kl}_c(m,n)x_{m,n,c}
         \int_\gamma\mathsf K_{2it}(x_{m,n,c}v)\frac{dv}{v},
 \quad x_{m,n,c}=4\pi\sqrt{mn}/c.
 \tag{actual-vector-Gram}
\]

另一方面，由 (actual-Maass-pairing)，

\[
 \langle V_b(t),u_j\rangle
    =C(t,r_j)\sum_n b_n\overline{\rho_j(n)},\qquad
 C(t,r)=\frac{\sqrt\pi\Gamma(1/2+it+ir)\Gamma(1/2+it-ir)}
                 {(4\pi)^{1/2+it}\Gamma(1+it)}.
\]

Gamma 反射式给出同一个正实表达式

\[
 |C(t,r)|^2=\frac\pi4\frac{\sinh(\pi t)}{t D(t,r)},\qquad
 D(t,r)=\cosh\pi(t-r)\cosh\pi(t+r).
 \tag{actual-positive-pairing-weight}
\]

对 r 实数，这是两个 `|Gamma(1/2+ix)|^2=pi/cosh(pi x)`。
对 r=i nu，则把两个共轭 Gamma 因子分别按反射式配对，得到
`D(t,i nu)=sinh(pi t)^2+cos(pi nu)^2>0`。t=0 的
sinh(pi t)/t 取极限 pi。由已证 nu<=1/4，异常谱的 cos(pi nu)
一致远离0；这个事实没有被暗中假设。

对任意有限个实际正交归一 u_j，用 Hilbert 空间的 Bessel 不等式
`sum |<V,u_j>|^2<=||V||^2`，再乘4 pi，得到

\[
 \pi^2\sum_j\frac{\sinh(\pi t)}{t D(t,r_j)}
              \left|\sum_n b_n\overline{\rho_j(n)}\right|^2
       \le4\pi\|V_b(t)\|_2^2.
 \tag{actual-discrete-Bessel-inequality}
\]

未投影的其余 L2 分量只增加右侧范数，因此无需假装已证明连续谱
的完备性或 Plancherel。这里得到的是足够用于上界的真实不等式。

## 6. Gaussian 积分与已证明的 Maass 几何核

对上式乘 `t^2 exp(-(t/K)^2)` 并对实 t 积分，K>=1。定义

\[
 A_K(r)=\int_{\mathbb R}
       \frac{t\sinh(\pi t)}{D(t,r)}e^{-(t/K)^2}dt>0.
 \tag{actual-Gaussian-spectral-weight}
\]

谱侧为有限非负和；扩为可数和时用非负 Tonelli。几何侧换序也
有绝对主化：对固定 m,n，在半圆上前篇的边界论证给出
`|K_(2it)(x v)|<=C_(m,n)(1+log c)exp(pi|t|)`，其中 x=4 pi sqrt(mn)/c。
故全部 c 和由 `sum tau(c)(1+log c)c^(-3/2)` 主化，t 积分则由
`t^2 exp(-(t/K)^2+pi|t|)` 主化，对固定 K 可积。

于是 (actual-vector-Gram) 给出

\[
 \pi^2\sum_j A_K(r_j)
               \left|\sum_n b_n\overline{\rho_j(n)}\right|^2
 \le\frac{\sqrt\pi}2K^3\|b\|_2^2
                -2i\sum_{q\mid c}\frac{G_K(c)}c,
 \tag{integrated-actual-Gram}
\]

其中 G_K 正是前篇定义的真实 Gaussian/Macdonald 几何二次和，
并非另选一个满足相似估计的函数。取绝对值上界并应用
[已经证明的 Maass 模数和](2026-08-31-conrey-bessel-geometric-sums.md)，得

\[
 \sum_j A_K(r_j)\left|\sum_n b_n\overline{\rho_j(n)}\right|^2
 \ll_\delta\left\{K^3+\frac{K N^{1+\delta}}q
                   +K e^{-K^2/4}\frac{N^2}{q^2}\right\}\|b\|_2^2.
 \tag{proved-weighted-spectral-budget}
\]

前面用于换序的固定参数主化不承担统一 K 的估计；统一性来自
前篇实际几何核的证明。Gaussian 尾项仍按已证的1/4保留。

### 6.1 所需截断范围内的统一下界

若 r>=0 实且 r<=K，限制 t 积分到 `[r+1,r+2]`。此处
`exp(-(t/K)^2)>=exp(-9)`，`t>=r+1`，而直接展开双曲函数得

\[
 \frac{\sinh(\pi t)}{\cosh\pi(t-r)\cosh\pi(t+r)}
        \ge\frac{c}{\cosh(\pi r)}.
\]

例如用 `sinh(pi t)>=(1-exp(-2pi))exp(pi t)/2`、
`cosh x<=exp(|x|)`，再用 t-r<=2 即可取绝对正常数。
所以 `A_K(r)>> (r+1)/cosh(pi r)`。

若 r=i nu、0<nu<=1/4，则取 t in [1,2]。
`D(t,i nu)<=cosh(pi t)^2`，Gaussian 至少 e^(-4)，所以 A_K 有
绝对正下界；同时 `(1+nu)/cos(pi nu)<=(5/4)sqrt(2)`。
故两种谱参数统一满足

\[
 \boxed{A_K(r)\ge c\frac{1+|r|}{\cosh(\pi r)}
                   \qquad(|r|\le K,\ K\ge1).}
 \tag{proved-spectral-cutoff-lower-bound}
\]

只在实际需要的 |r|<=K 范围证明此式，没有把平移后的 Gaussian
下界无说明地外推到任意大 r。

## 7. 消除 Gaussian 余项与完成普通离散大筛

记 B=N/q，并令

\[
 W(K)=\sum_{|r_j|\le K}\frac{1+|r_j|}{\cosh(\pi r_j)}
                   \left|\sum_n b_n\overline{\rho_j(n)}\right|^2.
\]

前节给出
`W(K)<<_delta (K^3+K B N^delta+K exp(-K^2/4)B^2)||b||^2`。
W 非负且单调。下面不把最后一项直接称为可忽略。

给定最终 epsilon>0，取 `delta=eta=min(epsilon/4,1/8)`，
`beta=delta+eta`，并置 `K_1=K+B^eta`。由 W(K)<=W(K_1)：

- 若 B<1，K_1<=2K，尾项至多2K，其余项至多常数倍
  `K^3+K B N^beta`。
- 若 B>=1，`K_1^3<<K^3+B^(3eta)<=K^3+B`，且
  `K_1 B N^delta<=2K B N^beta`，因为 B<=N、K>=1。
  函数 `B^2 exp(-B^(2eta)/4)` 在 B>=1 上有仅依赖 eta 的有限上界，
  故 Gaussian 项至多 `C_eta(K+B^eta)<=C_eta(K^3+B)`。

所以得到了不含该尾项的实际估计

\[
 W(K)\ll_\epsilon(K^3+K B N^\beta)\|b\|_2^2,
              \quad \beta\le\min(\epsilon/2,1/4).
 \tag{tail-free-weighted-Maass-sieve}
\]

对未加 1+|r| 权重的计数和 F(K)，逐个使用
`1/(1+r)=1/(1+K)+integral_r^K (1+t)^(-2)dt`，再做非负求和，得

\[
 F(K)=\frac{W(K)}{1+K}+\int_0^K\frac{W(t)}{(1+t)^2}dt
       \ll_\epsilon\{K^2+B N^\beta\log(2K)\}\|b\|_2^2.
\]

在 0<=t<1 的积分中只用 W(t)<=W(1)，所以没有调用 K<1 的未证界。
若 K<=N，log(2K) 可吸收到 N^(epsilon-beta)；若 K>N，则
`B N^beta<=N^(1+beta)<=K^(1+beta)`，而 beta<=1/4，故
`B N^beta log(2K)<<K^2`。两种情形共同给出
(discrete-Maass-large-sieve) 的整数 N 版本。

注意这里也处理了 K 远大于 N 的情况，不能在该范围直接写
`log K<<_epsilon N^epsilon`。

### 7.1 最低单点和实数 N

对于 n=1 单点，前篇证明真实 G_K 的全部模数和为
`O(q^(-1)|b_1|^2)`，统一于 K>=1。因此本篇同一个 Gram 论证给
`W(K)<< (K^3+q^(-1))|b_1|^2`，分部求和后为
`F(K)<<(K^2+q^(-1))|b_1|^2`。这覆盖 1/2<=N<1。

对于实数 N>=1，令 M=floor(N)，将系数分为 I_M 内部分及可能的
单点 2M+1；后者放在 I_(M+1)。两份支撑不交，且 M,M+1<=2N。
逐个非负谱项使用 `|A+B|^2<=2|A|^2+2|B|^2`，再用整数尺度界，
得到所有实数 N>=1/2 的结论。没有漏掉最低 dyadic 单点。

### 7.2 当前两个尖点的接合

取前篇已经核对的宽度1缩放 `sigma_infinity=I`、
`sigma_0=W_q=[[0,-q^(-1/2)],[q^(1/2),0]]`、`sigma_1=T_1W_q`。
W_q 精确归一化 Gamma_0(q)，双曲测度与 Delta 在其作用下不变，
故 `u(z)->u(W_q z)` 是实际 L2 酉变换，并保持 lambda 和尖点性。
在0的 Fourier 系数等于变换后形式在 infinity 的系数；在1因
T_1 in Gamma 而相同。每个完整特征空间上的平方和不依赖正交基，
所以所证离散大筛覆盖当前两尖点。缩放右乘实平移只引入单位模
相位，可吸收入输入系数而保持范数。

## 8. 原刊定位与尚未完成的谱部分

逐源核对：

- [DI82 第4节](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0023.pdf)，
  pp.250--253：本篇自行推导 (4.5)、Lemma 4.1 的极坐标变换及
  Lemma 4.2 的实际 Gram 内积；Gamma 配对与原刊离散部分一致。
  但没有把原刊引用的整个 L2 Parseval 当成本篇已经证明的事实。
- [DI82 第5节](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0024.pdf)，
  pp.260--261：使用同一个 Gaussian/Macdonald 核，保留已证尾项，
  通过非负谱截断、单调性和分部求和完成离散大筛。
- [DI82 原刊卷](https://gdz.sub.uni-goettingen.de/id/PPN356556735_0070)，
  p.226 的 Fourier 归一化 (1.15)、p.230 的目标 (1.29)；本篇不把
  (1.30) 的 Eisenstein 连续谱混入已完成声明。

纸面上已经得到：实际 L2 值 Poincare 延拓、尖点 3/16 谱隙、
准确的 Gram 内积、实际非负离散谱权，以及当前两尖点的普通
离散 Maass 大筛（含未放大的异常特征值）。

仍需完成：Eisenstein 系列在临界谱线的构造/延拓及散射归一化，
连续谱 Plancherel 与完整谱接合、Kuznetsov 等式，以及 DI11
所需 X 放大异常谱估计。Bessel 不等式足够证明本篇上界，但不等于
这些后续所需的等式，不能用它们的名字替代剩余工作。

English summary: prove the actual L2 continuation and Gram identity of
nonholomorphic Poincare series. Their explicit cusp-form pairing yields the
classical cuspidal 3/16 spectral gap. Bessel's inequality and the previously
proved geometric kernel then give the ordinary discrete Maass large sieve,
including unamplified exceptional eigenvalues, at the two cusps needed here.
Continuous-spectrum Plancherel, full Kuznetsov and amplified exceptional
estimates remain outside this proof.

独立审查应检查全尖点 L2 主化、参数全纯性、谱隙极点论证、极坐标
Jacobian/方向、所有 Gamma/4pi/i 常数、Gaussian 换序、异常谱正性、
参数替换和 K>N 时的对数处理。本次只运行允许的 Python、分类、
chain-gap 和 diff 验证；有限或浮点诊断不替代一般数学证明。
未获独占资源通知前不启动 Lean/Lake，源验证不替代最终 main 验证。
