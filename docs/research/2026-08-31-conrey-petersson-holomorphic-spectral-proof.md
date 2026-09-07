# Conrey 的 DI 谱路线：含最低权重的 Petersson 公式与全纯谱大筛

先说结论：本篇从实际 Poincare 级数证明 Petersson 公式，包含不能
直接用绝对收敛论证的最低权重 k=2；再把前篇已证的真实 Bessel
几何模数和接到实际全纯尖点形式的谱和，完成当前两个尖点所需的
全纯谱大筛。没有把 Petersson 公式或最低权重延拓放进条件接口。

**本篇不证明 Maass/连续谱的 Parseval 分解、预 Kuznetsov 公式或
exceptional-spectrum 加权估计，因而不是完整 DI11，也不是原生
Conrey 严格 `>2/5` 的完成声明。** 方法是经典 Petersson/DI 路线
的纸面展开，不主张新的谱定理。

冻结基点为 `7dc4327c45e026a2015a31a6b5ef44bd59aa433a`。
只新增纸面证明，不改 Lean、Lake、契约或已冻结源树。

## 1. 实际空间、归一化与结论

令 q 为正整数，Gamma=Gamma_0(q)，H 为复上半平面，
`e(t)=exp(2 pi i t)`。对实系数行列式1矩阵 g，记
`j(g,z)=cz+d`，`(f|_k g)(z)=j(g,z)^(-k)f(gz)`。
所有权重 k 都是正偶数。S_k(Gamma) 是在 H 上全纯、满足
`f|_k gamma=f`、在每个有理尖点消失的实际尖点形式空间。
内积取第一变量线性，**不除以群指数或基本域面积**：

\[
 \langle f,g\rangle_k
 =\int_{\Gamma\backslash\mathbb H}f(z)\overline{g(z)}
                 y^k\frac{dx\,dy}{y^2}.
 \tag{Petersson-normalization}
\]

取该空间的正交归一基 B_k(q)。其存在及有限性在第2节说明，不使用
Maass 谱分解。写 `f(z)=sum_(n>=1) a_f(n)e(nz)`，并定义
`rho_f(n)=n^(-(k-1)/2)a_f(n)`。

本篇先证明对全部 m,n>=1、k>=2 偶数，

\[
 \boxed{\frac{\Gamma(k-1)}{(4\pi)^{k-1}}
       \sum_{f\in B_k(q)}\overline{\rho_f(m)}\rho_f(n)
  =\delta_{m,n}+2\pi i^{-k}
       \sum_{\substack{c\ge1\\q\mid c}}
          \frac{\operatorname{Kl}_c(m,n)}c
             J_{k-1}\left(\frac{4\pi\sqrt{mn}}c\right).}
 \tag{actual-Petersson}
\]

Kl 是前篇已经证明任意模数 Weil 界的经典完全 Kloosterman 和。
特别地，对固定正整数 m 和任意整数 n，

\[
 |\operatorname{Kl}_c(m,n)|\le\tau(c)\sqrt{c\,(m,n,c)}
       \le\sqrt m\,\tau(c)\sqrt c.
 \tag{fixed-index-Weil}
\]

设 K>=1，先令 N 为正整数，b 支撑在 `I_N=(N,2N]` 的整数上。
实际平滑全纯谱和为

\[
 \mathcal Q_K(b;q)=
 \sum_{\substack{k\ge2\\k\ {\rm even}}}e^{-(k-1)/K}
       \frac{\Gamma(k)}{(4\pi)^{k-1}}
       \sum_{f\in B_k(q)}
          \left|\sum_n\overline{b_n}\rho_f(n)\right|^2.
 \tag{actual-holomorphic-spectrum}
\]

系数共轭只为与前篇 `b_m conjugate(b_n)` 的几何二次和逐字匹配；
改用任意系数的复共轭就得到 DI 原文的写法，不改变范数或结论。

本篇证明

\[
 \boxed{\mathcal Q_K(b;q)
   =D_K\|b\|_2^2+pi\sum_{q\mid c}\frac{H_K(c)}c
   =\left(D_K+O_\epsilon(q^{-1}N^{1+\epsilon})\right)\|b\|_2^2,}
 \tag{exact-smoothed-holomorphic}
\]

其中 H_K 是前篇的实际 E_K 加权二次和，

\[
 D_K=\sum_{l\ge1}(2l-1)e^{-(2l-1)/K}
     =\frac{\cosh(1/K)}{2\sinh^2(1/K)}.
\]

由谱侧非负性，对于所有实数 N>=1/2，以及当前 DI 应用所需尖点
infinity、0 和1的宽度1归一化，有

\[
 \boxed{\sum_{\substack{2\le k\le K\\k\ {\rm even}}}
       \frac{\Gamma(k)}{(4\pi)^{k-1}}
       \sum_{f\in B_k(q)}
       \left|\sum_{N<n\le2N}a_n n^{-(k-1)/2}a_{f,\mathfrak a}(n)\right|^2
   \ll_\epsilon (K^2+q^{-1}N^{1+\epsilon})\|a\|_2^2.}
 \tag{holomorphic-spectral-large-sieve}
\]

这是 DI Theorem 2 的全纯部分在当前两个实际尖点上的结论。
不声称任意其他尖点具有相同的 q^(-1) 参数。

## 2. 实际全纯空间的 Hilbert 性、有限性与全局界

Gamma(q) 是 SL_2(Z) 到有限矩阵群的核，包含于 Gamma_0(q)，所以
Gamma 有限指数。标准 SL_2(Z) 基本域的有限并给出 Gamma 的基本域；
它分成一个紧核与有限个有理尖点的竖条尾部。对每个尖点选择
`sigma in SL_2(Z)`，其宽度 w 为正整数且 w|q，因为
`sigma T_q sigma^(-1) in Gamma(q)`。竖条上的局部展开为
`(f|_k sigma)(z)=sum_(n>=1) a_(f,sigma)(n)e(nz/w)`。

### 2.1 闭性和完备性

在 H 内任意小闭圆盘上，全纯函数的平方模均值不等式把点值和
较小圆盘上的上确界控制在局部 L2 范数之内。基本域的有限重叠
平移、以及紧集上远离0和无穷的 y、j 因子，把这个局部范数控制在
Petersson 范数之内。因此范数 Cauchy 列在紧集上局部一致收敛到
全纯函数，且模变换律保留。

在每个尖点，极限是宽度 w 的全纯周期函数。它的 Laurent/Fourier
展开若有 n<0 项，平方积分在尾部指数发散；若有 n=0 项，则因
`k>=2`，积分 `integral_Y^infinity y^(k-2)dy` 发散。Parseval
先在每条水平线、再由非负 Tonelli 积分，严格排除这些项。因此
L2 极限仍为尖点形式，S_k 是 Hilbert 空间中的闭子空间。

### 2.2 单位球紧性与有限维

不能只用紧核上的 Montel 就忽略尖点尾部。固定一个嵌入基本域的
尖点带 `Y_0<=y<=Y_0+1`。该带的范数给出

\[
 w\sum_{n\ge1}|a_{f,\sigma}(n)|^2
       \int_{Y_0}^{Y_0+1}y^{k-2}e^{-4\pi ny/w}dy
 \le\|f\|_k^2.
\]

对 Y>=2(Y_0+1)，分母只取带内前半段，并对分子的 Gaussian-free
指数积分逐次分部积分，可得统一于 n>=1 的比值界

\[
 \frac{\int_Y^\infty y^{k-2}e^{-4\pi ny/w}dy}
      {\int_{Y_0}^{Y_0+1}y^{k-2}e^{-4\pi ny/w}dy}
 \le C_{k,w,Y_0}(1+Y^{k-2})e^{-2\pi Y/w}.
 \tag{uniform-cusp-tail}
\]

具体地，分母至少为常数乘 `exp(-4 pi n(Y_0+1/2)/w)`；
分子至多为常数乘 `(1+Y^(k-2))exp(-4 pi nY/w)`，因 n>=1
所有由分部积分产生的 n^(-j) 都有统一界。这就给出所写比值。

单位球的尖点尾部范数因而一致趋于0；在紧核上均值不等式和
Cauchy 导数估计给出正常族。取局部一致收敛子列，再结合上述尾界，
得到在整个 Petersson 范数中的收敛子列。若空间无限维，逐次在
有限维正交补中取单位向量会得到两两距离 sqrt(2) 的序列，矛盾。
所以 S_k 有限维，并可用有限次 Gram--Schmidt 取得 B_k(q)。

对每个固定 f，模不变量 `y^(k/2)|f(z)|` 在紧核有界，在各尖点
由 Fourier 展开的指数衰减有界。因此在整个 H 上

\[
 |f(x+iy)|\le C_f y^{-k/2}.
 \tag{global-cusp-bound}
\]

这些事实只用全纯函数、有限指数基本域和 Hilbert 空间的初等性质，
没有引入待证的非全纯谱定理。

## 3. k>2：绝对收敛的实际 Poincare 级数

令 Gamma_infinity={±T_j:j in Z}，并定义

\[
 P_{m,k}(z)=\sum_{\gamma\in\Gamma_\infty\backslash\Gamma}
           j(\gamma,z)^{-k}e(m\gamma z),\qquad m\ge1.
 \tag{Poincare-k-large}
\]

左陪集准确由 `(c,d)=(0,1)`，或 `c>0,q|c,gcd(c,d)=1` 参数化。
给定后者，取 `alpha d=1 mod c`，以 `(alpha d-1)/c` 为右上元；
不同 alpha 只相差左乘 T_j，e(m gamma z) 不变。负号因 k 偶数无影响。

在任意紧集 y>=y_0>0 上，忽略互素条件并对 d 求和，

\[
 \sum_{d\in\mathbb Z}|cz+d|^{-k}
 \le C_k\{(cy)^{-k}+(cy)^{1-k}\}.
 \tag{integer-row-sum}
\]

这是把距离 -cx 最近的整数单独取出，再用单调积分比较。
对 c>=1 求和在 k>2 时收敛，所以级数局部一致绝对收敛且全纯。
因 `|e(m gamma z)|<=1`，重排陪集可直接证明模变换律。

对任意 sigma=[[a,b],[v,u]] in SL_2(Z)，gamma sigma 的下行是
互素整数 (c,d)，且成员条件准确为

\[
 uc-vd\equiv0\pmod q.
 \tag{cusp-row-condition}
\]

因此 `P_(m,k)|_k sigma` 的非零下行部分由同一个全整数行和主化，
在 y 趋于无穷时为 O(y^(1-k))。零下行只在 q|v 时存在，贡献 e(mz)。
它也趋于0。周期全纯函数在尖点趋于0就只有正 Fourier 项，故
`P_(m,k) in S_k(Gamma)`。

## 4. k=2：正则化首项及所有尖点的极限

这一节专门补齐不能从上一节直接代入得到的最低权重。
对 0<s<=1/4 定义

\[
 P_{m,2,s}(z)=\sum_{\Gamma_\infty\backslash\Gamma}
         j(\gamma,z)^{-2}|j(\gamma,z)|^{-2s}e(m\gamma z),
 \qquad F_s(z)=y^sP_{m,2,s}(z).
 \tag{weight-two-regularization}
\]

对 s>0，(integer-row-sum) 的指数为 2+2s，级数绝对收敛。
P_s 的变换律有一个额外 `|j|^(2s)`；乘 y^s 后，F_s 正好是
权重2的模函数。**没有假装 F_s 在 s>0 时全纯。**

### 4.1 全部尖点上同一个首项—余项分解

固定 sigma=[[a,b],[v,u]] in SL_2(Z)。令 Q_(sigma,s) 为对
gamma sigma 的下行使用 (cusp-row-condition) 的同一正则化级数。
由 j 的乘法律，

\[
 (P_{m,2,s}|_2\sigma)(z)=|j(\sigma,z)|^{2s}Q_{\sigma,s}(z),
 \qquad (F_s|_2\sigma)(z)=y^sQ_{\sigma,s}(z).
 \tag{regularized-cusp-transform}
\]

对非零下行，`gamma sigma z=alpha/c-1/[c(cz+d)]`。
将指数拆成首项1与差值，得到

\[
 Q_{\sigma,s}(z)=\mathbf1_{q\mid v}e(mz)+L_{\sigma,s}(z)+R_{\sigma,s}(z),
\]

\[
 L_{\sigma,s}(z)=
 \sum_{c>0}c^{-2-2s}
 \sum_{\substack{d\in\mathbb Z\ (d,c)=1\\uc-vd\equiv0(q)}}
     e(m\bar d/c)(z+d/c)^{-2}|z+d/c|^{-2s},
 \tag{regularized-leading}
\]

\[
 R_{\sigma,s}(z)=
 \sum_{c>0}\sum_{\substack{d\in\mathbb Z\ (d,c)=1\\uc-vd\equiv0(q)}}
  e(m\bar d/c)(cz+d)^{-2}|cz+d|^{-2s}
       \left\{e\left(\frac{-m}{c(cz+d)}\right)-1\right\}.
 \tag{regularized-remainder}
\]

这里 c=1 时模1逆元和相位按唯一剩余类解释。零下行唯一陪集
在 q|v 时出现，且因 m 整数其整数平移相位为1。

由 `|exp(w)-1|<=|w|exp(|w|)`，差值因子至多
`C_m/[c|cz+d|]`，常数在 y>=y_0 的范围内一致。因此余项的主化是

\[
 C_{m,y_0}\sum_{c\ge1}\frac1c
          \sum_{d\in\mathbb Z}|cz+d|^{-3},
\]

在紧集上可求和，且 y>=1 时是 O_m(y^(-2))，一致于 0<=s<=1/4。
紧集上可能小于1的 `|cz+d|` 仅增加依赖 y_0 的常数。
所以 R_(sigma,s) 局部一致趋于实际全纯余项 R_(sigma,0)。

### 4.2 首项的完整 Fourier 分解与有限同余和

将 d 按模 qc 分组。定义

\[
 I_s(\xi,y)=\int_{\mathbb R}(t+iy)^{-2}|t+iy|^{-2s}e(-\xi t)dt,
\]

\[
 T_{c,\sigma}(n)=
 \sum_{\substack{d\bmod qc\ (d,c)=1\\uc-vd\equiv0(q)}}
       e\left(\frac{m\bar d}{c}+\frac{nd}{qc}\right).
\]

周期化的准确公式是

\[
 L_{\sigma,s}(x+iy)=\frac1q\sum_{n\in\mathbb Z}e(nx/q)I_s(n/q,y)
                         \sum_{c\ge1}c^{-2-2s}T_{c,\sigma}(n).
 \tag{leading-Poisson}
\]

对固定 c 先对绝对收敛的 d 和做周期化即可得到。为了让 s 降到0，
必须控制整份 c 和，而不是只控制有限 c。

对条件 uc-vd=0 mod q 用有限加法角色检测，再写 d=d_0+ct，
`t mod q`。t 和恰为 q 或0；约掉检测器的1/q后，得到精确式

\[
 \boxed{T_{c,\sigma}(n)=
    \sum_{\substack{\ell\bmod q\\n-\ell vc\equiv0(q)}}
       e(\ell uc/q)
       \operatorname{Kl}_c\left(m,\frac{n-\ell vc}{q}\right).}
 \tag{cusp-leading-completion}
\]

Kloosterman 两个参数可以用逆元换元互换。这里剩下的第二参数
因显示的整除条件确为整数，负数和0也允许。因此前篇已证 Weil 界给

\[
 |T_{c,\sigma}(n)|\le q\sqrt m\,\tau(c)\sqrt c
 \quad\text{对所有整数 }n.
 \tag{uniform-cusp-completion-bound}
\]

特别是 `sum_c c^(-2)|T_c(n)|` 一致于 n 收敛。
收敛性不需要新谱输入：`sum_c tau(c)c^(-3/2)=zeta(3/2)^2`
由非负双重级数直接得到。

### 4.3 首项极限及尖点增长

把积分变量缩放为 t=yh，两次对 h 分部积分。对 0<=s<=1/4，
`(h+i)^(-2)(1+h^2)^(-s)` 及其前两阶导数的 L1 范数一致有界。
故

\[
 |I_s(\xi,y)|\le C y^{-1-2s}(1+|\xi|y)^{-2}.
 \tag{regularized-Fourier-majorant}
\]

在 y 的任意正紧区间内，这和 (uniform-cusp-completion-bound)
给出 n,c 的双重可求和主化。因此 s 降到0时可穿过两份和，且局部
一致。直接闭合水平积分的轮廓，或用反导数处理零频，得到

\[
 I_0(\xi,y)=
 \begin{cases}-4\pi^2\xi e^{-2\pi\xi y},&\xi>0,\\0,&\xi\le0.
 \end{cases}
 \tag{weight-two-Fourier-integral}
\]

正频在下半平面闭合，方向为顺时针，极点在 -iy；负频在上半平面
闭合无极点。零频的反导数在两端都为0。这同时核对了负号。
于是 L_(sigma,0) 是只有正频的全纯函数，并在尖点指数趋于0。

注意 s>0 时零频一般不为0：缩放 t=yh 后，奇部积分为0，把偶部
`(h^2-1)(1+h^2)^(-2-s)` 的两个积分写成 Beta 积分，得到

\[
 I_s(0,y)=-s\sqrt\pi\frac{\Gamma(s+1/2)}{\Gamma(s+2)}y^{-1-2s}.
\]

只有在已经证明合法的 s 降到0极限后，这个非全纯零频才消失。

此外，对 y>=1，在 (regularized-Fourier-majorant) 中对 n 求和，
`sum_n(1+|n|y/q)^(-2)<=C(1+q/y)`，得到一致于 s 的

\[
 |L_{\sigma,s}(x+iy)|\le C_{m,q}/y,
 \qquad |Q_{\sigma,s}(x+iy)|\le C_{m,q}/y.
 \tag{all-cusp-regularized-growth}
\]

余项的 O(y^(-2)) 和零下行的指数项已经包含在第二式中。
所以 Q_(sigma,0) 全纯并趋于0；不需要只凭 infinity 的展开猜测
其他尖点也消失。

### 4.4 模性、尖点性及 Petersson 范数中的收敛

在 infinity 的局部一致极限记作 P_(m,2)。P_s 的变换律在极限中
变成准确的权重2模性。由 (regularized-cusp-transform) 的局部极限，
`P_(m,2)|_2 sigma=Q_(sigma,0)`。上一节证明它在所有尖点趋于0，故
`P_(m,2) in S_2(Gamma)`。

F_s 局部一致趋于 P_(m,2)。在每个尖点的竖条尾部，

\[
 |(F_s|_2\sigma)(x+iy)|\le C_{m,q}y^{s-1}\le C_{m,q}y^{-3/4}.
\]

权重2内积的测度是 dxdy，所以平方的主化 `C y^(-3/2)` 在尾部
可积。紧核上用局部一致收敛，有限个尖点上用该主化，严格得到

\[
 \boxed{\|F_s-P_{m,2}\|_2\longrightarrow0\quad(s\downarrow0).}
 \tag{weight-two-L2-limit}
\]

这一步消除了随后取内积极限时的缺口；仅有逐点极限是不够的。

## 5. 展开积分、准确 Fourier 系数与 Petersson 公式

### 5.1 与尖点形式的内积

对 k>2，可以绝对展开 (Poincare-k-large) 的内积。
在展开后的宽度1竖条中，y 接近0时
`|f(z)|y^(k-2)<=C_f y^(k/2-2)`，由 k>2 可积；
y 趋于无穷时有尖点指数衰减。所以没有使用仅形式的 unfolding。
水平积分提取第 m 个 Fourier 系数，随后是 Gamma 积分：

\[
 \langle f,P_{m,k}\rangle_k
       =\frac{\Gamma(k-1)}{(4\pi m)^{k-1}}a_f(m).
 \tag{unfolded-cusp-pairing}
\]

对 k=2，先用真正模性的 F_s。在 y 接近0时，绝对展开后的主化是
`C_f y^(s-1)`，只在 s>0 时使用。于是

\[
 \langle f,F_s\rangle_2
       =a_f(m)\frac{\Gamma(1+s)}{(4\pi m)^{1+s}}.
\]

再由 (weight-two-L2-limit) 及 Cauchy--Schwarz 令 s 降到0，得到
(unfolded-cusp-pairing) 的 k=2 情形。没有把 s>0 的绝对主化
直接外推至 s=0。

### 5.2 Fourier 积分及 Bessel 常数

对 h>=2 整数、n>0，顺时针闭合轮廓给

\[
 \int_{\mathbb R}(t+iy)^{-h}e(-nt)dt
       =\frac{(-2\pi i)^h n^{h-1}}{(h-1)!}e^{-2\pi ny};
 \tag{holomorphic-Fourier-integral}
\]

n<=0 时为0。对固定 m,c,y，在积分中展开
`exp(-2 pi i m/[c^2(t+iy)])`，由 `|t+iy|>=y` 和可积的
`|t+iy|^(-k)` 主化，可以逐项积分。所得级数为

\[
 (-2\pi i)^k n^{k-1}e^{-2\pi ny}
    \sum_{r\ge0}\frac{(-4\pi^2mn/c^2)^r}{r!\,(k+r-1)!}.
\]

将它和 d 的有限相位和合并，按 J_(k-1) 的标准幂级数识别，得到

\[
 a_{P_{m,k}}(n)=\delta_{m,n}
  +2\pi i^{-k}(n/m)^{(k-1)/2}
       \sum_{q\mid c}\frac{\operatorname{Kl}_c(m,n)}c
                   J_{k-1}(4\pi\sqrt{mn}/c).
 \tag{actual-Poincare-coefficient}
\]

当 k>2，原始级数和积分本来绝对收敛。k=2 时，首项使用第4节
已经证明的 c,n 双重主化，余项使用其绝对收敛主化；故同一个计算
仍合法。对固定 m,n，最终 c 和也绝对收敛：小参数 Bessel 界是
`J_(k-1)(A/c)=O_(k,A)(c^(-(k-1)))`，再用 (fixed-index-Weil)。
最弱的 k=2 已给出可求和的 `O_m,n(tau(c)c^(-3/2))`。

### 5.3 实际基展开，不是抽象谱接口

P_(m,k) 已属于实际有限维 S_k。由第2节的正交归一基及第5.1节，

\[
 P_{m,k}=\frac{\Gamma(k-1)}{(4\pi m)^{k-1}}
              \sum_{f\in B_k(q)}\overline{a_f(m)}f.
\]

取第 n 个 Fourier 系数，再乘 `(m/n)^((k-1)/2)`，即得到
(actual-Petersson)。基的完备性、最低权重、内积归一化、Gamma 因子
和 Bessel 相位都已在这里实际构造或证明。

## 6. 真实加权全纯谱和及无限求和接合

对 (actual-Petersson) 乘 `b_m conjugate(b_n)`、对有限 m,n 求和，
然后乘 `(k-1)exp(-(k-1)/K)`。谱侧恰为第1节定义的非负平方和，
因为 `Gamma(k)=(k-1)Gamma(k-1)`。

为了换序 k 与 c，不能只援引非负性，因为几何侧有相位。
令 A=4 pi sqrt(mn)。由前篇的标准 Bessel 幂级数界，

\[
 |J_r(A/c)|\le\frac{(A/(2c))^r}{r!}e^{A^2/(4c^2)},
 \qquad
 \sum_{r\ge1}r e^{-r/K}|J_r(A/c)|\le C_{A,K}/c.
\]

因此对固定 m,n,K，几何双重和的绝对值总和至多
`C_(m,n,K) sum_c tau(c)c^(-3/2)<infinity`。有限个 m,n 不影响换序。
谱侧用非负 Tonelli；或者先在 k 上有限截断，再取极限。
所有等号两边都是真正收敛的级数。

前篇定义的 E_K 准确是
`2 sum_(k>=2 even)(k-1)(-1)^(k/2)exp(-(k-1)/K)J_(k-1)`。
故几何项前因子为 pi 而非2 pi，得到

\[
 \mathcal Q_K(b;q)=D_K\|b\|_2^2+\pi\sum_{q\mid c}H_K(c)/c.
 \tag{actual-spectrum-geometric-identity}
\]

这里不改动前篇已经核对的 E_K 整体负号。应用前篇已证明的
[全纯几何模数和界](2026-08-31-conrey-bessel-geometric-sums.md)，得到
(exact-smoothed-holomorphic)，常数只依赖 epsilon，统一于 q,N,K,b。
以上换序主化依赖固定参数没有问题：它只用于等式合法性；统一估计
来自已经另行证明的几何模数和界。

## 7. 非负谱截断、实数 dyadic 参数与两个实际尖点

对 2<=k<=K，`exp(-(k-1)/K)>=exp(-1)`。因为每个谱项非负，
未平滑截断谱和至多 e 倍 Q_K。又 `D_K<<K^2` 对 K>=1 一致，
这就证明整数 N 的 (holomorphic-spectral-large-sieve)。K<2 时
截断谱和为空，结论仍成立。

### 7.1 不能漏掉实数 N 及最低单点

对实数 N>=1，令 M=floor(N)>=1。整数区间 `(N,2N]` 包含于
`I_M` 与可能存在的单点 `{2M+1}` 之并；该单点属于 I_(M+1)。
将系数分为两个不相交部分。对每个形式的线性和使用
`|A+B|^2<=2|A|^2+2|B|^2`，再对非负谱权求和。
两个整数尺度 M,M+1 都不超过2N，系数平方范数之和为原范数平方，
故得到所需实数尺度的同阶上界。

对 `1/2<=N<1`，区间中只有可能的 n=1。前篇第7节已经证明这一
单点的全纯几何模数和为 `O(q^(-1)|b_1|^2)`。第6节的准确迹恒等式
对任意有限支撑都成立，故单点谱和也在 `O(K^2+q^(-1))|b_1|^2`
内，与该实数 N 范围所需预算相符。

这里对实数区间证明的是大筛上界；没有通过平方和分割错误地声称
保留一个准确的平滑渐近主项。

### 7.2 Fricke 的实际酉变换

当前 S=1 应用的第二尖点为1，与0等价。取

\[
 W_q=\begin{pmatrix}0&-q^{-1/2}\\q^{1/2}&0\end{pmatrix},
 \quad \sigma_\infty=I,\quad\sigma_0=W_q,\quad\sigma_1=T_1W_q.
\]

前篇第7节已逐矩阵核对 `W_q^(-1)Gamma_0(q)W_q=Gamma_0(q)`，
且这些缩放后的尖点稳定子均为宽度1的 Gamma_infinity。
映射 `U_q f=f|_k W_q` 保持全纯性与尖点性，`U_q^2=Id` 因为
W_q^2=-I、k 偶数。由 `Im(gz)=y/|j(g,z)|^2` 和双曲测度不变性，
将基本域作 W_q 变量替换，直接得到

\[
 \langle U_qf,U_qg\rangle_k=\langle f,g\rangle_k.
\]

所以 `U_q B_k(q)` 仍为同一个实际空间的正交归一基。
f 在0的归一化 Fourier 系数就是 U_qf 在 infinity 的 Fourier
系数；在1则因 T_1 in Gamma 而相同。对完整基的平方和与所选
正交归一基无关，故两个尖点的全纯谱和正好转成第6节的对象。
若缩放右乘 T_t，只给第 n 个系数乘 e(nt)，可吸收到输入系数中，
其平方范数不变。这完成当前两个实际尖点的接合。

## 8. 精确对角项的保留及原刊平滑式的边界

原刊 DI82 p.249 的 (4.4) 与本篇 (actual-Petersson) 一致；对偶数 k，
`i^k=i^(-k)`。p.258 的 (5.3)--(5.4) 也保留了准确的 D_K。
不过，若将其 Proposition 4 的 (5.2) 按字面解释为统一于 q,N,K 的
`K^2/2+O(q^(-1)N^(1+epsilon))`，必须补回一个 O(1) 或保留 D_K。

本篇的结论准确为

\[
 \mathcal Q_K(b;q)=
   \{K^2/2+O_\epsilon(1+q^{-1}N^{1+\epsilon})\}\|b\|_2^2,
\]

或第1节更强、更准确的 D_K 版本。不能在 q 远大于 N 时把
`D_K-K^2/2=O(1)` 吸进 q^(-1)N^(1+epsilon)。

这一点有精确检验：固定 K=N=1、只令 b_2=1，取 q 趋于无穷。
本篇已证迹公式和几何界给出 `Q_1(b;q)->D_1`。但 D_1>1/2。
令 B=cosh(1)，则

\[
 D_1-\frac12=\frac{1+B-B^2}{2(B^2-1)}>0.
\]

严格不等式不用数值：cosh 的幂级数中，1/6! 之后相邻比至多
1/56，故
`1<B<1+1/2+1/24+(1/720)/(1-1/56)<8/5`；在 [1,8/5] 上
`1+B-B^2>=1/25>0`。因此把准确对角项替换为 K^2/2 且不留 O(1)
不能在任意大 q 上成立。

这个修正不影响原刊 Theorem 2 的大筛上界，因为 K>=1，O(1)
可吸收到 K^2。它也不改变前篇两类几何模数和的证明。
本次主要交付是实际 Petersson 与全纯谱接合，而非符号审计清单。

## 9. 逐源定位与仍未完成的步骤

直接核对的原始依据：

- [DI82 第4节](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0023.pdf)，
  pp.248--249，实际全纯基、内积和 (4.1)--(4.4)；同页非全纯谱
  Parseval 是另一个输入，不能由本篇的有限维全纯论证代替。
- [DI82 第5节](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0024.pdf)，
  pp.257--258，Proposition 4、准确 D_K 和 E_K 的谱—几何接合。
- [DI82 定理陈述](https://gdz.sub.uni-goettingen.de/id/PPN356556735_0070)，
  p.230，Theorem 2 的全纯式 (1.28) 与两个非全纯式 (1.29)--(1.30)。
- [Fonseca, 2020, Proposition 3](https://pmc.ncbi.nlm.nih.gov/articles/PMC7651428/)，
  交叉核对 k=2 的 Hecke 正则化形式。本篇第4节自行给出所需
  首项同余完成、全部尖点主化和 L2 极限，不把该命题作为证明输入。

至此，当前两个尖点的**全纯**谱大筛已经有完整纸面证明。
继续到 DI11 仍需实际 Maass/连续谱分解、预 Kuznetsov 公式、
相应非负谱权与 exceptional-spectrum 加权估计。前篇 Maass 几何
和已证，但这些谱输入尚未由它自动得到，不能宣布完整 Theorem 2。

English summary: derive the actual Petersson trace formula for every even
weight k>=2, including an all-cusp Hecke regularization and its Petersson-L2
limit at weight two. Assemble the previously proved geometric kernel bound
into the holomorphic spectral large sieve at the two cusps needed here.
Keep the exact diagonal D_K. The Maass/continuous and exceptional spectral
inputs are not proved by this note.

验收重点是权重2的所有尖点条件、角色完成的整数参数、双重主化、
正则化模因子与 L2 极限、unfolding 的绝对积分范围、Gamma/4pi/i
归一化、谱侧非负性及 k,c 换序。有限计算只能诊断，不能替代这些
一般证明。本次只运行允许的 Python/分类/chain-gap/diff 验证；
未获独占资源通知前不启动 Lean/Lake，也不把源验证当最终 main 验证。
