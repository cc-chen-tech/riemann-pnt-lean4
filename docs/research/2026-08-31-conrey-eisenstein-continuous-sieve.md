# Conrey 的 DI 谱路线：实际 Eisenstein 延拓、波包与连续谱大筛

先说结论：本篇在 Gamma_0(q) 上实际构造临界谱线的 Eisenstein
系列，证明散射矩阵的酉性、Maass--Selberg 截断恒等式和正频波包
等距式，再从它们推出连续谱 Bessel 不等式。接合前篇已经证明的
真实 Poincare Gram 与几何模数和，得到当前尖点 infinity、0/1
上的 DI Theorem 2 连续谱大筛 (1.30)。没有假设一个未证的
Eisenstein 正性、Plancherel 或谱分解接口。

本篇证明波包空间的等距性，不声称该空间与尖点形式穷尽整个 L2。
完整谱装配、Kuznetsov 等式、DI11 的 X 放大异常谱仍待后续证明；
因此仍不是原生 Conrey 严格 `>2/5` 的完成声明。

冻结基点 `c54c414de6a2073bf7707cccb7fb14a1829d8c55`。
只新增纸面数学，不改任何冻结祖先、Lean、Lake 或契约。
方法属于经典同余格点/Poisson/Maass--Selberg 理论，不主张新定理。

## 1. 实际对象、归一化和目标

固定正整数 q，Gamma=Gamma_0(q)，`e(x)=exp(2 pi i x)`，
`dmu=dxdy/y^2`，L2 内积第一变量线性。尖点集合 A 取互不等价的
代表；它有限，因为 Gamma 在 SL_2(Z) 中有限指数。

对每个尖点 a，取 tau_a in SL_2(Z) 将 infinity 送到 a，
其整数宽度为 w_a，取宽度1缩放

\[
 \sigma_a=\tau_a\operatorname{diag}(\sqrt{w_a},1/\sqrt{w_a}),\qquad
 E_a(z,s)=\sum_{\gamma\in\Gamma_a\backslash\Gamma}
                    \operatorname{Im}(\sigma_a^{-1}\gamma z)^s
                    \quad(\operatorname{Re}s>1).
 \tag{actual-Eisenstein}
\]

Gamma_a 包含 -I。没有额外除以曲面面积或尖点数。
初始级数及局部各阶 z 导数绝对收敛，满足
`Delta E_a=s(1-s)E_a`。写

\[
 E_a(\sigma_b z,s)=\delta_{ab}y^s+\Phi_{ab}(s)y^{1-s}
       +\sqrt y\sum_{n\ne0}\rho^E_{ab}(n,s)
               K_{s-1/2}(2\pi|n|y)e(nx),
 \tag{E-Fourier}
\]

其中初始双陪集 Poisson 求和给出

\[
 \Phi_{ab}(s)=\frac{\sqrt\pi\Gamma(s-1/2)}{\Gamma(s)}
                 \varphi_{ab0}(s),\qquad
 \rho^E_{ab}(n,s)=\frac{2\pi^s|n|^{s-1/2}}{\Gamma(s)}
                 \varphi_{abn}(s).
 \tag{DI-E-normalization}
\]

准确地，phi_abn(s) 是正下行 c 的和
`sum_c c^(-2s) sum_(d mod c) e(nd/c)`，下行来自
sigma_a^(-1) Gamma sigma_b；这里 c 可以不是整数，d 按右平移
模 c，且上下三角左稳定子已经商去。该定义与 DI (1.17) 一致。
后面延拓的是这些实际函数，不另定义一组替代系数。

本篇目标是对 K>=1、实数 N>=1/2、a_n 支撑在 N<n<=2N，证明

\[
 \boxed{\sum_{a\in A}\int_{-K}^{K}
       \left|\sum_{N<n\le2N}a_n n^{ir}
                    \varphi_{abn}(1/2+ir)\right|^2dr
    \ll_\epsilon\left(K^2+\frac{N^{1+\epsilon}}q\right)\|a\|_2^2,}
 \tag{actual-continuous-large-sieve}
\]

其中 b 为当前需要的 infinity、0、1；0 与1为同一尖点类。
左侧求和遍历全部不等价 Eisenstein 尖点，而非只保留两个系列。
最终常数只依赖 epsilon，不从尖点数引入隐藏 q 因子。

## 2. 有限同余格点给出的真实亚纯延拓

这一节不调用曲面 resolvent、连续谱分解或 Dirichlet L 函数的
零点自由线。先得到亚纯延拓，再用实际截断内积消除临界线极点。

### 2.1 周期 Dirichlet 级数的初等延拓

对 alpha>0，逐个单位区间积分两次得到 Euler--Maclaurin 式

\[
 \zeta(w,\alpha)=\frac{\alpha^{1-w}}{w-1}
  +\frac{\alpha^{-w}}2+\frac{w}{12}\alpha^{-w-1}
  -\frac{w(w+1)}2\int_0^\infty
              B_2(\{x\})(x+\alpha)^{-w-2}dx,
 \tag{periodic-Dirichlet-continuation}
\]

`B_2(u)=u^2-u+1/6`。先在 Re w>1 对有限区间使用分部积分，
端点望远镜相消，再令终点趋于无穷；B_2 有界使余积分在
Re w>-1 局部一致绝对收敛，连同参数导数的 log 幂也一样。
这证明所需延拓，而不是引用 Hurwitz zeta 的延拓结论。
因此每个 `sum_(k>=1,k=r mod q) k^(-w)`，写成
`q^(-w) zeta(w,r/q)`（r 取1到q），都在 Re w>-1 亚纯。

### 2.2 非本原格点和及其准确 Fourier 展开

令 V 是模 q 的本原行，即 gcd(v_1,v_2,q)=1；q=1 时包含唯一行。
初始 Re s>1 定义

\[
 H_v(z,s)=\sum_{\substack{(c,d)\in\mathbb Z^2\setminus\{0\}\\
                         (c,d)\equiv v\ (q)}}
                  \frac{y^s}{|cz+d|^{2s}},\qquad
 P_v(z,s)=\sum_{\substack{(c,d)=1\\(c,d)\equiv v\ (q)}}
                  \frac{y^s}{|cz+d|^{2s}}.
 \tag{actual-residue-lattice-sums}
\]

这里仍计入正负行；只在恢复 E 时除以2。对每个 c!=0 沿 d 的
模 q 等差数列做 Poisson 求和。所用 Fourier 积分是

\[
 \int_{\mathbb R}(t^2+Y^2)^{-s}e(-\xi t)dt
  =\frac{2\pi^s}{\Gamma(s)}|\xi|^{s-1/2}Y^{1/2-s}
                    K_{s-1/2}(2\pi|\xi|Y)\quad(\xi\ne0),
 \tag{scalar-Poisson-transform}
\]

零频为 `sqrt(pi) Gamma(s-1/2) Y^(1-2s)/Gamma(s)`。
可由 Gamma 积分表示 `(t^2+Y^2)^(-s)`、实 Gaussian Fourier
积分以及 u 与1/u 的 Macdonald 积分表示直接推出；Re s>1 时
各步绝对收敛。代入 Y=|c|y、xi=k/q、频率 n=kc，得到

\[
\begin{split}
 H_v(z,s)={}&\mathbf1_{v_1=0}y^s
          \sum_{\substack{d\ne0\\d\equiv v_2(q)}}|d|^{-2s}\\
 &+\frac{\sqrt\pi\Gamma(s-1/2)}{q\Gamma(s)}y^{1-s}
          \sum_{\substack{c\ne0\\c\equiv v_1(q)}}|c|^{1-2s}\\
 &+\frac{2\pi^s\sqrt y}{q^{s+1/2}\Gamma(s)}
       \sum_{n\ne0}|n|^{s-1/2}
         \left(\sum_{\substack{c\mid n\\c\equiv v_1(q)}}
                    |c|^{1-2s}e\left(\frac{nv_2}{cq}\right)\right)
            K_{s-1/2}(2\pi|n|y/q)e(nx/q).
\end{split}
 \tag{exact-lattice-Fourier}
\]

内层 c|n 遍历正负非零约数。两类零模分别用 w=2s 和 w=2s-1
的周期 Dirichlet 延拓处理，故在 Re s>0 亚纯。
非零模的内层是有限约数和，在任何 s 紧集只有 n 的多项式增长；
K 在正实大自变量的指数衰减使其在 y>=y_0>0 上，连同各阶
z 导数和参数导数局部一致收敛。该衰减也可直接从
`K_nu(X)=integral_0^infty exp(-X cosh t) cosh(nu t)dt` 分段估计。
所以右式确实延拓了实际 H_v，且可逐项施加 Delta。

### 2.3 有限矩阵反演，不假设任何 L 函数非消失

每个格点行唯一写成正整数 k 乘本原行。由于 v 模 q 本原，
k 与 q 互素，故准确地

\[
 H_v(z,s)=\sum_{\substack{k\ge1\\(k,q)=1}}k^{-2s}P_{k^{-1}v}(z,s),
              \qquad H(z,s)=M_q(s)P(z,s).
 \tag{finite-primitivity-matrix}
\]

M_q 的条目是有限个模 q 等差 Dirichlet 级数，由2.1亚纯延拓。
当 Re s 趋于正无穷时，k=1 项为 I，其余项的行和至多
`sum_(k>=2) k^(-2 Re s)`，趋于0。因此 det M_q 不恒为0，
有限维的 `adj(M_q)/det(M_q)` 给出亚纯逆矩阵。
定义 P=M_q^(-1)H，便在 Re s>0 亚纯延拓了原来的本原行和。
此时允许逆矩阵有极点；没有擅自假定临界线可逆。

### 2.4 恢复每个实际尖点系列与全尖点增长

令 R_a 是下行 `(c,d) mod q` 的有限集合，这些下行来自
`tau_a^(-1) gamma`，gamma in Gamma。则

\[
 E_a(z,s)=\frac{w_a^{-s}}2\sum_{v\in R_a}P_v(z,s).
 \tag{actual-E-from-lattices}
\]

这里须验证“某个模 q 行可出现”确实等价于“该模 q 类中的每个
本原整数行均可出现”。给定两个模 q 相同的本原行，各取一个
行列式1的上行；模 q 上两个上行之差是下行的标量倍数。
调整上行一个整数倍的下行，即可使两个矩阵模 q 相同，所以
`tau_a M in Gamma_0(q)` 的条件保持。相同下行的两种上行差 T_k；
两者都合法恰意味着 `tau_a T_k tau_a^(-1) in Gamma_a`。
因此左陪集与这些本原行模正负一一对应，正好给出1/2，而没有
残留的 w_a 或额外陪集重数。R_a 也对取负封闭。

在另一尖点 b，用
`H_v(tau_b z,s)=H_(v tau_b)(z,s)`，再将 z 换成 w_b z。
2.2的有限和展开给出全尖点的亚纯、光滑展开：两项幂函数加
指数衰减的非零模。初始 Re s>1 时 y^s 系数是 delta_ab，
由解析唯一性延拓后仍如此，y^(1-s) 系数记为 Phi_ab(s)。
Gamma 的周期1不变性消去非整数频率，剩余即 (E-Fourier)。
由初始双陪集求和和 (scalar-Poisson-transform) 得到1节的 phi
归一化，之后同样按唯一性延拓。

因此 E、Phi、rho 和 phi 均是实际级数的亚纯延拓。在避开极点的
s 紧集上，每个尖点的非零模及其各阶导数统一指数衰减；常数
项及其参数导数最多为 y 的固定幂乘 log 幂。这足以支持以下
Green、参数积分和截断步骤，不需要全谱理论。

## 3. 散射酉性、临界线正则性与函数方程

### 3.1 尖点正交性与散射对称性

对任意实际 Maass 尖点形式 u，初始 Re s>1 可绝对展开
`<E_a(s),u>` 到宽度1的全条带。y 趋于0时 u 有全局有界性，
y 趋于无穷时指数衰减；因此积分可先按 x 做，得到 u 的零
常数项。于是

\[
             \langle E_a(s),u\rangle=0.
 \tag{actual-cusp-orthogonality}
\]

全尖点多项式增长乘 u 的指数衰减使此配对在 Re s>0 亚纯，
所以该恒等式保持。关于 u 的有界性和尖点尾项见前篇3节的
实际 Fourier/ODE 论证。

在截断曲面上对 E_a(s)、E_b(s) 使用不取共轭的 Green 恒等式。
它们的特征值相同；紧核的成对边相消，每个尖点的非零模边界
贡献趋于0。常数项的 Wronskian 留下
`(1-2s)(Phi_ba(s)-Phi_ab(s))=0`，故

\[
                      \Phi(s)^T=\Phi(s).
 \tag{scattering-symmetry}
\]

先在无极点且 s!=1/2 的开集上成立，再作亚纯延拓。
初始实 s 的 E 为实函数，因此
`E(bar s)=overline(E(s))`、`Phi(bar s)=overline(Phi(s))`。

### 3.2 临界线上的通量恒等式

取 s=1/2+ir、r!=0，暂避开亚纯极点。Delta 的特征值为实数。
对 E_a(s)、overline(E_b(s)) 使用 Green；同样让尖点高度趋于
无穷，常数项给出

\[
 -2ir\left(\delta_{ab}
           -\sum_c\Phi_{ac}(s)\overline{\Phi_{bc}(s)}\right)=0.
 \tag{actual-flux-identity}
\]

交叉 y^s/y^(1-s) 项的 Wronskian 为0，非零模趋于0。
所以 Phi(s)Phi(s)^*=I。此为方阵，也有 Phi(s)^*Phi(s)=I。
每个条目在临界线的正则点模长<=1；亚纯极点若存在，沿该直线
逼近会无界。因此 Phi 在整条临界线无极点，包括 r=0 的可去点。
由连续性，r=0 时亦酉。

### 3.3 排除 E 本身的临界线极点

仅证明 Phi 无极点还不够：需排除常数项为0的极点残量。
若 E_a 在 s_0=1/2+ir_0 有极点，取其最高阶 Laurent 系数 R。
因为 delta_ab y^s+Phi_ab(s)y^(1-s) 无极点，R 在每个尖点的
常数项均为0，非零模指数衰减。比较 Delta 方程最高阶得
`Delta R=(1/4+r_0^2)R`。所以非零 R 是实际 L2 Maass 尖点形式。
将 u=R 代入 (actual-cusp-orthogonality)，取同阶 Laurent 系数
得到 `<R,R>=0`，矛盾。E 在临界线全部正则，其 Fourier 系数
随 r 光滑。这里没有将 L 函数的零点自由线当作隐藏前提。

### 3.4 函数方程和正负谱参数

由实共轭、对称性和酉性，在临界线上
`Phi(s)Phi(1-s)=I`。向量 E 按尖点 a 为行指标排列成列，则

\[
                       E(s)=\Phi(s)E(1-s).
 \tag{actual-E-functional-equation}
\]

证明：两边在每个尖点的 y^s 和 y^(1-s) 常数项完全相同。
差为 L2 尖点特征函数，又由3.1与每个尖点特征函数正交，因此
差为0。临界线的恒等式也给出 0<Re s<1 上的亚纯函数方程。
这将用于准确处理正、负 r 的重复计数，不能只口头说“谱是偶的”。

## 4. 准确的 Maass--Selberg 截断内积

选 Y 足够大，使所有归一化尖点柱 `0<=x<1,y>Y` 互不相交。
令 C_ac(y,s)=delta_ac y^s+Phi_ac(s)y^(1-s)，定义 Lambda^Y E_a
在每个这样的尖点柱上从 E_a 减去 C_ac，其他地方不变。
于是 Lambda^Y E_a 属于 L2。

对于初始避开极点、且以下分母非零的 s,w，有准确等式

\[
\begin{split}
 \langle\Lambda^Y E_a(s),\Lambda^Y E_b(w)\rangle
 ={}&\frac{\delta_{ab}Y^{s+\bar w-1}}{s+\bar w-1}
 +\frac{\sum_c\Phi_{ac}(s)\overline{\Phi_{bc}(w)}
                         Y^{1-s-\bar w}}{1-s-\bar w}\\
 &+\frac{\overline{\Phi_{ba}(w)}Y^{s-\bar w}}{s-\bar w}
  +\frac{\Phi_{ab}(s)Y^{\bar w-s}}{\bar w-s}.
\end{split}
 \tag{actual-Maass-Selberg}
\]

给出边界推导以固定符号。对 u,v，第一变量线性的 Green 式为

\[
 \int(\Delta u\bar v-u\overline{\Delta v})d\mu
                  =\int_{y=Y}(u\bar v_y-u_y\bar v)dx.
\]

先在截断紧核应用，再把每个尖点的非零模积分从 Y 加到无穷。
常数模与非零模的 x 积分交叉项为0，非零模 Wronskian 在 Y
恰好相消，在无穷为0。因此剩下的边界完全由 C 给出。
除以 `s(1-s)-bar w(1-bar w)=(s-bar w)(1-s-bar w)`；
例如 y^s 与 y^barw 的 Wronskian 为
`(bar w-s)Y^(s+bar w-1)`，商为第一项。另三项同样直接相除。
本式没有未控制的指数误差。零分母处按可去极限理解；左边
截断 L2 配对在正则参数附近全纯/反全纯，保证组合极限存在。

## 5. 正频波包的等距式与连续谱 Bessel 不等式

这一节只证明足够用于大筛的等距嵌入，不宣称满射。

### 5.1 波包确实属于 L2

取向量 h=(h_a)，各 h_a in C_c^infty((0,infinity))，定义

\[
              W_h(z)=\sum_a\int_0^\infty
                            h_a(r)E_a(z,1/2+ir)dr.
 \tag{actual-positive-wave-packet}
\]

临界线正则性使此积分在紧核上光滑。每个尖点的常数项是
sqrt(y) 乘下列 log(y) Fourier 变换：

\[
 \int_0^\infty h_c(r)e^{ir\log y}dr
       +\sum_a\int_0^\infty h_a(r)\Phi_{ac}(1/2+ir)e^{-ir\log y}dr.
\]

在 r 上任意次分部积分，得 `O_A(sqrt(y)(1+log y)^(-A))`。
其平方乘双曲测度为 `O_A(dy/[y(1+log y)^(2A)])`，A>1/2 时
可积；非零模统一指数衰减。所以 W_h in L2，且
`Lambda^Y W_h -> W_h` 在 L2 中成立。

### 5.2 截断核的 delta 极限与精确2pi

将 s=1/2+ir、w=1/2+it 代入4节，写 L=log Y，
`S(r,t)=Phi(1/2+ir)Phi(1/2+it)^*`。前两项是

\[
 \delta_{ab}\frac{2\sin((r-t)L)}{r-t}
       +\frac{(\delta_{ab}-S_{ab}(r,t))e^{-i(r-t)L}}{i(r-t)}.
 \tag{positive-packet-delta-kernel}
\]

由于 S(r,r)=I，第二项的除差在包含 h 支撑的紧矩形上光滑。
与 h_a(r)overline(h_b(t)) 积分后，Riemann--Lebesgue（或一次
分部积分）使其趋于0。另两项分母为 i(r+t) 和 -i(r+t)；
正频紧支撑远离0，故同样是光滑振荡积分，趋于0。

第一项的极限是 `2pi delta(r-t)`。具体地，令
`g(u)=integral h_a(t+u) overline(h_a(t))dt`，则 g 光滑紧支撑；
`2 sin(Lu)/u=integral_(-L)^L exp(i v u)dv`，Fourier 反演和
g 的 Fourier 快速衰减给出积分极限2pi g(0)。此处没有额外的
1/2，因为 r,t 同在正轴，已避开重复谱参数。
结合5.1的 L2 截断极限得到准确等距式

\[
                \boxed{\|W_h\|_2^2=2\pi\sum_a
                                      \int_0^\infty|h_a(r)|^2dr.}
 \tag{actual-wave-packet-isometry}
\]

整个证明只使用已经构造的 E、Green、有限尖点和实 Fourier
反演；没有先引用连续谱 Plancherel 来证明自身。

### 5.3 对偶、负参数及联合 Bessel

由上述等距嵌入的对偶，对 f in L2 有

\[
 \frac1{2\pi}\sum_a\int_0^\infty
                   |\langle f,E_a(1/2+ir)\rangle|^2dr\le\|f\|_2^2.
 \tag{positive-continuous-Bessel}
\]

一般 f 的括号先定义为波包等距嵌入的 Hilbert 对偶；当 f 与
E 在每个紧 r 区间有绝对可积配对时，Fubini 表明就是普通积分。
向量函数方程给出
`v(-r)=overline(Phi(1/2-ir))v(r)`，其中 v_a(r)=<f,E_a(1/2+ir)>。
该矩阵酉，故正负参数的向量平方和相同。因此

\[
 \boxed{\frac1{4\pi}\sum_a\int_{\mathbb R}
              |\langle f,E_a(1/2+ir)\rangle|^2dr\le\|f\|_2^2.}
 \tag{actual-continuous-Bessel}
\]

波包与每个实际 Maass 尖点形式正交，由3.1和绝对换序可知。
因而左边还可以加上任意有限正交归一尖点族的平方配对和，
再用单调收敛扩为可数族。这是联合 Bessel 不等式，而非完整
Parseval；任何未识别的正交补仍可能存在，未被此论证删掉。

## 6. 与真实 Poincare 组合的准确配对

先取观测尖点 b=infinity，使用前篇实际
`U_m(z;s)=sum Im(gamma z)^s e(m gamma z)` 及其 Re s>3/4
的 L2 值延拓。固定临界谱参数 r，在所有尖点
`E_a(s_r)=O_r(y^(1/2))`，其中 s_r=1/2+ir。
在全条带上可取 `O_r(y^(1/2)+y^(-1/2))`：有限个缩放下的尖点
高度由 `C_q max(y,1/y)` 控制，紧核上有界。

因此初始 Re s>3/2 可绝对展开 `<U_m(s),E_a(s_r)>`。
先做 x 积分取第 m 个 Fourier 模，再做前篇已证 Gamma/Macdonald
积分，得到

\[
 \langle U_m(s),E_a(s_r)\rangle
  =\overline{\rho^E_{a\infty}(m,s_r)}
   \frac{\sqrt\pi\Gamma(s-1/2+ir)\Gamma(s-1/2-ir)}
        {(4\pi m)^{s-1/2}\Gamma(s)}.
 \tag{actual-E-Poincare-pairing}
\]

配对积分本身也延拓到 Re s>3/4：前篇全尖点估计
`U_m(s)=O(y^(1-Re s)+y^(-Re s)+y^(Re s)e^(-c y))`
乘 E 的 sqrt(y) 和双曲测度，最慢项是
`y^(-Re s-1/2)dy`，在该半平面可积，紧参数集的 log 导数也可积。
故参数唯一性将上式延拓到所需 s=1+it。没有在 Eisenstein
不有界的情况下直接套用尖点形式的初始 Re s>1 展开。

对有限输入 b_n 定义前篇同一个真实向量

\[
 V_b(t)=\sum_n b_n n^{1/2+it}U_n(1+it),\qquad
 C(t,r)=\frac{\sqrt\pi\Gamma(1/2+it+ir)\Gamma(1/2+it-ir)}
                      {(4\pi)^{1/2+it}\Gamma(1+it)}.
\]

配对为 `C(t,r) sum_n b_n overline(rho^E_a(n,s_r))`。准确地

\[
 |C(t,r)|^2=\frac\pi4\frac{\sinh(\pi t)}{tD(t,r)},\qquad
 D(t,r)=\cosh\pi(t-r)\cosh\pi(t+r),
 \tag{actual-pairing-weight}
\]

而 (DI-E-normalization) 和
`|Gamma(1/2+ir)|^2=pi/cosh(pi r)` 给出

\[
 \left|\sum_n b_n\overline{\rho^E_{a\infty}(n,s_r)}\right|^2
    =4\cosh(\pi r)
       \left|\sum_n b_n n^{-ir}\overline{\varphi_{a\infty n}(s_r)}\right|^2.
 \tag{rho-to-phi-exact}
\]

将这两式和1/(4pi)连续 Bessel 因子逐个代入，乘4pi得到

\[
 \pi\sum_a\int_{\mathbb R}
       \frac{\cosh(\pi r)\sinh(\pi t)}{tD(t,r)}
       \left|\sum_n b_n n^{-ir}\overline{\varphi_{a\infty n}(s_r)}\right|^2dr
                  \le4\pi\|V_b(t)\|_2^2.
 \tag{actual-continuous-pre-sieve}
\]

t=0 按可去极限理解，所有权为非负实数。这里的 pi 而不是 pi^2
与前篇离散侧不同；它与 DI 的连续谱归一化一致。

## 7. 连续谱 Gaussian 估计与普通大筛

### 7.1 与前篇同一个几何预算

乘 `t^2 exp(-(t/K)^2)` 并积分，定义前篇同一个

\[
 A_K(r)=\int_{\mathbb R}\frac{t\sinh(\pi t)}{D(t,r)}e^{-(t/K)^2}dt.
\]

连续谱侧用非负 Tonelli，不需先假设谱积分收敛；右侧真实 Gram
的全部模数换序沿用前篇的绝对主化
`sum_c tau(c)(1+log c)c^(-3/2)` 与
`integral t^2 exp(-(t/K)^2+pi|t|)dt`。因此

\[
 \pi\sum_a\int_{\mathbb R}\cosh(\pi r)A_K(r)
       \left|\sum_n b_n n^{-ir}\overline{\varphi_{a\infty n}(s_r)}\right|^2dr
 \le\frac{\sqrt\pi}2 K^3\|b\|_2^2-2i\sum_{q\mid c}\frac{G_K(c)}c.
 \tag{actual-continuous-Gaussian-Gram}
\]

G_K 正是已证的 Gaussian/Macdonald 二次和，未换成相似核。
其模数估计及前篇6.1的受限窗口下界
`cosh(pi r) A_K(r)>=c(1+|r|)`（|r|<=K、K>=1）给出

\[
 W(K):=\sum_a\int_{-K}^{K}(1+|r|)
       \left|\sum_n b_n n^{-ir}\overline{\varphi_{a\infty n}(s_r)}\right|^2dr
 \ll_\delta\left(K^3+\frac{K N^{1+\delta}}q
                       +K e^{-K^2/4}\frac{N^2}{q^2}\right)\|b\|_2^2.
 \tag{actual-weighted-continuous-budget}
\]

暂取整数 N>=1。W 是实际非负单调的积分，不是待求的假设。

### 7.2 保留尾项后再消除，处理 K>N

写 B=N/q<=N，取 `delta=eta=min(epsilon/4,1/8)`、
`beta=delta+eta<=min(epsilon/2,1/4)`，令 K_1=K+B^eta。
由 W(K)<=W(K_1)，若 B<1 则 K_1<=2K，全部尾项为 O(K)。
若 B>=1，则

- `K_1^3 << K^3+B^(3eta) <= K^3+B`；
- `K_1 B N^delta <= 2K B N^beta`；
- `B^2 exp(-B^(2eta)/4)` 在 B>=1 上有只依赖 eta 的有限上界，
  因而余下 Gaussian 项至多 `C_eta(K+B^eta)<=C_eta(K^3+B)`。

所以

\[
                     W(K)\ll_\epsilon(K^3+KBN^\beta)\|b\|_2^2.
 \tag{tail-free-continuous-budget}
\]

记 F(K) 为删去权1+|r|的同一积分。逐点恒等式
`1/(1+r)=1/(1+K)+integral_r^K (1+t)^(-2)dt` 与非负 Tonelli
给出

\[
 F(K)=\frac{W(K)}{1+K}+\int_0^K\frac{W(t)}{(1+t)^2}dt
       \ll_\epsilon\{K^2+BN^\beta\log(2K)\}\|b\|_2^2.
\]

在 t<1 只用 W(t)<=W(1)。K<=N 时将 log 吸收进
N^(epsilon-beta)；K>N 时 `BN^beta<=K^(1+beta)`，beta<=1/4
使其乘 log(2K) 为 O(K^2)。因此得到目标的整数尺度版本。
最后取 b_n=overline(a_n)，上述 phi 线性式的模平方正好变成
目标中的 `sum a_n n^(ir) phi(s_r)`；相位和共轭没有丢失。

### 7.3 最低单点、实数尺度及0/1尖点

n=1 单点用前篇已经证明的真实几何和
`sum_(q|c) |G_K(c)|/c << q^(-1)|b_1|^2`，统一于 K>=1。
于是 `W(K)<<(K^3+q^(-1))|b_1|^2`，相同分部积分给出
`F(K)<<(K^2+q^(-1))|b_1|^2`，覆盖1/2<=N<1。
实数 N>=1 令 M=floor(N)，把支撑拆为整数块 I_M 与可能的
单点2M+1（放入 I_(M+1)）。两块不交，M,M+1<=2N；逐点
`|A+B|^2<=2|A|^2+2|B|^2` 后应用整数尺度界，完成实数 N。

Fricke 矩阵 `W_q=[[0,-1/sqrt(q)],[sqrt(q),0]]` 精确归一化
Gamma_0(q)，保双曲测度且置换全部尖点。在宽度1缩放下，
`W_q sigma_a` 与被置换尖点的缩放只差左 Gamma 元素和右实平移：
剩余对角伸缩必须将平移稳定子 Z 双向映到自身，故伸缩因子为1。
初始陪集定义因而将 `E_a(W_q z,s)` 准确映为另一尖点的 E，
没有面积或宽度倍数；之后延拓仍相等。观测尖点0的 Fourier
系数等于无穷尖点系数的这种重编号，右平移仅有共同单位相位
e(n alpha)，可吸收到输入。求和遍历所有 a，重编号不改预算。
尖点1用 `sigma_1=T_1 W_q`，T_1 in Gamma，与0相同。
因此 (actual-continuous-large-sieve) 在所声明的尖点范围成立。

## 8. 结果定位与剩余工作

原刊核对：

- [DI82 原刊卷](https://gdz.sub.uni-goettingen.de/id/PPN356556735_0070)，
  p.227 的 Eisenstein 展开 (1.17)、p.230 的连续谱目标 (1.30)。
- [DI82 第4节](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0023.pdf)，
  pp.252--253 的连续 Gamma 配对、Lemma 4.5 和 (4.8) 权重。
  本篇以自己证明的波包 Bessel 不等式接合，而不把其引用的
  整个 L2 Parseval 当作本篇已证事实。

与前两篇合起来，纸面上已证明当前 infinity、0/1 尖点所需的
全偶权 holomorphic、普通离散 Maass 和连续 Eisenstein 三类
大筛。连续侧包括全体不等价 Eisenstein 尖点，并有实际
1/(4pi) 归一化，无尖点数损失。

本篇另外真正证明了临界线 E 的构造/正则性、散射酉性与函数
方程、Maass--Selberg 恒等式和正频波包等距性。**等距嵌入不等于
满射**；剩余正交补、完整谱装配与 Kuznetsov 等式仍需证明。
X 放大异常谱和 DI11 的完整应用也未由普通大筛自动解决。
原生 Conrey >2/5 仍未闭合，不能以本篇 PR 或测试代替它。

独立审查重点：同余行恢复的1/2与宽度、有限矩阵反演的真实
延拓、临界线极点残量的排除、Green 的四个分母/符号、正频
波包的2pi与全实轴1/(4pi)、非有界 E 配对的初始 Re s>3/2、
rho/phi 的4cosh因子、最低单点与全尖点重编号。

English summary: construct the actual critical-line Eisenstein family
from finite congruence lattice sums and prove scattering unitarity,
Maass--Selberg truncation, and a positive-frequency wave-packet isometry.
Its dual gives continuous Bessel with the exact 1/(4pi) normalization.
Together with the already proved Poincare Gram and geometric modulus
budget this proves the continuous large sieve at the cusps used here.
Completeness, full Kuznetsov, amplified exceptional spectrum and native
Conrey >2/5 remain separate proof obligations.
