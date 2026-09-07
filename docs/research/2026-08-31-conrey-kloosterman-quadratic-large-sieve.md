# Conrey 的 DI 谱路线：二次 Kloosterman 和的三条实际估计

先说结论：本篇证明 DI82 Proposition 3 在当前 Conrey 所需尖点上的
三条二次和估计，而不是再引入一个谱条件接口。核心是一个直接由
Gaussian 积分证明的混合大筛，以及保持完整平滑支撑的 Poisson
共振分离。前者不借用谱大筛，后者确实利用二次和的抵消。

这使后续 DI82 Theorem 2 的证明不再需要把这三条几何侧估计作为
未证明输入。**Kuznetsov 公式、Bessel 权重分析、Theorem 2 的完整
谱论接合及 exceptional-spectrum 加权估计仍未在本任务自证。**
本篇不是完整 DI11 或原生 Conrey 严格 `>2/5` 的完成声明。

源基点为冻结的 `e1c81aa71135b6d0736cb6543d5ad223655df862`。
只新增这篇纸面证明，不改变 Lean、Lake、Prop 接口或已有冻结交付。
以下沿用经典 DI 方法，不主张数学新颖性。

## 1. 精确对象和三条结论

固定正整数 c,N、实数 theta>0，以及支撑在
`I_N={n in Z : N<n<=2N}` 上的任意复系数 b_n。记

\[
 e(t)=\exp(2\pi i t),\qquad
 K_c(m,n)=\sum_{d\bmod c}^{*}e((md+n\bar d)/c),\qquad
 \|b\|_2^2=\sum_{n\in I_N}|b_n|^2,
\]

其中星号表示模 c 的单位，bar d 是同一模数的逆元；约定 K_1=1。
研究真实二次和

\[
 B_c(\theta,N;b)=\sum_{m,n\in I_N}b_m\overline{b_n}
 K_c(m,n)e(2\theta\sqrt{mn}/c).
 \tag{quadratic-actual}
\]

它不必是非负实数。以下只对它的绝对值作估计：

\[
 \boxed{|B_c|\le 2\tau(c)^2\sqrt c\,N\|b\|_2^2,}
 \tag{Q-Weil}
\]

\[
 \boxed{|B_c|\ll(c+N+\sqrt{\theta cN})\|b\|_2^2,}
 \tag{Q-hybrid}
\]

以及对任意 epsilon>0，在 `0<theta<2,1<=c<=N` 时

\[
 \boxed{|B_c|\ll_\epsilon
    \theta^{-1/2}c^{1/2}N^{1/2+\epsilon}\|b\|_2^2.}
 \tag{Q-oscillatory}
\]

第一条使用已经纸面证明的任意模数
[Weil 界](2026-08-31-conrey-prime-weil-stepanov-proof.md)，
并保留 gcd。后两条以下直接证明，不使用 Weil 界或谱大筛。
第7节说明为何这里的经典完全和覆盖当前 DI 应用的两个尖点。

## 2. Weil 界求和时不能丢掉 gcd

已有任意模数界为
`|K_c(m,n)|<=tau(c)sqrt(c)sqrt(gcd(m,n,c))`。
利用 `sqrt(g)<=sum_(d|g)sqrt(d)`，得到

\[
 \begin{aligned}
 |B_c|&\le\tau(c)\sqrt c
   \sum_{d\mid c}\sqrt d
      \left(\sum_{n\in I_N,\ d\mid n}|b_n|\right)^2\\
 &\le2\tau(c)\sqrt c\,N
      \sum_{\substack{d\mid c\\d\le2N}}d^{-1/2}
                 \sum_{n\in I_N,\ d\mid n}|b_n|^2\\
 &\le2\tau(c)^2\sqrt c\,N\|b\|_2^2.
 \end{aligned}
\]

第二行使用区间内 d 的倍数数量不超过 `floor(2N/d)<=2N/d`，
然后用有限 Cauchy--Schwarz。d>2N 时内层为空；没有用一个在
d>N 时失效的 `N/d` 计数界。相位模为1，故 Q-Weil 对全部 theta 成立。

## 3. Gaussian 直接给出混合大筛

先证明以下完全独立的估计：对任意 T>0 和支撑在 I_N 的复系数 a_n，

\[
 \int_{-T}^T\sum_{d\bmod c}^{*}
       \left|\sum_{n\in I_N}a_n n^{it}e(nd/c)\right|^2dt
 \le e^1\sqrt\pi\,(cT+4\sqrt\pi N)\|a\|_2^2.
 \tag{hybrid-Gaussian}
\]

先在取非负平方后，将单位剩余类扩大到全部剩余类；再用
`e^1 exp(-(t/T)^2)>=1` 主化 [-T,T] 上的积分。有限正交性和
Gaussian Fourier 积分给出上界

\[
 e^1c\sqrt\pi T
 \sum_{\substack{m,n\in I_N\\m\equiv n\pmod c}}
 a_m\overline{a_n}
       \exp\!\left(-\frac{T^2}{4}\log^2(m/n)\right).
 \tag{Gaussian-Gram}
\]

Gaussian 积分可由完成 Fourier 变换的微分方程直接得到：
`G(u)=integral exp(-t^2)e^(iut)dt` 满足 `G'(u)=-uG(u)/2`，
分部积分无边界项，且 G(0)=sqrt(pi)。缩放 t 即得到所用公式。
导数、积分交换由 Gaussian 乘多项式的可积主化保证。

对 m,n in I_N，中值定理给
`|log(m/n)|>=|m-n|/(2N)`。固定 n，并写 m=n+kc，便有

\[
 \begin{aligned}
 \sum_{m\equiv n\ (c)}
   \exp\!\left(-\frac{T^2}{4}\log^2(m/n)\right)
 &\le\sum_{k\in\mathbb Z}
        \exp\!\left(-\frac{T^2c^2k^2}{16N^2}\right)\\
 &\le1+\frac{4\sqrt\pi N}{Tc}.
 \end{aligned}
\]

最后一步对正 k 的递减 Gaussian 用从0开始的积分主化。
在 (Gaussian-Gram) 中先取绝对值，再用
`2|a_m a_n|<=|a_m|^2+|a_n|^2`，即可得到 (hybrid-Gaussian)。
这不是引用 Montgomery--Vaughan 或谱大筛后的改名。

后面也会用 n^(-it/2) 的版本，作 t/2 代换即可，绝对常数改变。
任意包含于 [-2T,2T] 的 t 区间同样被这个非负积分控制。

## 4. Mellin 分离真实的平方根相位

固定一个非负光滑函数 eta，在[1,2]上等于1，支撑包含在
`(3/4,9/4)` 内。它及全部导数此后固定。这样的函数可由
`exp(-1/x)` 型光滑台阶构造；特别可以让 0<=eta<=1。

令 lambda=2 theta N/c，定义

\[
 M(1+it)=\int_0^\infty\eta(x)e(\lambda x)x^{it}\,dx.
\]

Mellin 反演精确给出

\[
 \eta(x)e(\lambda x)=\frac1{2\pi}
       \int_{\mathbb R}M(1+it)x^{-1-it}\,dt.
 \tag{Mellin-exact}
\]

为固定归一化，令 x=exp(u)。M(1+it) 是光滑紧支撑函数
`exp(u)eta(exp(u))e(lambda exp(u))` 的正号 Fourier 变换。
反演该变换再除以 exp(u)，正是 (Mellin-exact)。其反演可通过
在 t 积分中乘 `exp(-delta t^2)`、Fubini、Gaussian 近似恒等核，
然后令 delta 降到0证明。对 u 分部积分两次给 Fourier 变换可积，
故极限也可在反演积分中交换。这里 lambda 固定时即可完成恒等式；
下一节另证明所需的参数一致界。

因 `sqrt(mn)/N in [1,2]`，将 (Mellin-exact) 代入真实二次和，得到

\[
 B_c=\frac1{2\pi}\int_{\mathbb R}M(1+it)\mathcal B(t)\,dt,
 \quad
 \mathcal B(t)=\sum_{m,n\in I_N}b_m\overline{b_n}K_c(m,n)
                (\sqrt{mn}/N)^{-1-it}.
 \tag{quadratic-Mellin}
\]

这不是给 m,n 任意添加独立相位；它严格来自同一个 sqrt(mn)。
展开 K_c 后，B(t) 除一个模为1的 N^(it) 因子外等于

\[
 \sum_{d\bmod c}^{*}
 \left(\sum_m b_m\sqrt{N/m}\,m^{-it/2}e(md/c)\right)
 \left(\sum_n\overline{b_n}\sqrt{N/n}\,n^{-it/2}e(n\bar d/c)\right).
\]

对 d 和一个 `|t|<=2T` 内的区间同时用 Cauchy；d->bar d 是单位群
的置换，两份系数范数都不超过 ||b||。由第3节有

\[
 \int_{J}|\mathcal B(t)|\,dt
     \ll(cT+N)\|b\|_2^2
 \quad(J\subseteq[-2T,2T],\ T>0).
 \tag{bilinear-hybrid}
\]

### 4.1 Mellin 权重的一致振荡界

写积分相位 `Phi(x)=2 pi lambda x+t log x`。在 eta 的固定支撑上，
当 |t|>=1 时，Phi''=-t/x^2 固定符号，绝对值与 |t| 相比有固定上下界。
于是

\[
 |M(1+it)|\ll(1+|t|)^{-1/2}
 \tag{Mellin-stationary}
\]

统一于 lambda。这里的二阶导数估计可以直接说明：把积分分成
`|Phi'|<=sqrt(|t|)` 和其余部分。前者因 Phi' 单调且导数模至少
常数乘 |t|，长度为 O(|t|^(-1/2))；其余至多两个区间，各作一次
分部积分。边界、eta' 项以及 `Phi''/(Phi')^2` 的积分均为
O(|t|^(-1/2))，最后一项使用 1/Phi' 的单调变差。
|t|<1 时直接用 eta 的 L1 范数。

另有固定 K>0，使当 `|t|>=K(1+lambda)` 时
`|Phi'|>=kappa |t|`，其中 kappa>0 固定。Phi 的更高导数均为
O_j(|t|)，对 `exp(i Phi)` 反复分部积分，给任意整数 p>=2

\[
 |M(1+it)|\ll_p|t|^{-p}
 \quad(|t|\ge K(1+\lambda)).
 \tag{Mellin-tail}
\]

eta 在支撑两端平坦为0，因此无端点残项。所有常数独立于 lambda。
例如取 K 足够大，使 `2 pi lambda <= |t|/6`，在支撑上
`|t|/x>=4|t|/9` 即足够；正负 t 都包含在这一检验中。

### 4.2 合并全部 Mellin 频率

在 |t|<=1 上直接用 (bilinear-hybrid)。对
`1<T<=K(1+lambda)` 的 dyadic 块，用 (Mellin-stationary)，
其贡献不超过

\[
 C\,(c\sqrt T+N/\sqrt T)\|b\|_2^2.
\]

两份几何级数分别由 `c sqrt(1+lambda)` 和 N 控制。
高频块使用 (Mellin-tail) 和 (bilinear-hybrid)，取 p=3 即得
绝对收敛的总和 O((c+N)||b||^2)。所以

\[
 |B_c|\ll[c\sqrt{1+\lambda}+N]\|b\|_2^2
       \ll(c+N+\sqrt{\theta cN})\|b\|_2^2,
\]

证明了 Q-hybrid。没有把高频尾项直接丢掉，也没有引入额外 log 损失。

## 5. 振荡估计：精确共振及非共振频率

现在假设 `0<theta<2`。本节先不要求 c<=N。
按 n 对 (quadratic-actual) 用 Cauchy，再用 eta(n/N) 主化非负平方，
得到

\[
 \begin{aligned}
 |B_c|^2\le\|b\|_2^2
 \sum_{m_1,m_2\in I_N}b_{m_1}\overline{b_{m_2}}
 \sum_{d_1,d_2\bmod c}^{*}e((m_1d_1-m_2d_2)/c)
 \sum_{n\in\mathbb Z}\eta(n/N)e(A n+\beta\sqrt n),
 \end{aligned}
 \tag{square-before-Poisson}
\]

内层仅在 n>0 非零。选 alpha_j 为 bar d_j 在[0,c)的代表，并记

\[
 A=(\alpha_1-\alpha_2)/c,\qquad
 \beta=2\theta(\sqrt{m_1}-\sqrt{m_2})/c.
\]

右侧整个表达式是非负平方和的展开，不是逐项非负。
对光滑紧支撑函数 `f(x)=eta(x/N)e(Ax+beta sqrt(x))` 作 Poisson：

\[
 \sum_n f(n)=\sum_{k\in\mathbb Z}\widehat f(k),\qquad
 \widehat f(k)=\int_0^\infty\eta(x/N)
                e((A-k)x+\beta\sqrt x)\,dx.
 \tag{quadratic-Poisson}
\]

这里 Fourier 使用负号，与
[前篇的补全证明](2026-08-31-conrey-di-arithmetic-completion.md) 一致。
f 向负半轴延拓为0后仍光滑；所有导数可积，Poisson 级数绝对收敛。

### 5.1 在整个积分支撑上排除非共振驻点

若 k!=A，则 c(A-k) 为非零整数，故 `|A-k|>=1/c`。
对 eta(x/N) 的整个支撑 x>=3N/4，有

\[
 \left|\frac{\beta}{2\sqrt x}\right|
 \le\frac{4(\sqrt2-1)}{\sqrt3\,c}
 =\frac{1-\delta_0}{c},\qquad
 \delta_0=1-\frac{4(\sqrt2-1)}{\sqrt3}>0.
 \tag{full-support-gap}
\]

用到了 `|sqrt(m_1)-sqrt(m_2)|<=(sqrt2-1)sqrt(N)` 和 theta<2。
delta_0>0 等价于 45<32 sqrt(2)，平方后为2025<2048。
所以相位 `Psi_k(x)=(A-k)x+beta sqrt(x)` 满足

\[
 |\Psi_k'(x)|\ge\delta_0|A-k|.
\]

这里固定选择较窄的 cutoff 是为了在**平滑后的整个支撑**上成立。
如果只知道 x in [N,2N] 上没有驻点，不足以估计延拓后的积分。
一个精确诊断是：取 N=10000、c=3、m_1=19881=141^2、
m_2=10201=101^2、theta=19/10、alpha_1=1、alpha_2=2、k=0。
此时 `Psi_k(x)=-x/3+(152/3)sqrt(x)`，在 x=5776=76^2 有驻点，
它位于 `(N/2,3N/4)`，但不在本篇 cutoff 的支撑内。这反驳的是
对任意较宽 cutoff 都可直接沿用无驻点论证的推断，不反驳三条最终估计。

令 x=Ny，则归一化相位一阶导数模至少
`delta_0 N|A-k|`，更高阶导数模为 `O_j(N|A-k|)`。
反复使用 `(2 pi i Psi')^(-1) d/dx` 分部积分，得到每个整数 p>=2

\[
 |\widehat f(k)|\le C_p N(N|A-k|)^{-p}\quad(k\ne A).
\]

各次导数中，分母的下界固定，上述高阶导数界保证每次都多得
`(N|A-k|)^(-1)`；eta 的导数固定且端点平坦。
因 c(A-k) 是非零整数，求和后有

\[
 \sum_{k\ne A}|\widehat f(k)|
 \le C_p N(c/N)^p.
 \tag{nonresonant-tail}
\]

这是对非零整数绝对 p 次幂倒数求和所得，常数与 c,N,A,theta 独立。
若 A 不是整数，所有 k 都属于此尾项；没有虚构一个共振频率。

### 5.2 共振正好迫使两个单位相等

若 k=A 为整数，因为 alpha_j in [0,c)，只能 A=k=0、alpha_1=alpha_2。
单位逆元映射为双射，因此 d_1=d_2。对共同的 d 求和得到精确项

\[
 r_c(m_1-m_2)J(m_1,m_2),
 \quad r_c(h)=\sum_{d\bmod c}^{*}e(hd/c),
 \quad J=\int_0^\infty\eta(x/N)e(\beta\sqrt x)\,dx.
 \tag{resonance-exact}
\]

Ramanujan 和满足 `|r_c(h)|<=gcd(c,h)`，并且 r_c(0)=phi(c)。
为说明这不是用错 Weil 的退化情形，可直接用
`r_c(h)=sum_(d|gcd(c,h))d mu(c/d)`：在模 p^a 上它依次为
`p^a-p^(a-1)`、`-p^(a-1)`、0，分别对应 h 被 p^a 整除、
恰被 p^(a-1) 整除、以及其余情形。逐素数相乘即得所写 gcd 界。

显然 |J|<=C N。若 h=m_1-m_2!=0，再作一次分部积分给出

\[
 |J|\ll\frac{\sqrt N}{|\beta|}
       \ll\frac{cN}{\theta|h|}.
 \tag{resonant-integral}
\]

第一步中相位导数为 beta/(2 sqrt(x))，其倒数及变差均为
`O(sqrt(N)/|beta|)`；eta(x/N) 的总变差固定。
第二步使用
`|sqrt(m_1)-sqrt(m_2)|=|h|/(sqrt(m_1)+sqrt(m_2))`
以及两项均不超过2N，故没有丢失一个 sqrt(N)。

### 5.3 全部配对求和及明确余项

共振对角 m_1=m_2 贡献至多 `C cN||b||^4`。
共振非对角由 (resonant-integral) 控制。对每个非零差 h，
用 Cauchy 或 `2|xy|<=|x|^2+|y|^2`，有
`sum_m |b_(m+h)b_m|<=||b||^2`。又有

\[
 \sum_{1\le h\le N}\frac{\gcd(h,c)}h
 =\sum_{d\mid c}\frac{\varphi(d)}d H_{\lfloor N/d\rfloor}
 \le\tau(c)H_N,
 \tag{gcd-harmonic}
\]

其中 H_0=0；等式用 `gcd(h,c)=sum_(d|gcd(h,c))phi(d)`。
此恒等式来自将1到 gcd(h,c) 的整数按约分后分母分类。

对每一组 m_1,m_2,d_1,d_2，(nonresonant-tail) 统一成立。
单位对数量不超过 c^2，且 `(sum_(m in I_N)|b_m|)^2<=N||b||^2`。
所以 (square-before-Poisson) 给出的**完整带余项估计**为

\[
 \boxed{|B_c|^2\le C_p\left[
 cN\{1+\theta^{-1}\tau(c)H_N\}
       +c^2N^2(c/N)^p\right]\|b\|_2^4,}
 \tag{quadratic-with-tail}
\]

对所有正整数 c,N、0<theta<2 和整数 p>=2 成立。
这一步没有把 c 接近 N 时并不小的非共振尾项消失掉。

## 6. 分开 c 接近 N 的范围，完成振荡界

固定 epsilon>0，令 `delta=min(epsilon,1/2)`，选整数
`p>=max(2,2/delta)`。若 N>=2 且 `c<=N^(1-delta)`，则

\[
 c^2N^2(c/N)^p\le cN,
\]

因为除以 cN 后不超过 `N^2 N^(-delta p)<=1`。
利用 `0<theta<2` 吸收无 theta 的常数项，并用
`tau(c)H_N <<_epsilon N^(2epsilon)`，从
(quadratic-with-tail) 开平方得到 Q-oscillatory。
约数和调和界均为初等：前篇给过 `tau(c)<<_eta c^eta`
的逐素数证明，且 H_N<=1+log N；各取充分小的 eta 即可。

若 `N^(1-delta)<c<=N`，不再使用尾项估计，而用已证明的 Q-hybrid：
因为 theta<2 且 c<=N，它给出 `|B_c|<<N||b||^2`。
同时

\[
 \theta^{-1/2}c^{1/2}N^{1/2+\epsilon}
 \ge2^{-1/2}N^{1+\epsilon-\delta/2}
 \ge2^{-1/2}N.
\]

所以这一范围也成立。N=1、c<=N 时只能 c=1，I_N 只有一个整数，
直接得到 |B_1|=||b||^2，用 theta<2 吸收常数即可。
至此三条二次和结论均已有证明。

## 7. 当前 DI 所需的两个尖点确实归约到这些经典和

DI11 当前取 S=1，谱展开所在群为 Gamma_0(r)。原刊 §9.1
出现的两个尖点是 infinity 与 1/s=1；后者等价于0。
不能把这里的 q=r 与前篇 Fourier 零频里的 S 混用。
下面对任意正整数 q 验证所需的对角尖点和。

令

\[
 \Gamma_0(q)=\left\{\begin{pmatrix}a&b\\qc&d\end{pmatrix}
       \in\mathrm{SL}_2(\mathbb Z)\right\},\qquad
 W_q=\begin{pmatrix}0&-q^{-1/2}\\q^{1/2}&0\end{pmatrix}.
\]

它将 infinity 送到0，并且直接矩阵相乘给出

\[
 W_q^{-1}\begin{pmatrix}a&b\\qc&d\end{pmatrix}W_q
       =\begin{pmatrix}d&-c\\-qb&a\end{pmatrix}.
 \tag{Fricke-exact}
\]

故 `W_q^(-1)Gamma_0(q)W_q=Gamma_0(q)`。取 infinity 的缩放矩阵为
单位阵，0 的为 W_q，1 的为 `T_1 W_q`，其中
`T_u=((1,u),(0,1))`，且 T_1 属于 Gamma_0(q)。这些都是宽度归一到1
的缩放：共轭后的相应尖点稳定子就是 `{±T_n:n in Z}`。

因此在这三个所选缩放下，对角双陪集均是
`Gamma_infinity \ Gamma_0(q) / Gamma_infinity`。固定正的左下角 c，
只有 q|c 时存在双陪集。每个模 c 单位 a 唯一给出
d=bar a mod c，选整数代表并设 b=(ad-1)/c，就得到矩阵。
左右整数平移分别改变 a 和 d 的 c 倍数，故这些是完整且不重复的
双陪集参数。于是对角尖点和恰为

\[
 S_{aa}(m,n;c)=K_c(m,n)\quad(q\mid c),
 \qquad a\in\{\infty,0,1\}
 \tag{actual-cusps}
\]

在所选宽度归一化下成立，没有额外 q、sqrt(q) 或相位因子。
这说的是**对角尖点和**，不把 infinity 到1的非对角和偷换成它。
后者仍由前篇 DI11 的准确对象承接；谱 Cauchy 所需的两份大筛
正是各自尖点的对角二次和。

若原刊对同一尖点采用另一个宽度为1的缩放，则在选定等价尖点后
相差右乘 T_u（以及无影响的符号）。共轭矩阵的两个对角元变为
a-uc、d+uc，故 Kloosterman 和只乘 `e((n-m)u)`。
这在 B_c 中可通过 `b_m -> b_m e(-mu)` 吸收，范数不变。
任意两个将 infinity 送到同一尖点的实行列式1矩阵之比为上三角；
稳定子宽度同为1迫使其对角比为1，才得到上述平移形式。
因此三条界不依赖于这个缩放选择，也不隐含一个原刊未使用的尖点。

## 8. 原刊接合、剩余工作与验收

已按原刊逐页核对：DI82 Proposition 3，(1.25)--(1.27)，p.229；
其 §5.1，pp.255--257，给出二次和方法；§9.1，pp.278--280，
确认当前两个尖点以及 Theorem 2 在 DI11 常规谱中的用途。

- [定义与定理部分](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0020.pdf)。
- [原刊第5节](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0024.pdf)。
- [原刊第9节](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0028.pdf)。

本篇为实际尖点重证了上述三条界，补出了原刊留作练习的混合大筛，
展开 Mellin 衰减与频率合并，并显式保留 Poisson 非共振尾项。
窄 cutoff 的选择只是保证本篇证明中的全支撑驻点排除，不把它
宣称为新发现的原刊勘误。

**剩余不是三个换名的条件接口。** 三条二次和界已经证明；但从它们
到谱 Theorem 2 还需要 Kuznetsov、所选 Bessel 权重及全部谱项的
合法接合。DI11 另需的 exceptional-spectrum 加权估计也仍待自证。
本篇没有证明这些内容，不能凭本篇或回归通过就宣布最终 Conrey 完成。

English summary: prove all three quadratic Kloosterman estimates needed at
the two actual cusps of the S=1 application, using a direct Gaussian hybrid
sieve and a full-support Poisson resonance analysis. The subsequent spectral
large sieve and exceptional-spectrum arguments remain open here.

独立审查应核对系数的共轭、Mellin 的1/(2 pi)、Gaussian 行和、
delta_0 的整个支撑、k=A 的整数条件、Ramanujan 退化、尾项求和、
c 接近 N 的分段，以及 Fricke 的矩阵和相位归一化。
最终 SHA 只运行允许的 Python/目标分类/chain-gap/diff 验证；
有限枚举仅作诊断。未获专属资源通知前不启动 Lean/Lake，源验证
不替代最终 main 集成验证或原生数学验收。
