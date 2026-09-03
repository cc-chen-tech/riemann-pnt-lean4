# Conrey 的变化尺度输入：光滑 Bessel 核的统一谱衰减

先说结论：本篇证明完整 DI11 的 S=1 应用所需的光滑变化尺度
测试核估计。通过一个固定区间函数的 Fourier 变换，直接控制
实 Maass、连续谱、全纯谱及异常谱；不引用待证的 DI Lemma 7.1。
异常参数趋于0时保留必要的对数，实谱转折尺度也明确保留。

冻结基点 46b49ada33a37605565aa60f203827b96277d8ce。
这里只新增纸面证明，不新增 Lean、Lake 或条件契约。

## 1. 固定轮廓、实际变换及目标

固定 0<kappa<K<infinity。令 h 属于 C_c^infinity((kappa,K))，
可以复值；给物理核尺度 a>0，置 f_a(x)=h(x/a)。用 S_J(h)
表示至多 J 阶导数的最大上确界之和。所有常数可依赖 kappa,K
和有限个 S_J，但不依赖 a、谱参数或最小正异常参数。

沿用已证明的实际谱变换：

\[
 \widetilde f(l)=\int_0^\infty J_l(x)f(x)\frac{dx}{x},
\]

\[
 \widehat f(r)=\frac{\pi i}{2\sinh(\pi r)}
     \int_0^\infty(J_{2ir}(x)-J_{-2ir}(x))f(x)\frac{dx}{x},
 \qquad
 \check f(r)=2\cosh(\pi r)\int_0^\infty K_{2ir}(x)f(x)\frac{dx}{x}.
 \tag{actual-smooth-transforms}
\]

hat 在 r=0 按可去极限解释；check 中保留标准 K 函数对应的2。
设 T=1+a、L_a=1+log_+(1/a)。本篇证明：对任意整数 A>=0，
存在有限 J=J(A)，使所有实 r 及整数 l>=1 满足

\[
 \boxed{|\widehat f_a(r)|+|\check f_a(r)|
     \le C_A S_J(h)\frac{L_a}{T}(1+|r|/T)^{-A},}
 \tag{uniform-real-spectral-envelope}
\]

\[
 \boxed{|\widetilde f_a(l)|
     \le C_A S_J(h)\frac1T(1+l/T)^{-A}.}
 \tag{uniform-holomorphic-envelope}
\]

对 0<=nu<=1/4，还证明

\[
 \boxed{|\widehat f_a(i\nu)|+|\check f_a(i\nu)|
    \le C S_J(h)\frac{L_a}{1+a}(1+a^{-1})^{2\nu}.}
 \tag{uniform-exceptional-envelope}
\]

本篇假定光滑轮廓具有足够多的受控导数，不宣称仅有两阶导数
就能得到任意阶谱衰减。完整 DI11 使用的光滑权重符合这个范围。

## 2. 一维 Fourier 对象与准确积分表示

定义

\[
 H(v)=\int_\kappa^K h(u)e^{ivu}\frac{du}{u},\qquad
 F(v)=\frac{H(v)+H(-v)}2
     =\int_\kappa^K h(u)\cos(vu)\frac{du}{u}.
\]

H 为复值 Schwartz 函数，F 为复值偶 Schwartz 函数。更具体地，
对任意 j,B>=0，由在 u 上分部积分 B 次，

\[
       |H^{(j)}(v)|+|F^{(j)}(v)|
                   \le C_{j,B}S_{j+B}(h)(1+|v|)^{-B}.
 \tag{profile-Fourier-seminorms}
\]

端点项为0，因为 h 的支撑紧包含在 (kappa,K)；u 的正负幂在
这个固定区间上有界。F 的偶性给 F'(0)=0。

前序 [小尺度核第3节](2026-08-31-conrey-compensated-small-scale-kernel.md)
已从实际一维 Bessel 积分证明

\[
 \widehat f_a(r)=2\int_0^\infty\cos(2rt)F(a\cosh t)dt,
 \qquad
 \check f_a(r)=2\int_0^\infty\cos(2rt)F(a\sinh t)dt.
 \tag{actual-cosine-representations}
\]

它们对实 r 及 r=i nu、0<=nu<=1/4 均成立。原始一维振荡表示
先在有限 t 上换序，再以分部积分控制尾项；完成 u 积分后，
当前 Schwartz 预算使显示的 t 积分绝对收敛。

对整数 l>=1，用 J_l 的单位圆积分，有限角区间允许直接换序：

\[
 \widetilde f_a(l)=\frac1{2\pi}\int_0^{2\pi}
                    e^{-il\theta}H(a\sin\theta)d\theta.
 \tag{actual-circle-representation}
\]

因此本篇后续只需估计这三个实际振幅的导数和 L1 范数。

## 3. 小物理尺度 0<a<=1

设 g_+(t)=F(a cosh t)、g_-(t)=F(a sinh t)。两个 g 都是光滑
偶函数，因而在0处的所有奇数阶导数为0；在无穷处任意阶导数
衰减。由 (profile-Fourier-seminorms)，

\[
             \|g_+\|_{L^1(0,\infty)}+
             \|g_-\|_{L^1(0,\infty)}\ll S_J(h)L_a.
 \tag{small-scale-zero-derivative}
\]

证明是在 t<=1、1<=t<=1+log(1/a)、剩余尾部分段；中段长度
产生 log(1/a)，尾部因 a sinh t、a cosh t 与 a exp(t) 可比而可积。

任意固定 k>=1 则有不含对数的

\[
             \|g_+^{(k)}\|_1+\|g_-^{(k)}\|_1
                                         \ll_k S_{J(k)}(h).
 \tag{small-scale-positive-derivatives}
\]

在 t<=1，由链式法则、a<=1 和 F 的有界导数即可。t>=1 时置
v=a cosh t 或 a sinh t，dt 与 dv/v 可比；每个 k 阶导数都是
O_k(v^j |F^(j)(v)|)、1<=j<=k 的有限和。在 v<=1，j=1 时
vF'(v)=O(v^2)，j>=2 时 v^j F^(j)(v)=O(v^2)；在 v>=1 使用
Schwartz 衰减。故这些函数对 dv/v 的积分一致有界。

在余弦积分中分部积分任意偶数次，不出现0处的边界项，也无
无穷端点项。结合零阶界，得到
|hat f_a(r)|+|check f_a(r)|<=C_A S_J(h)L_a(1+|r|)^(-A)。
因为1<=T<=2，这就是 (uniform-real-spectral-envelope) 的小尺度部分。

对全纯项，theta -> H(a sin theta) 是光滑周期函数；a<=1 时，
任意固定阶导数的 L1 范数由有限个 S_J 一致控制。单位圆上
分部积分给 |tilde f_a(l)|<=C_A S_J(h)(1+l)^(-A)，亦得到目标。

## 4. 大物理尺度 a>=1 及谱转折区

### 4.1 hat 振幅

对 g_+(t)=F(a cosh t)，所有链式导数项都受
C_k sum_(j<=k) v^j|F^(j)(v)| 控制，v=a cosh t>=a。
给任意 B>0，在 Fourier 估计中取更高阶衰减后，

\[
                    \|g_+^{(k)}\|_1
                         \ll_{k,B} S_J(h)a^{-B}.
 \tag{large-scale-hat-derivatives}
\]

例如被积函数可界为 C(a cosh t)^(-B)，其积分为 O_B(a^(-B))。
在余弦积分中取足够多次偶数阶分部积分，即有比目标更强的
a 与 r 双重衰减。特别满足目标中的 a^(-1)(1+|r|/a)^(-A)。

### 4.2 check 振幅

置 v=a sinh t，dt=dv/sqrt(a^2+v^2)。第 k 阶 t 导数是
F^(j)(v) 乘 v 与 sqrt(a^2+v^2) 的至多 j 次乘积的有限和，
j<=k。因此对所有 k>=0，

\[
 \|g_-^{(k)}\|_1\ll_k S_J(h)a^{k-1}.
 \tag{large-scale-check-derivatives}
\]

确实 a>=1 时 (a+v)^j<=a^j(1+v)^j，且
1/sqrt(a^2+v^2)<=1/a；Schwartz 衰减使余下 v 积分有界。
结合 k=0 与足够大的偶数 k 的余弦分部积分，得到

\[
                |\check f_a(r)|
                     \ll_A S_J(h)a^{-1}(1+|r|/a)^{-A}.
\]

所以 r 与 a 可比的转折区并未丢弃：它被宽度 O(a)、高度 O(1/a)
的统一包络覆盖，而不是用固定小尺度的 r 衰减误套在所有 a 上。

### 4.3 全纯振幅

对周期振幅 H(a sin theta)，任意 k 阶导数是至多 k 个 a 因子
乘 H 的相应导数及有界三角函数的有限和。
在 sin theta 的零点附近，用距离零点的局部坐标，积分
(1+a|sin theta|)^(-B)=O(1/a)；远离零点，Schwartz 衰减给
O(a^(-B))。故

\[
       \|\partial_\theta^k H(a\sin\theta)\|_{L^1(0,2\pi)}
                            \ll_k S_J(h)a^{k-1}.
\]

单位圆的周期分部积分没有边界项。结合零阶与高阶界，得
|tilde f_a(l)|<=C_A S_J(h)a^(-1)(1+l/a)^(-A)。
连同第3节，实谱及全纯谱两条统一包络均已证明。

## 5. 异常谱：在 nu=0 附近仍一致

在 (actual-cosine-representations) 中，r=i nu 把余弦替换为
cosh(alpha t)，其中 alpha=2nu 属于 [0,1/2]。

若 a<=1，t<=1 部分一致有界。t>=1 时 v 与 a exp(t) 可比，
用 |F(v)|<=C min(1,v^(-2))，在 t=log(1/a) 的固定邻域处分段。
主体至多常数乘

\[
 \int_0^{\log(1/a)}\cosh(\alpha t)dt
       +a^{-2}\int_{\log(1/a)}^\infty e^{-2t}\cosh(\alpha t)dt
             \ll (1+\log(1/a))a^{-\alpha}.
\]

第一积分在 alpha=0 是 log(1/a)，不能换成一个一致有界常数。
第二积分的分母 2-alpha、2+alpha 在当前闭区间上远离0。

若 a>=1，hat 振幅的快速衰减足以支付 cosh(alpha t)，给
O(S_J(h)/a)。check 振幅置 v=a sinh t 后，
cosh(alpha t)<=C(1+v/a)^(1/2)，而 dt<=dv/a，仍给同一上界。
于是两种异常变换统一受

\[
 C S_J(h)\frac{L_a}{1+a}(1+a^{-1})^\alpha
\]

控制。没有出现 1/nu 或最小异常谱隙的倒数。该式也覆盖 nu=0，
但在谱分类中 r=0 仍属于普通谱。

## 6. 直接支付三类普通谱大筛的预算

给整数层数 q>=1、两个尺度 M,N>=1，尖点属于 infinity、0/1。
已有三类普通谱累积大筛，对谱高度 H>=1 的每个实际系数平方和
分别给 (H^2+M^(1+eta)/q)||a_m||_2^2，以及 N、b_n 的同式。
全纯项保留 Gamma(k)/(4pi)^(k-1) 与指标归一化，连续谱遍历
全部 Eisenstein 尖点；这些都不是可以随意删掉的权重。

对任一类普通谱，将 |r|<=T 或 k<=T 作为首块，再取高度
2^j T 到2^(j+1)T。用上面包络，取 A>2，几何级数给出

\[
 \sum_{\rm ordinary} |\mathcal T_f(r)|\,|A(r)|^2
       \ll_\eta S_J(h)\frac{L_a}{T}
                 (T^2+M^{1+\eta}/q)\|a\|_2^2.
 \tag{actual-weighted-ordinary-square}
\]

这里 sum 也代表实际连续谱积分及其谱权重；对全纯项用 l=k-1
替代 k，只改变固定常数，最低 k=2 仍在首块中。
由带权 Cauchy，实际双线性普通谱部分绝对值至多

\[
 C_\eta S_J(h)\frac{L_a}{T}
  (T^2+M^{1+\eta}/q)^{1/2}
  (T^2+N^{1+\eta}/q)^{1/2}\|a\|_2\|b\|_2.
 \tag{actual-weighted-ordinary-bilinear}
\]

系数可以复值并带任意单位模扭曲。这个预算同时证明普通谱
各次求和/积分的绝对主化，后篇将它接入实际跨尖点几何式。

## 7. 来源与边界

原刊对照为 DI Section 7，pp.264--267 的 Lemma 7.1：
[原刊扫描](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0026.pdf)。
本篇假设光滑固定轮廓，使用实际 Fourier/余弦表示，不照搬
原刊有限导数的 Mellin--Barnes 证明，也不使用其异常参数趋0
时缺少一致对数的字面 (7.1)。所有尺度及对数均在当前公式中。

本篇只证明测试核与实际普通谱预算。完整 DI11 S=1 的变量
分离、层数平均及异常项由配套篇证明；最终 Conrey 与机器
形式化不能仅凭这些核估计宣布完成。

### English summary

For a smooth fixed profile at physical scale a, the actual Bessel
transforms have ordinary-spectrum envelope
L_a/(1+a) times (1+|r|/(1+a))^(-A), with a corresponding holomorphic
bound. The proof uses Fourier transforms composed with cosh, sinh and
sin, retaining the transition range. Exceptional transforms are bounded
by L_a/(1+a) times (1+a^(-1))^(2nu), uniformly through nu=0.
Dyadic spectral summation gives the precise ordinary bilinear budget.
