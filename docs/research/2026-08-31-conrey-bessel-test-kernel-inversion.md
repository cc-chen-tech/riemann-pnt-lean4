# Conrey 的 DI 谱路线：实际 Bessel 测试核反演

先说结论：本篇不再将测试核反演作为未证输入。通过一维微分
算子的实际 Green 核，得到含离散项的 J 反演与 K 反演；再用
阶参数留数计算与绝对主化，证明预 Kuznetsov 所需的三个标量
积分恒等式。配套篇将这些结果接到实际模曲面谱和。

冻结基点 6c5b8d4dea1eb2f7bfcf4dd0d1c670884aac8308。
只新增纸面数学；不改冻结祖先、Lean、Lake 或契约。本篇使用
自伴算子的谱定理/Stone 公式这些通常的泛函分析定理，但实际
算子、边界条件、Green 核及谱测度均在这里计算；不假设某个
Bessel/Kuznetsov 反演公式。方法属于经典谱理论，不主张新定理。

所有测试函数 phi 属于 C_c^infty(0,infinity)，可为复值。
这是当前 DI 光滑权重实际需要的类别；不声称已经降至 C_c^3。
J、I、K 均为标准 Bessel 函数，正实数的幂用实对数定义。

## 1. 精确目标与两个微分算子

令 D=x partial_x，测度为 dx/x，定义微分表达式

\[
 A=-D^2-x^2,\qquad B=-D^2+x^2.
\]

变换 u=log x 将测度化为 du。A 在正无穷端必须另定边界，
不能将它当成有界下方的 Friedrichs 算子：势 -exp(2u) 向下
无界，且该端为 limit-circle。B 两端为 limit-point，且非负。

记 S_t(x)=J_(2it)(x)+J_(-2it)(x)，Q_t(x)=J_(2it)(x)-J_(-2it)(x)。
对 h in C_c^infty，后面证明

\[
 h(x)=\sum_{\substack{l\ge2\\l\ {m even}}}
          2lJ_l(x)\int_0^\infty J_l(y)h(y)\frac{dy}{y}
       +\int_{\mathbb R}\frac{tS_t(x)}{\sinh(2\pi t)}
                   \left(\int_0^\infty S_t(y)h(y)\frac{dy}{y}\right)dt,
 \tag{actual-even-J-inversion}
\]

\[
 h(x)=\frac4{\pi^2}\int_{\mathbb R}t\sinh(2\pi t)K_{2it}(x)
                   \left(\int_0^\infty K_{2it}(y)h(y)\frac{dy}{y}\right)dt.
 \tag{actual-K-inversion}
\]

两式先是 L2 等式；对上述测试函数，右侧在 x 的紧子集上一致
绝对收敛，因而也是逐点等式。第一式的离散项不能删除。

## 2. 端点、Green 核与谱测度

### 2.1 A 的实际自伴实现

最大域由 f、Df 局部绝对连续且 f、Af 属于 L2(dx/x) 的函数
组成。取 W_D(f,g)=f Dg-(Df)g。A 的定义域再要求

\[
 \lim_{x\to\infty}W_D(f,J_0)(x)=0.
 \tag{cosine-end-boundary}
\]

这是实际的余弦端点条件，不是一个未经定义的“适当边界”。
J_0、Y_0 在 infinity 均为 O(x^(-1/2))，故在该端都平方可积。
对最大域函数，用 J_0、Y_0 的变参数表达式，W 的导数是 f 或
Af 与这两个平方可积函数的乘积。因此两条端点迹存在，并且
连续依赖局部 Cauchy 数据和图范数。该边界条件定义闭域。
Green 恒等式的 infinity 通量在这个域上为零。

在0端，lambda=-nu^2、Re nu>0 的两个基本解分别为 J_nu 和
J_(-nu)，其首项为常数乘 x^nu、x^(-nu)；只有前者平方可积。
整数阶按极限使用 Y 解。故0为 limit-point，无需另加条件。
也可在 u 变量中使用势在负半轴有界且趋零的积分方程，证明
最大域函数的相互 Green 通量在负无穷处为零。

对非实 lambda=-nu^2，选择 Re nu>0。在 infinity 满足边界的解为
J_nu+J_(-nu)：两者的大参数正弦项相消，留下余弦项。由幂级数
首项及常 Wronskian，

\[
 W_D(J_\nu,J_{-\nu})=-\frac{2\sin(\pi\nu)}\pi.
\]

因此 (A-lambda)^(-1) 的候选核（相对于 dy/y）是

\[
 R_\lambda^A(x,y)=\frac\pi{2\sin(\pi\nu)}
       J_\nu(x_<)\bigl(J_\nu(x_>)+J_{-\nu}(x_>)\bigr).
 \tag{actual-A-Green}
\]

其 D 导数在 x=y 的跳跃为 -1，故 (A-lambda)R=delta，符号与
微分表达式的负二阶导数一致。对紧支撑光滑 h，核积分在0端
为 J_nu 的倍数，在 infinity 为边界解的倍数，所以属于上述域。
Green 恒等式的虚部给
||R_lambda h||_2 <= |Im lambda|^(-1)||h||_2。
于是核算子延拓到全部 L2；图范数闭性保留方程与端点迹。
对 lambda 与 conjugate(lambda) 都有满射逆，故这个闭对称算子
实际自伴。这里没有通过形式核等式跳过自伴性或满射。

### 2.2 A 的离散项与连续跳跃

核在 nu=l>0 偶数处有简单极点。在 lambda=-l^2 附近，

\[
 R_\lambda^A(x,y)=-\frac{2lJ_l(x)J_l(y)}{\lambda+l^2}+O(1).
\]

故该特征投影的核是2lJ_l(x)J_l(y)。特别地
integral J_l(x)^2 dx/x=1/(2l)。正奇数处，J_(-l)=-J_l，
分子的零消去分母；那里没有该边界条件的特征值。

令 lambda=k^2>0。上、下岸分别为 nu=-ik、ik。直接相减得

\[
 \frac{R_{k^2+i0}^A-R_{k^2-i0}^A}{2\pi i}(x,y)
   =\frac{(J_{ik}(x)+J_{-ik}(x))(J_{ik}(y)+J_{-ik}(y))}
           {4\sinh(\pi k)}.
 \tag{actual-A-Stone-density}
\]

这是关于 d(lambda) 的密度。乘 d(lambda)=2k dk、再令 k=2t，
正 t 轴的系数是2t/sinh(2pi t)；改为全轴就是第一节的系数。
阈值0不是特征值：J_0 在0不平方可积，Y_0 也不平方可积。
对紧支撑配对，核在正轴任一远离0的紧区间具有光滑边界值，
故 Stone 公式在那里只有上述绝对连续测度；负轴只有已列极点。
可能剩在单点0的测度只能是原子，而该原子已排除。
由谱定理的完备性及紧支撑函数的稠密性，得到全部 L2 的分解，
没有保留一个未知的奇异连续分量。

### 2.3 B 的 Green 核与 K 反演

B 在 u 坐标中的势为 exp(2u)。负无穷端仍为 limit-point；
正无穷端的 I_nu 指数增长、K_nu 指数衰减，所以也为 limit-point。
积分分部或闭二次型 integral(|Dh|^2+x^2|h|^2)dx/x 给非负自伴
实现。对 lambda=-nu^2、Re nu>0，其实际 Green 核为

\[
 R_\lambda^B(x,y)=I_\nu(x_<)K_\nu(x_>),
 \qquad W_D(I_\nu,K_\nu)=-1.
 \tag{actual-B-Green}
\]

同样可由核作用于紧支撑函数及非实参数的范数界直接核对满射。
连接式 K_nu=pi(I_(-nu)-I_nu)/(2sin(pi nu)) 给出

\[
 \frac{R_{k^2+i0}^B-R_{k^2-i0}^B}{2\pi i}(x,y)
     =\frac{\sinh(\pi k)}{\pi^2}K_{ik}(x)K_{ik}(y).
 \tag{actual-B-Stone-density}
\]

无负特征值来自非负性；正参数的任何非零解在0都含 x^(ik)
或 x^(-ik)，不平方可积；0处的常数/对数行为也不平方可积。
核无其他极点，紧支撑配对的边界值排除其余奇异谱。将密度乘
2k dk，再作 k=2t 及全轴转换，就得到4/pi^2的实际 K 反演。

## 3. 使反演与后续换序合法的估计

以下常数可以依赖测试函数支撑的固定紧区间与所取导数阶，
不依赖积分谱参数；追踪变化尺度的 DI 估计仍在后续单列。

### 3.1 J 的全正轴主化

Poisson 表示直接由幂级数与 Beta 积分得到

\[
 J_\nu(x)=\frac{(x/2)^\nu}{\sqrt\pi\Gamma(\nu+1/2)}
             \int_{-1}^1 e^{ixv}(1-v^2)^{\nu-1/2}dv
 \quad(\operatorname{Re}\nu>-1/2).
\]

对 nu=2it，用 |Gamma(1/2+2it)|^2=pi/cosh(2pi t)，因此
|J_(2it)(x)| <= C exp(pi|t|)，统一于全部 x>0。
对 x >= (1+2|t|)^2，还有
|J_(2it)(x)| <= C exp(pi|t|)x^(-1/2)。具体地，令
w=sqrt(x)J_(2it)(x)，则
w''+(1+(4t^2+1/4)/x^2)w=0。
从 infinity 的两项正弦/余弦数据作 Volterra 积分，余项的绝对
积分至多 (4t^2+1/4)/x；迭代指数主化给上述统一界。
这说明大参数估计的使用范围，不将固定阶渐近式外推到任意阶。

分割于 (1+2|t|)^2，得到对0<x<=b

\[
 \int_x^\infty |S_t(u)|\frac{du}{u}
   \ll_b e^{\pi|t|}\bigl(1+|\log x|+\log(2+|t|)\bigr).
 \tag{absolute-J-tail}
\]

对整数 l，Bessel 圆积分给 |J_l(x)|<=1；相同的 Volterra 论证
在 x>=(1+l)^2 给统一 O(x^(-1/2))，故其尾积分也只有 log(l+2)
的增长。紧支撑配对则有更强的阶衰减：

\[
 |J_l(x)|\le \frac{(b/2)^l}{l!}e^{b^2/4}\quad(0<x\le b).
 \tag{integer-order-bound}
\]

### 3.2 谱变换的快速衰减

S_t 是 A 的特征函数，特征值4t^2。对 h in C_c^infty 反复分部
积分，没有端点通量；任意整数 N>=0 有

\[
 \left|\int S_t(x)h(x)\frac{dx}{x}\right|
      \ll_{h,N} e^{\pi|t|}(1+|t|)^{-N}.
 \tag{J-transform-decay}
\]

在 |t|>=1 时用 A 的足够多次幂，其余参数在紧集上连续。
导数版可用同样方法或局部 Bessel 方程得到，足够保证紧 x
区间上的一致收敛。

对 K，使用
K_(2it)(x)=(1/2)integral_R exp(-x cosh u+2it u)du。
将 u 移到 u+i sign(t)(pi/2-1/(1+2|t|))；两端因 cosh 增长
消失，得到

\[
 |K_{2it}(x)|\ll e^{-\pi|t|}
                       K_0\left(\frac{c x}{1+|t|}\right)
 \ll_b e^{-\pi|t|}\bigl(1+|\log x|+\log(2+|t|)\bigr)
 \quad(0<x\le b).
 \tag{K-order-decay}
\]

对支撑在 [a,b] 内的 h，再用 B 的多次分部积分，吸收 log 因子，得

\[
 \left|\int K_{2it}(x)h(x)\frac{dx}{x}\right|
          \ll_{h,N}e^{-\pi|t|}(1+|t|)^{-N}.
 \tag{K-transform-decay}
\]

这些界使两条反演的连续积分在紧 x 上绝对收敛；离散项由
(integer-order-bound) 绝对收敛。于是 L2 反演升级为逐点反演。

## 4. 从偶阶反演到实际 holomorphic 补项

定义

\[
 \widetilde\phi(l)=\int_0^\infty J_l(x)\phi(x)\frac{dx}{x},\qquad
 \phi_B(x)=\sum_{\substack{l\ge1\\l\ {m odd}}}
                      2l\widetilde\phi(l)J_l(x),\qquad
 \phi_H=\phi-\phi_B,
\]

\[
 h(x)=-x\left(\frac{\phi(x)}x\right)',\qquad
 f(t)=\int S_t(x)h(x)\frac{dx}{x}
     =-\int S_t(x)\left(\frac{\phi(x)}x\right)'dx.
 \tag{actual-f-seed}
\]

h 仍为紧支撑光滑函数。令 T g(x)=x integral_x^infty g(u)du/u；
在所用函数上积分绝对收敛，且 Th=phi。
第3节界使 T 可穿过 h 反演中的连续积分和离散和：连续项是
exp(pi|t|) 的尾界乘 exp(pi|t|)(1+|t|)^(-N) 的变换，再乘
t/sinh(2pi t)；指数恰好抵消，剩下可积快速衰减。
离散项的 log(l+2) 尾界乘阶乘衰减，也绝对可和。

偶阶离散项经 T 后恰为 phi_B，下面给出不省略的代数核对。
令 a_l=tilde phi(l)。分部积分及 J_l'=(J_(l-1)-J_(l+1))/2 给
h_(2k)=(a_(2k-1)-a_(2k+1))/2。另一方面，递推式给

\[
 -x\left(\frac{2lJ_l(x)}x\right)'
       =(1-l)J_{l-1}(x)+(1+l)J_{l+1}(x).
\]

将它乘 a_l 并按正奇数 l 求和，J_(2k) 的系数成为
2k(a_(2k-1)-a_(2k+1))=4k h_(2k)。l=1 的 J_0 项系数为0，
所以没有遗漏阈值补项。两边除以 x 在 infinity 都趋0：
phi_B 有界，T 离散和的尾部趋零；因此积分常数也为0。

于是实际得到

\[
 \boxed{\quad
 x\int_x^\infty\int_{\mathbb R}
             \frac{t f(t)}{\sinh(2\pi t)}S_t(u)dt\frac{du}{u}
       =\phi_H(x).
 \quad}
 \tag{actual-integrated-J-inversion}
\]

此结论同时证明 phi_H 在0为 O_phi(x)，而不是仍然紧支撑；
其小参数尾必须在几何模数和中保留。

## 5. 两条 J 标量卷积：从实际留数求出

记

\[
 H(r,t)=\frac{\cosh(\pi r)}{\cosh(\pi(t-r))\cosh(\pi(t+r))},
 \qquad
 \widehat\phi(r)=\frac{\pi i}{2\sinh(\pi r)}
                       \int_0^\infty Q_r(x)\phi(x)\frac{dx}{x}.
 \tag{actual-hat-transform}
\]

r=0 按可去极限；需要的异常参数 r=i nu，0<nu<=1/4，也在
全纯带 |Im r|<1/2 内。这里显式保留 i 和负号的等价关系：
pi i/2=-pi/(2i)。

### 5.1 闭合阶轮廓的合法性

下列计算令 v=2it，把整条实 t 轴改为向上的虚 v 轴；向右
闭合时方向是顺时针。幂级数及 Gamma 的右半平面 Stirling 界给

\[
 |J_{\sigma+i\tau}(x)|+|I_{\sigma+i\tau}(x)|
 \ll_b \frac{(x/2)^\sigma}{|\Gamma(1+\sigma+i\tau)|}
                 \exp\left(\frac{b^2}{4(1+\sigma)}\right),
 \qquad 0<x\le b,\quad\sigma\ge0.
\]

倒 Gamma 的指数增长不超过 exp(pi|tau|/2)；所用三角分母
衰减 exp(-pi|tau|) 或 exp(-pi|tau|/2)。在后一个临界情形，
先把 x 与紧支撑种子配对并对其反复使用 Bessel 微分方程，
得到任意次 |v|^(-2N)，再闭合轮廓。右边取避开整数极点的
固定距离竖线；Gamma 的阶乘增长使竖边积分趋零。
因此下面第二个恒等式可先在紧支撑分布意义求出，再由其
平滑代表确认；不将未配对的条件收敛积分冒充绝对收敛。

### 5.2 H 卷积

由于 f 与 H 为偶函数，先计算
B_r(x)=integral_R H(r,t)S_t(x)dt。
在 v 变量中 H=2cosh(pi r)/(cos(pi v)+cosh(2pi r))。
正实部的极点为 v=2k+1 plus/minus 2ir，k>=0；留数分别为
plus/minus 1/(pi i sinh(pi r))。闭合方向及 dt=dv/(2i) 给

\[
 B_r(x)=\frac2{i\sinh(\pi r)}
        \sum_{k\ge0}\bigl(J_{2k+1-2ir}(x)-J_{2k+1+2ir}(x)\bigr).
\]

先取实 r>0；阶乘界允许逐项求导，导数递推式望远镜相消，得
B_r'(x)=-Q_r(x)/(i sinh(pi r))。
随后用 |Im r|<1/2 上的全纯性延拓，包含0的可去极限和所有
实际异常参数。对 f 的紧支撑定义分部积分，得到

\[
 \int_{\mathbb R}H(r,t)f(t)dt=\frac2\pi\widehat\phi(r).
 \tag{actual-H-f-convolution}
\]

### 5.3 对角卷积

同样的 v 轮廓中 t/sinh(pi t)=v/(2sin(pi v/2))。
正极点 v=2k 的留数为2k(-1)^k/pi。得到的 Bessel 级数是
4sum_(k>=1)k(-1)^(k+1)J_(2k)(x)=xJ_1(x)，最后等号由阶
递推逐项相消。按5.1先与种子配对，且 (xJ_1)'=xJ_0，故

\[
 \int_{\mathbb R}\frac{t f(t)}{\sinh(\pi t)}dt
                         =\int_0^\infty J_0(x)\phi(x)dx.
 \tag{actual-diagonal-convolution}
\]

左侧由第3节快速衰减绝对收敛；t=0 为可去极限。

## 6. K 卷积及全部常数

实际恒等式是

\[
 \boxed{\int_{\mathbb R}t\sinh(2\pi t)H(r,t)K_{2it}(x)dt
                      =x\cosh(\pi r)K_{2ir}(x).}
 \tag{actual-H-K-convolution}
\]

左侧对固定 r 在 |Im r|<1/2 内绝对收敛：sinh(2pi t)H
在实 t 无穷处有界，K 的阶衰减仍给 exp(-pi|t|)。
给出直接计算以确定符号与 cosh，不能仅引用原刊(4.11)。
令 v=2it，以 K_v=pi(I_(-v)-I_v)/(2sin(pi v)) 展开。
利用 v 变号与偶性，左侧恰为

\[
 \frac\pi{4i}\int_{-i\infty}^{i\infty}
       v\frac{2\cosh(\pi r)}{\cos(\pi v)+\cosh(2\pi r)}I_v(x)dv.
\]

按5.1向右闭合，并用
sum_(k>=0)(2k+1+alpha)I_(2k+1+alpha)(x)=x I_alpha(x)/2，
得到
pi x(I_(-2ir)(x)-I_(2ir)(x))/(4i sinh(pi r))。
再用 K 的连接式及 sinh(2pi r)=2sinh(pi r)cosh(pi r)，正好是
上式右侧。先实 r>0，随后全纯延拓，r=0 用可去极限。

若 g(t)=integral K_(2it)(y)phi(y)dy/y^2，则 K 反演和本式给

\[
 \frac4{\pi^2}\int_{\mathbb R}t\sinh(2\pi t)K_{2it}(x)g(t)dt
                 =\frac{\phi(x)}x,
\]

\[
 \int_{\mathbb R}t\sinh(2\pi t)H(r,t)g(t)dt
           =\cosh(\pi r)\int_0^\infty K_{2ir}(y)\phi(y)\frac{dy}{y}.
 \tag{actual-K-test-transfer}
\]

在后一式中，y 支撑紧且有正下界，绝对主化由上述 K 阶衰减
给出，因此这次 Fubini 不依赖前一个反演等式。

## 7. 预 Kuznetsov 中要用的统一绝对界

定义 D核为前篇已纠正的
D_(2it)(x)=-(2it/sinh(pi t))integral_(gamma_up)K_(2it)(xv)dv/v。
前篇实际端点连接证明
D_(2it)(x)=(2pi t/sinh(2pi t))integral_x^infty S_t(u)du/u。
对0<x<=b，由3节有

\[
 \int_{\mathbb R}|D_{2it}(x)f(t)|dt
                         \ll_\phi 1+|\log x|,
\]

\[
 \int_{\mathbb R}|t\sinh(2\pi t)K_{2it}(x)g(t)|dt
                         \ll_\phi 1+|\log x|.
 \tag{absolute-geometric-test-bounds}
\]

两条主化都使用任意阶快速衰减，不假定模数和的相位相消。
对实 r>=0，还需要谱侧的绝对值，而不仅是卷积后的相消结果：

\[
 \int_{\mathbb R}|H(r,t)f(t)|dt\ll_{\phi,N}(1+r)^{-N},
\]

\[
 \int_{\mathbb R}|H(r,t)t\sinh(2\pi t)g(t)|dt
                                      \ll_{\phi,N}(1+r)^{-N}.
 \tag{absolute-spectral-test-bounds}
\]

证明可分割 |t|<=r/2、r/2<|t|<2r、|t|>=2r：H 由
C exp(-pi r-2pi(|t|-r)_+) 主化，而 f 与 t sinh g 均由
exp(pi|t|) 乘任意负幂主化；在中段只留下 exp(-pi||t|-r|)。
两外段指数衰减。0<=r<=1 直接用统一可积界。
异常 r=i nu、0<=nu<=1/4 的 H 在这个紧区间也统一受控，且
对大 |t| 为 O(exp(-2pi|t|))。

这些正是下篇几何模数和、离散 Maass 和全尖点连续谱三种
换序各自使用的界；不把它们合并成一个宽泛“允许换序”假设。

## 8. 来源及边界

- [DI82 §4，pp.254--255](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0023.pdf)
  给出目标积分操作，但末段明确省略若干收敛细节。本篇以实际
  Green 核及绝对主化补出所需光滑类别，不引用其反演作证明输入。
- [DLMF 10.9.4](https://dlmf.nist.gov/10.9.E4) 的 Poisson 表示及
  [10.17](https://dlmf.nist.gov/10.17) 的 Bessel 大参数展开，用于
  核对基本函数约定；文中另给出需要的一致参数范围及 Volterra 界。
- 原刊(4.11)印为负的 H-K 积分等于 xK；在这里固定的标准
  K 与 H 定义下，实际式是正的积分等于 x cosh(pi r)K。
  第6节提供逐步留数证明；不能仅改掉印刷负号却漏掉 cosh。

本篇不包含 X 放大异常谱、DI11 参数预算或最终 Conrey 比例。
它完成的是配套实际测试核公式所必需的反演与标量换序；机器
形式化仍待独占资源窗口。数学证明、有限诊断和回归测试分开记录。

English summary: construct the cosine-boundary J operator and the positive
K operator, compute their Green kernels and Stone measures, and prove the
required Bessel inversions including discrete residues. Derive all scalar
test convolutions by order-contour residues and give separate absolute bounds
for geometric and spectral exchanges. No Kuznetsov inversion is assumed.
