# Conrey 的 DI 谱路线：小尺度差核与零谱参数的一致控制

先说结论：两个相邻尺度的测试函数相减，可以消去零谱参数处的
对数增长，同时保留异常谱的尺度放大。本篇证明该差核的实谱快速
衰减、全纯阶数衰减及异常谱的正下界；下一篇据此证明实际固定
层数的加权异常谱大筛。不用一个在参数趋零时不一致的常数替代
证明，也不把固定层数结果冒充跨层数平均的 DI11。

冻结基点为 7905ef19c761d08396d462a8a9a19f8acd75ab18。
沿用该基点的
[实际有符号 Kuznetsov 归一化](2026-08-31-conrey-actual-signed-kuznetsov.md)。
本篇只新增纸面证明；没有 Lean、Lake 或契约变更。

## 1. 变换、范围与本次实际输出

对 phi 属于 C_c^infty(0,infinity)，约定

\[
 \widetilde\phi(l)=\int J_l(x)\phi(x)\frac{dx}{x},\qquad
 \widehat\phi(r)=\frac{\pi i}{2\sinh\pi r}
                  \int(J_{2ir}(x)-J_{-2ir}(x))\phi(x)\frac{dx}{x},
\]

\[
 \check\phi(r)=2\cosh\pi r\int K_{2ir}(x)\phi(x)\frac{dx}{x}.
 \tag{actual-transforms}
\]

hat(0) 按可去极限，即积分核 -pi Y_0(x)。异常参数写成
r=i nu，0<=nu<=1/4，另记 a=2nu 属于 [0,1/2]；本篇的 a
不是 Fourier 系数或尖点标签。这个范围来自已证明的 3/16
谱隙，而不是 Selberg 的 zeta 零点正比例定理。

固定非负 b 属于 C_c^infty((1,2))，并归一化
integral b(u)du/u=1。固定一次以后不再随任何参数变化。令

\[
 \Phi_\delta(x)=b(x/\delta)-b(x/(2\delta)),\qquad 0<\delta\le1/16.
 \tag{compensated-test}
\]

它支撑在 (delta,4delta)，Mellin 零阶质量严格为0。本篇证明

\[
 |\widehat\Phi_\delta(r)|+|\check\Phi_\delta(r)|
          \le C_{b,A}(1+|r|)^{-A}\quad(r\in\mathbb R, A\ge0),
 \tag{uniform-real-decay}
\]

\[
 |\widetilde\Phi_\delta(l)|
       \le 2e^{4\delta^2}\frac{(2\delta)^l}{l!}\quad(l=1,2,\ldots),
 \tag{uniform-holomorphic-decay}
\]

\[
 \frac{\log2}{16}\delta^{-2\nu}
       \le\widehat\Phi_\delta(i\nu)
       \le C_b\delta^{-2\nu},\qquad
 |\check\Phi_\delta(i\nu)|\le C_b\delta^{-2\nu}.
 \tag{uniform-positive-exceptional}
\]

所有常数都与 delta、nu 及后续 q,N,X 无关。这里的快速衰减是
特定光滑差核族的结论，不声称任意只满足 C^2 范数限制的测试
函数也有任意阶衰减；也没有宣称一般大尺度、转折区估计已完成。

## 2. 原刊一致性问题的精确反例

DI 原刊 p.264，Lemma 7.1 (7.1)，在0<nu<1/2 上写出
两种异常变换 O((1+X^(-2nu))/(1+X))，并声明常数绝对。
其 p.234 (1.43)--(1.44) 假设是支撑 [X,8X]、sup 范数<=1、
一阶导 L1<=2、二阶导 L1<=6Y/X。以下反例满足这些字面假设，
且 Y 固定，不需要实际存在某个接近零的异常特征值。

令

\[
 p(u)=(u-1)^3(2-u)^3\quad(1\le u\le2),\qquad p(u)=0\text{ otherwise},
 \qquad f_X(x)=p(x/X).
\]

这个 p 为 C^2，非负，sup p=1/64，总变差1/32。写 z=u-1，
p''=6z-36z^2+60z^3-30z^4，所以 integral |p''|<=36。
因此可取 Y=6。令 B=integral_1^2 p(u)du/u>0。

取 L>=2，X=e^(-L)，nu=L^(-2)。由实际积分表示

\[
 K_a(x)=\int_0^\infty e^{-x\cosh t}\cosh(at)\,dt\ge K_0(x),
 \qquad K_0(x)\ge e^{-1}\log(1/x)\quad(0<x<1),
\]

第二式只需在0<=t<=log(1/x) 上用 cosh t<=e^t。于是

\[
 \check f_X(i\nu)
 \ge\sqrt2\,e^{-1}B(L-\log2),\qquad
 \frac{1+X^{-2\nu}}{1+X}\le1+e.
 \tag{exact-uniformity-counterexample}
\]

左侧无界、右侧有界。原刊 check 的定义与本篇相差固定因子
2/pi，不能消去这个反例。这只否定上述一致性陈述的字面形式，
不否定 DI 的全部定理，更不证明实际谱中有这样的 nu 序列。

同样，未作质量消去的正 bump 满足
hat f_X(0)=2B log(1/X)+O_p(1)。这是 -pi Y_0(x) 的零点展开，
所以 p.270 (8.2) 若解释为包含 r=0、且独立于 Y 的统一
O((1+|r|^2)^(-1))，也不能直接使用。后续证明不会使用它。

## 3. 保留归一化的余弦表示及修正上界

Mehler--Sonine 表示中相减的正确符号是

\[
 \frac{J_{2ir}(x)-J_{-2ir}(x)}{\sinh\pi r}
       =-\frac{4i}{\pi}\int_0^\infty
                     \cos(x\cosh t)\cos(2rt)\,dt.
\]

因此对实 r，以及 |Im r|<1/2 的延拓，

\[
 \widehat\phi(r)=2\int_0^\infty\cos(2rt)
                \left\{\int\cos(x\cosh t)\phi(x)\frac{dx}{x}\right\}dt,
 \tag{hat-cosine}
\]

\[
 \check\phi(r)=2\int_0^\infty\cos(2rt)
                \left\{\int\cos(x\sinh t)\phi(x)\frac{dx}{x}\right\}dt.
 \tag{check-cosine}
\]

第二式使用 cosh(pi r)K_(2ir)(x)=integral cos(x sinh t)cos(2rt)dt，
不是在非振荡的 K 表示中删去 cosh(pi r)。这些公式分别见
[DLMF 10.9.8](https://dlmf.nist.gov/10.9.E8) 与
[DLMF 10.32.7](https://dlmf.nist.gov/10.32.E7)。
本处只使用这些一维特殊函数积分，不引用任何未证的谱大筛。

换序先在0<=t<=T 上做。对固定 x>0，t 尾部用相位
x cosh t 或 x sinh t 分部积分，余项在任意紧 x 区间上一致
为 O((1+|r|) exp(-(1-2|Im r|)T))，常数可以依赖该紧区间及 r。
于是可以先做有限积分再令 T 趋无穷。对内层 x 积分分部积分后，
右侧又成为绝对收敛；这才是后续对 t 使用绝对值的对象。

作为对第2节的修正，若 f 仅满足那里原刊的 sup 及一阶变差
假设，则令 C_f(v)=integral cos(vx)f(x)dx/x，可得
|C_f(v)|<=C min(1,(X|v|)^(-1))。这是对 f(x)/x 分部积分，
其导数 L1<=3/X；v=0 使用支撑比8。

对0<X<=1，在 t=log(1/X) 附近分段，0<=a<=1/2 时

\[
 \int_0^\infty \cosh(at)\min(1,X^{-1}e^{-t})dt
 =\frac{\sinh(aL)}a+
   \frac12\left(\frac{e^{aL}}{1-a}+\frac{e^{-aL}}{1+a}\right),
 \quad L=\log(1/X),
 \tag{exact-envelope-integral}
\]

其中 sinh(aL)/a 在 a=0 取 L。cosh/sinh 参数与 e^t 之间的
固定倍数及 t<=1 的积分只改变绝对常数。因此两种异常变换均为
O((1+L)X^(-a))，不丢弃 L。
当 X>=1，hat 由 cosh t>=e^t/2 得 O(X^(-1))；check 则使用
K_a(x)<=C e^(-x)/sqrt(x)，该式由 cosh t>=1+t^2/2 和
cosh(at)<=e^(t/2) 完全平方得到，在0<=a<=1/2上一致。
合起来有可安全使用的修正版

\[
 |\widehat f(i\nu)|+|\check f(i\nu)|
 \ll\frac{(1+\log_+(1/X))(1+X^{-2\nu})}{1+X},\qquad 0\le\nu\le1/4.
 \tag{safe-general-exceptional-upper}
\]

本篇固定层数证明不靠把这个对数塞进 epsilon；它使用下面
具有严格零质量的差核，直接得到无对数的一致界。

## 4. 差核实谱衰减：逐尺度的可积导数证明

记

\[
 F(v)=\int_1^2 b(u)\cos(vu)\frac{du}{u},\qquad G(v)=F(v)-F(2v).
\]

F 是实偶 Schwartz 函数，F(0)=1；G 同为偶 Schwartz 函数，
G(0)=G'(0)=0。换元给两种变换恰为

\[
 \widehat\Phi_\delta(r)=2\int_0^\infty\cos(2rt)G(\delta\cosh t)dt,
 \quad
 \check\Phi_\delta(r)=2\int_0^\infty\cos(2rt)G(\delta\sinh t)dt.
 \tag{compensated-cosine}
\]

对任意整数 j>=0，两种 t 振幅的 j 阶导数都有与 delta 无关
的 L1 上界。证明如下，明确包含 t=0 的边界。

- 0<=t<=1：链式法则的各项包含 G 的导数与 delta sinh t、
  delta cosh t 的乘积。j=0 用 G(v)=O(v^2)，j=1 中用
  G'(v)=O(v)；j>=2 的其余项至少有两个 delta 因子。
  因而每一项为 O_(b,j)(delta^2)。
- t>=1：置 v=delta cosh t 或 delta sinh t，两者都满足
  dv/dt 介于 v 的两个固定正倍数之间。链式法则每项由
  v^h G^(h)(v) 乘有界的双曲函数比值构成。h=0 或1 的项
  在0为 O(v^2)，h>=2 的项至少为 O(v^2)；在无穷快速衰减。
  因而积分被 C_(b,j) integral min(v^2,v^(-2))dv/v 控制。

两种振幅延拓到整条实 t 轴都为光滑偶函数：第二种用到了
G 偶性。故半轴反复分部积分中出现的所有奇数阶导数在0为0；
无穷端的导数趋零。对 r>=1 积分分部积分任意偶数次，再结合
j=0 的 L1 界处理 |r|<=1，即得 (uniform-real-decay)。
这同时覆盖 r=0 和全尖点连续谱所需的正负 r。

对异常参数，以上换元另乘 cosh(at)<=C(v/delta)^a（t>=1）。
由于0<=a<=1/2，积分
integral |G(v)|v^(a-1)dv 在整个 a 区间一致有界；t<=1 仍为
O(delta^2)。因此得到 (uniform-positive-exceptional) 的两个
上界，没有引入1/nu。

对于正整数 l，J 的绝对值级数给
|J_l(x)|<=(x/2)^l exp(x^2/4)/l!。两项的 x 都<=4delta，
每项 b(u)du/u 的质量都是1，立即得到
(uniform-holomorphic-decay)。这里只需要 l=k-1>=1。

## 5. 异常谱正下界：不能仅靠变换的绝对值

令

\[
 k_a(x)=\frac{\pi}{2\sin(\pi a/2)}(J_{-a}(x)-J_a(x)),
 \quad 0<a\le1/2,\qquad k_0(x)=-\pi Y_0(x),\quad D=x\partial_x.
\]

先证明在0<x<=1/4、0<=a<=1/2上一致的

\[
                         -Dk_a(x)\ge\tfrac14 x^{-a}.
 \tag{positive-logarithmic-derivative}
\]

由 J 的微分递推式，对 a>0 有准确恒等式

\[
 -Dk_a(x)=\frac{\pi}{2\sin(\pi a/2)}
   \{a(J_{-a}(x)+J_a(x))+x(J_{1-a}(x)-J_{1+a}(x))\}.
 \tag{exact-kernel-derivative}
\]

以下用级数检查右侧的符号，不引用数值实验。
J_s(x)=(x/2)^s/Gamma(s+1) times (1+R_s(x))，其中
R_s=sum_(h>=1)(-x^2/4)^h/(h!(s+1)_h)。
对1/2<=s<=3/2，z=x^2/(4(s+1))<=1/96，逐项微分给

\[
 |R_s|\le e^z-1<1/90,\qquad
 |\partial_sR_s|\le\tfrac23 ze^z<1/100.
\]

又 psi(s+1)>=-gamma>-1，可由 digamma 的正项差级数直接得到。
于是
partial_s log J_s(x)=log(x/2)-psi(s+1)+partial_s R_s/(1+R_s)<0，
因为 log(x/2)<=-log8<-2。故 J_(1-a)>=J_(1+a)。

另一方面，s=-a 的交错级数项递减且第一修正项至多1/32，
所以 J_(-a)>=(31/32)(x/2)^(-a)/Gamma(1-a)。Gamma 的对数凸性
及 Gamma(1/2)=sqrt(pi)、Gamma(1)=1 给 Gamma(1-a)<=sqrt(pi)。
J_a 同样为正，而 pi a/(2sin(pi a/2))>=1。代入上式得
-Dk_a>=(31/(32sqrt(pi)))x^(-a)>x^(-a)/4。
在 a=0，由关于阶数的可去极限及其 x 导数连续性取极限；
没有除以最小正异常参数。

最后按 u 换元，

\[
 \widehat\Phi_\delta(i\nu)
   =\int_1^2b(u)\{k_a(\delta u)-k_a(2\delta u)\}\frac{du}{u}
   =\int_1^2b(u)\int_1^2[-Dk_a(\delta uv)]\frac{dv}{v}\frac{du}{u}.
\]

因 delta uv<=4delta<=1/4，且 (uv)^(-a)>=1/2，右边至少为
(log2/8)delta^(-a)，特别是所声明的 (log2/16)delta^(-a)。
这就证明了真正所需的正下界，不要求 Phi_delta 在几何侧非负。

## 6. 验收边界与来源

本篇的核心是第4--5节针对一个实际光滑函数族的证明，不是新添
一个等待输入的条件接口。后续可以使用任意复 Fourier 系数；
核本身保持实值，异常谱 hat 权重保持正值。

本地有限数值诊断只检查归一化、正号、零质量、参数边界和反例
增长。Python 回归守护原仓库；二者均不代替上述一致数学证明。

逐源核对：DI 1982 p.234 (1.43)--(1.44)、p.264 (7.1)及其
证明、p.270 (8.1)--(8.3)。
原刊扫描分别为 [statements](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0020.pdf)、
[section 7](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0026.pdf)、
[section 8](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0027.pdf)。
J 的级数定义及逐阶数计算与
[DLMF 10.2.2](https://dlmf.nist.gov/10.2.E2) 一致。

### English summary

The literal absolute-constant exceptional transform bound at DI (7.1)
fails uniformly as the spectral parameter tends to zero. A fixed C2 bump
with scale exp(-L) and parameter L^(-2) gives an exact counterexample.
For a different, smooth test family b(x/delta)-b(x/(2delta)), zero Mellin
mass removes this logarithm. Cosine representations give scale-uniform
rapid real-spectrum decay, while an order-monotonicity calculation for
Bessel J proves a positive exceptional lower bound c delta^(-2nu),
uniformly for 0<=nu<=1/4. These are local paper proofs, not the complete
varying-level exceptional sieve or the native Conrey theorem.
