# Conrey 的 DI 谱路线：真实 Bessel 权重及两个几何模数和

先说结论：本篇证明 DI82 大筛证明中实际出现的两类 Bessel 权重，
并将前篇的三条二次 Kloosterman 估计接成完整的几何模数和界。
全纯部分的误差一致于谱参数 K；Maass 部分保留线性 K 项和明确的
Gaussian 尾项。没有把这些真实权重替换成任意条件接口。

**本篇不证明 Petersson/Kuznetsov 谱公式、谱侧的正性与完整接合，
也不证明 exceptional-spectrum 加权估计。** 因而不是完整谱大筛、
DI11 或原生 Conrey 严格 `>2/5` 的完成声明。

冻结基点为 `042452fca8b9bde40dd2cd1717bab81a32744544`。
只新增本篇纸面证明，不改 Lean、Lake、契约或冻结源分支。
方法是经典 DI 路线的展开，不主张新的谱定理。

## 1. 实际对象、已有输入与结论

固定正整数 q,N，实数 K>=1，复系数 b_n 支撑在
`I_N={n in Z:N<n<=2N}`。q 是群的水平，不是指数权重。
记 `e(t)=exp(2 pi i t)`，Kl_c(m,n) 为前篇同一整数模数下的完全
Kloosterman 和，并设 `x_(m,n,c)=4 pi sqrt(mn)/c`。

定义两个实际几何二次和

\[
 H_K(c)=\sum_{m,n\in I_N}b_m\overline{b_n}
       \operatorname{Kl}_c(m,n)E_K(x_{m,n,c}),
 \tag{holomorphic-geometric}
\]

\[
 G_K(c)=\sum_{m,n\in I_N}b_m\overline{b_n}
       \operatorname{Kl}_c(m,n)x_{m,n,c}\Phi_K(x_{m,n,c}).
 \tag{Maass-geometric}
\]

其中 E_K 是第2节的真实 Bessel 级数，Phi_K 是第5节的真实
Gaussian/Macdonald 轮廓积分，不是任意满足某个界的函数。
本篇证明对任意 epsilon>0，统一于 q,N,K,b，

\[
 \boxed{\sum_{\substack{c\ge1\\q\mid c}}\frac{|H_K(c)|}{c}
       \ll_\epsilon\frac{N^{1+\epsilon}}q\|b\|_2^2,}
 \tag{holomorphic-moduli-bound}
\]

\[
 \boxed{\sum_{\substack{c\ge1\\q\mid c}}\frac{|G_K(c)|}{c}
       \ll_\epsilon
       \left\{\frac{K N^{1+\epsilon}}q
         +\frac{K e^{-K^2/4}N^2}{q^2}\right\}\|b\|_2^2.}
 \tag{Maass-moduli-bound}
\]

所用输入是已经证明的
[三条实际二次和估计](2026-08-31-conrey-kloosterman-quadratic-large-sieve.md)：
对 `B_c(theta;b)=sum b_m conjugate(b_n) Kl_c(m,n)e(2 theta sqrt(mn)/c)`，

\[
 \begin{aligned}
 |B_c(\theta;b)|&\le2\tau(c)^2\sqrt c\,N\|b\|_2^2,\\
 |B_c(\theta;b)|&\ll(c+N+\sqrt{\theta cN})\|b\|_2^2,\\
 |B_c(\theta;b)|&\ll_\epsilon
     \theta^{-1/2}c^{1/2}N^{1/2+\epsilon}\|b\|_2^2
       \quad(0<\theta<2,\ c\le N).
 \end{aligned}
 \tag{proved-quadratic-inputs}
\]

第一条对任意实 theta 成立，第二条先对 theta>0，并由有限和连续性
延至 theta=0。负相位也受同样的正参数界控制：单位换元 d->-d
表明 Kl_c(m,n) 为实数，而
`B_c(-theta;b)=conjugate(B_c(theta;conjugate(b)))`。
所以后面将 cos、sin 写成两个指数相位时，仍可用同一范数界。

前篇已通过 Fricke 精确共轭证明：当前 DI11 的 S=1 应用中，
两个所需尖点 infinity 与 1（等价于0）的对角和恰落在 q|c 的
经典模数上。这里没有把非对角尖点和偷换成对角和。

## 2. 全纯 Bessel 级数：从全部系数证明正确符号

令 `a=1/K, omega=exp(-a), B=cosh(a), s=sinh(a)`。
整数阶 J_n 按标准幂级数归一化：

\[
 J_n(x)=\sum_{h\ge0}\frac{(-1)^h(x/2)^{n+2h}}{h!(n+h)!}.
\]

原刊 p.258 在 (5.4) 下定义的权重为

\[
 E_K(x)=2\sum_{l\ge1}(2l-1)(-1)^l\omega^{2l-1}J_{2l-1}(x).
 \tag{E-series}
\]

以下证明的准确积分式带一个负号：

\[
 \boxed{E_K(x)=-sB\,x\int_0^1
          \frac{\xi J_0(\xi x)}{(B^2-\xi^2)^{3/2}}\,d\xi.}
 \tag{E-correct-integral}
\]

令右侧负号后的正表达式为 R_K(x)。不能只靠低阶数值把
E_K=-R_K 当成恒等式，下面比较全部 Taylor 系数。

### 2.1 积分矩的有限递推

设

\[
 D_j=sB\int_0^1\frac{\xi^{2j+1}}{(B^2-\xi^2)^{3/2}}\,d\xi.
\]

直接积分得 D_0=B-s=omega。对 j>=1，用
`d/dxi (B^2-xi^2)^(-1/2)=xi(B^2-xi^2)^(-3/2)` 分部积分，
在 xi=1 的端点为1/s，在 xi=0 的端点为0，得到

\[
 (2j-1)D_j=2jB^2D_{j-1}-B.
 \tag{moment-recurrence}
\]

具体地，若去掉 sB 后的积分为 I_j，则
`I_j=1/s-2j(B^2 I_(j-1)-I_j)`，即上式。

另一方面定义有限多项式

\[
 A_j(z)=\sum_{l=1}^{j+1}a_{j,l}z^{2l-1},\qquad
 a_{j,l}=\frac{(j!)^2(2l-1)}{(j-l+1)!(j+l)!}.
\]

它们满足 A_0(z)=z，以及

\[
 (2j-1)A_j(z)=
   2j\left(\frac{z+z^{-1}}2\right)^2A_{j-1}(z)
        -\frac{z+z^{-1}}2.
 \tag{polynomial-recurrence}
\]

为完整检查边界，令越界 a_(j-1,l)=0。对 2<=l<=j+1，逐系数式是

\[
 (2j-1)a_{j,l}=\frac j2
       (a_{j-1,l-1}+2a_{j-1,l}+a_{j-1,l+1}).
\]

由

\[
 a_{j,l}=\frac{(j!)^2}{(2j)!}
   \left[\binom{2j}{j-l+1}-\binom{2j}{j-l}\right]
\]

及两次 Pascal 恒等式即得；归一化因子的相邻比是
`j/[2(2j-1)]`。对 l=1，系数还需减去1/2：
`a_(j-1,1)=1/j`、`a_(j-1,2)=3(j-1)/(j(j+1))`（j=1时第二项为0），
故右端为 `(2j-1)/(j+1)=(2j-1)a_(j,1)`。
唯一可能的负幂 z^(-1) 系数则为 `j(1/j)/2-1/2=0`。
这证明了 (polynomial-recurrence)，没有漏掉边界系数。

代 z=omega 后 `(z+z^(-1))/2=B`。由同一递推和初值，D_j=A_j(omega)。

### 2.2 级数重排及整函数恒等式

R_K(x) 的 x^(2j+1) 系数为 `(-1)^j D_j/[4^j(j!)^2]`。
从 (E-series) 逐项展开 J_(2l-1)，其对应系数为

\[
 \frac{(-1)^{j+1}}{4^j}
 \sum_{l=1}^{j+1}
 \frac{(2l-1)\omega^{2l-1}}{(j-l+1)!(j+l)!}
 =-\frac{(-1)^jA_j(\omega)}{4^j(j!)^2}.
\]

所有重排均合法：对复 x 的任意紧集，
`|J_n(x)|<=(|x|/2)^n exp(|x|^2/4)/n!`，给出全部双重级数的
局部一致绝对主化。积分侧因 B>1，分母在[0,1]上远离0，
J_0 的幂级数也可一致积分。两边均为整函数，系数全同就证明了
(E-correct-integral)，不只是渐近相等。

附带的对角权重也是准确可求的：

\[
 \sum_{l\ge1}(2l-1)e^{-(2l-1)/K}
     =\frac12\frac{\cosh(1/K)}{\sinh^2(1/K)}
     =\frac12K^2+O(1).
 \tag{holomorphic-diagonal}
\]

第一式由几何级数求导；第二式在 0<a<=1 上展开 sinh、cosh，
减去1/(2a^2)后为在 a=0 可去奇点的连续函数，因此有统一常数。
它不包含任何谱分解假设。

## 3. 全纯核的统一权重质量与角度分部积分

记 `W_K(xi)=sB(B^2-xi^2)^(-3/2)`，则 W_K 非负，且

\[
 \int_0^1\xi W_K(\xi)\,d\xi=\omega\le1,\qquad
 \int_0^1\xi^{-1/2}W_K(\xi)\,d\xi\ll1
 \tag{uniform-holomorphic-mass}
\]

一致于 K>=1。第二式在 xi<=1/2 上由 s<=sinh(1)、B<=cosh(1)、
`B^2-xi^2>=3/4` 控制；在 xi>=1/2 上用
`xi^(-1/2)<=2 sqrt(2)xi` 和第一式。这样即使 K 趋于无穷、
权重向 xi=1 集中，也没有把 K 损失藏进常数。

J_0 的 Poisson 表示为

\[
 \frac\pi2J_0(y)=\int_0^{\pi/2}\cos(y\cos u)\,du.
\]

可直接从幂级数证明：偶次余弦矩为
`(pi/2)(2j)!/[4^j(j!)^2]`，由一次分部积分递推；逐项积分 cos
的级数就得到 J_0。对 0<Delta<=pi/2，正确的分部积分式是

\[
 \frac\pi2J_0(y)=
 \int_0^\Delta\cos(y\cos u)\,du
 -\frac1y\int_\Delta^{\pi/2}
       \frac{\cos u}{\sin^2u}\sin(y\cos u)\,du
 +\frac{\sin(y\cos\Delta)}{y\sin\Delta}.
 \tag{angular-IBP}
\]

这里 `d/du sin(y cos u)=-y sin u cos(y cos u)`；在 u=pi/2 的
端点为0，在 u=Delta 的端点保留了所写的正号。y=0 时用连续极限。

把 (angular-IBP) 代入 R_K=-E_K，写 R_K=R_1-R_2+R_3：

\[
 \begin{aligned}
 R_1(x)&=\frac{2x}\pi\int_0^1\xi W_K(\xi)
            \int_0^\Delta\cos(\xi x\cos u)\,du\,d\xi,\\
 R_2(x)&=\frac2\pi\int_0^1W_K(\xi)
            \int_\Delta^{\pi/2}\frac{\cos u}{\sin^2u}
                           \sin(\xi x\cos u)\,du\,d\xi,\\
 R_3(x)&=\frac{2}{\pi\sin\Delta}
            \int_0^1W_K(\xi)\sin(\xi x\cos\Delta)\,d\xi.
 \end{aligned}
 \tag{R-three-parts}
\]

sin/cos 所对应的二次和参数准确是 `theta=xi cos u`：
`exp(i xi x_(m,n,c) cos u)=e(2 xi cos u sqrt(mn)/c)`。
没有将 4 pi 再次放入 e(t) 的参数。

## 4. 全纯几何二次和及全部模数

若 c<=N，取 Delta=sqrt(c/N)<=1。R_1 中的 x 因子提出4 pi N/c，
并把系数改为 `b'_m=b_m sqrt(m/N)`，所以 `||b'||^2<=2||b||^2`。
其余两部分没有 x 前因子，不改系数。
用 (proved-quadratic-inputs) 的振荡界以及统一质量，得到

\[
 \begin{aligned}
 |H_{K,1}(c)|&\ll_\epsilon
       \frac{\Delta N}{c}\sqrt c N^{1/2+\epsilon}\|b\|_2^2,\\
 |H_{K,2}(c)|+|H_{K,3}(c)|&\ll_\epsilon
       \Delta^{-1}\sqrt c N^{1/2+\epsilon}\|b\|_2^2.
 \end{aligned}
\]

角度积分的检验分别是
`integral_0^Delta (cos u)^(-1/2)du << Delta`、
`integral_Delta^(pi/2) sqrt(cos u)/sin^2 u du <=cot Delta <<Delta^(-1)`，
以及 `1/(sin Delta sqrt(cos Delta)) <<Delta^(-1)`。
Delta<=1 保证最后的 cos 远离0；xi=0 或 cos u=0 的零测端点
用已写出的可积主化处理。因此

\[
 |H_K(c)|\ll_\epsilon N^{1+\epsilon}\|b\|_2^2\quad(c\le N).
\]

若 c>N，取 Delta=pi/2，只有 R_1。对 N<c<=N^2 用混合界，
因 0<=theta<=1，二次和为 O(c||b'||^2)，所以 H_K(c)<<N||b||^2。
对 c>N^2 用保留 tau(c)^2 的 Weil 界。因此统一得到

\[
 |H_K(c)|\ll_\epsilon\|b\|_2^2
 \begin{cases}
 N^{1+\epsilon},&c\le N,\\
 N,&N<c\le N^2,\\
 \tau(c)^2c^{-1/2}N^2,&c>N^2.
 \end{cases}
 \tag{holomorphic-three-ranges}
\]

现在对 q|c 求和。前两段使用
`sum_(q|c,c<=N^2)1/c <=q^(-1)H_floor(N^2/q)`，吸收一个 log。
尾段选 0<delta<1/2，并用 `tau(c)^2 <<_delta c^delta`。若 q<=N^2，
对 c=qj、j>N^2/q 用积分比较，尾段至多

\[
 C_\delta N^2 q^{-3/2+\delta}
       (N^2/q)^{-1/2+\delta}
 =C_\delta q^{-1}N^{1+2\delta}.
\]

若 q>N^2，从 j=1 开始求和，得到 `C_delta N^2 q^(-3/2+delta)`，
也不超过 `C_delta q^(-1)N^(1+2delta)`。
把各处 epsilon、delta 先取目标 epsilon 的充分小倍数，即证明
(holomorphic-moduli-bound)，包含 q>N^2 时为空的前两段。

## 5. Maass 核：带虚轴端点的真实轮廓积分

为区别整数模数的 Kl，Macdonald 函数记作 mathsf K。
对实 t、Re z>0，采用标准归一化

\[
 \mathsf K_{2it}(z)=\int_0^\infty e^{-z\cosh u}\cos(2tu)\,du.
 \tag{Macdonald-integral}
\]

这一归一化可直接识别：两次对 z 求导并对 u 分部积分，得到
`z^2 f''+z f'-(z^2-4t^2)f=0`；在正实轴上令 u=v/sqrt(z)，
由 cosh(u)>=1+u^2/2 主化得
`f(z)~sqrt(pi/(2z))e^(-z)`。这确定标准的衰减解；复右半平面
由解析延拓一致。下面也直接用其积分表示完成证明。

设 gamma 为从 -i 到 i、经过1的右单位半圆，方向向上。
对 x>0，实际 Gaussian 权重定义为

\[
 \Phi_K(x)=\int_{\mathbb R}t^2e^{-(t/K)^2}
          \int_\gamma\mathsf K_{2it}(xv)\,\frac{dv}{v}\,dt.
 \tag{Phi-contour}
\]

虚轴端点取从右半平面到达的值。不能在 Re(xv)=0 时直接用
(Macdonald-integral) 做未经主化的 Fubini，以下通过右移轮廓证明。

### 5.1 端点控制与合法 Abel 极限

对 `z=r exp(i phi)`、r 在任意固定正紧区间、`|phi|<pi/2`，
把 (Macdonald-integral) 的 u 半射线平移到 `u=w-i phi`。
被积函数关于 u 整；大矩形的远边因指数衰减而消失。新半射线上

\[
 \operatorname{Re}\{z\cosh(w-i\phi)\}
 =\frac r2(e^w+e^{-w}\cos2\phi)\ge r\sinh w.
\]

而 `|cos(2t(w-i phi))|<=exp(2|t phi|)`。
从0到 -i phi 的短连接段也被 `C exp(pi|t|)` 主化。
所以该变形延伸到 phi=±pi/2，并给出

\[
 |\mathsf K_{2it}(z)|\le C\,e^{\pi|t|}
 \quad(\operatorname{Re}z\ge0,\ r_0\le|z|\le r_1),
 \tag{Macdonald-boundary-bound}
\]

常数只依赖正紧区间。新半射线的积分由 `exp(-r_0 sinh w)`
控制，连接段有限长，因此端点极限的连续性也已得到。

将 gamma 右移 epsilon>0 得 gamma_epsilon。对 0<epsilon<1/2，
其上 |v| 在[1,3/2]内，故 (Macdonald-boundary-bound) 与
`t^2 exp(-(t/K)^2+pi|t|)` 一起提供可积主化。
于是 (Phi-contour) 等于 epsilon 降到0时的右移轮廓积分极限，
而且该极限可穿过 t 积分。这一步只需固定 K,x，不把此主化常数
用作后面的统一 K 估计。

### 5.2 先在右半平面计算，再取端点极限

对 Re z>0、t!=0，在 u 上分部积分得到

\[
 \mathsf K_{2it}(z)=\frac z{2t}
       \int_0^\infty e^{-z\cosh u}\sinh u\sin(2tu)\,du.
\]

u=0 的 sin 项为0，u 趋于无穷时双指数衰减，边界项均消失。
乘以 t^2 后在 t=0 的表达式可连续延拓，也不影响积分。
在 gamma_epsilon 上 Re(xv)>=x epsilon，所有 t,u,v 的交换
先由 Gaussian 和 `sinh(u)exp(-x epsilon cosh u)` 的绝对可积性保证。

Gaussian Fourier 积分求导给出精确式

\[
 \int_{\mathbb R}t e^{-(t/K)^2}\sin(2tu)\,dt
       =\sqrt\pi K^3u e^{-K^2u^2}.
\]

轮廓积分则只取端点：

\[
 \int_{\gamma_\epsilon}e^{-xv\cosh u}\,dv
     =\frac{2i}{x\cosh u}e^{-\epsilon x\cosh u}\sin(x\cosh u).
\]

因此取 epsilon 降到0，并用 `u tanh(u)exp(-K^2u^2)` 主化，得到

\[
 \boxed{\Phi_K(x)=i\sqrt\pi K^3\int_0^\infty
       e^{-K^2u^2}u\tanh u\sin(x\cosh u)\,du.}
 \tag{Phi-sine}
\]

所有 x、i、sqrt(pi)、K^3 因子都由上面的计算保留。
再利用 `d/du cos(x cosh u)=-x sinh u sin(x cosh u)` 分部积分，得

\[
 \boxed{x\Phi_K(x)=i\sqrt\pi K^3\int_0^\infty
      \frac{e^{-K^2u^2}}{\cosh u}
        (1-u\tanh u-2K^2u^2)\cos(x\cosh u)\,du.}
 \tag{Phi-cosine}
\]

因为 `u exp(-K^2u^2)/cosh u` 在0及无穷处都为0，未漏端点项。
这证明原刊 (5.6)--(5.7) 在所写轮廓约定下的真实恒等式。
两式还直接给出统一的 `|Phi_K(x)|<<1` 和 `|x Phi_K(x)|<<K^2`：
前者用 tanh u<=u，后者对 Gaussian 的0、1、2次矩缩放。

## 6. Maass 几何和的四段估计及明确高参数尾项

(Phi-sine) 中的二次和参数准确为 theta=cosh u。
当 0<=u<=1 时 `1<=theta<=cosh(1)<2`，可使用已证明的振荡界；
当 u>1 时改用混合界，不外推 theta<2 的结论。

先设 c<=N。用 (Phi-sine) 时，x 前因子仍提出4 pi N/c，
将系数改为 b'_m=b_m sqrt(m/N)。低 u 部分给出

\[
 |G_{K,\mathrm{low}}(c)|
    \ll_\epsilon c^{-1/2}N^{3/2+\epsilon}\|b\|_2^2,
 \tag{sine-low}
\]

因为 `K^3 integral_0^1 u tanh(u)exp(-K^2u^2)du<<1`。
若改用 (Phi-cosine)，不再有 N/c 因子，也不改系数；Gaussian 矩给

\[
 |G_{K,\mathrm{low}}(c)|
    \ll_\epsilon K^2c^{1/2}N^{1/2+\epsilon}\|b\|_2^2.
 \tag{cosine-low}
\]

因此在 c<=N/K^2 时用 (cosine-low)，在 N/K^2<c<=N 时用
(sine-low)。这个分界即使小于1，也只是令第一段为空，不要求存在模数。

### 6.1 u>1 的部分不能丢掉

当 c<=N，混合界在 theta=cosh u 处为
`O(N(1+sqrt(cosh u))||b||^2)`。
对 (Phi-sine)，利用 tanh u<=1 及

\[
 \int_1^\infty u e^{-K^2u^2}(1+\sqrt{\cosh u})\,du
       \ll K^{-2}e^{-K^2/2},
\]

得到高 u 贡献 `O(K exp(-K^2/2)N^2/c)||b||^2`。
上述积分界可直接验证：分出一个 `exp(-K^2/2)`，再用
`sqrt(cosh u)<=exp(u/2)` 和
`u/2<=K^2u^2/4+1/(4K^2)`，剩下是 Gaussian 一次矩。

对 (Phi-cosine)，用
`(1+sqrt(cosh u))/cosh u<=2`，并在 u>1 上分出
`exp(-K^2/2)`，得到高 u 贡献

\[
 \ll K^3N e^{-K^2/2}
   \int_0^\infty e^{-K^2u^2/2}(1+u+2K^2u^2)du\,\|b\|_2^2
 \ll K^2N e^{-K^2/2}\|b\|_2^2.
\]

因为 c<=N、且 `K exp(-K^2/4)` 在 K>=1 上有统一界，
两种表示的高 u 项都可用同一个误差主化：

\[
 O\!\left(K e^{-K^2/4}\frac{N^2}{c}\right)\|b\|_2^2.
 \tag{explicit-high-u-error}
\]

这里的指数常数1/4来自已经写出的主化，不把原刊更紧的
exp(-K^2) 当作本篇已经证明的值。

### 6.2 c>N 的两段

对 N<c<=N^2，始终使用 (Phi-sine) 和混合界。
Gaussian 矩仍一致，因为

\[
 K^3\int_0^\infty u\tanh u\,e^{-K^2u^2}
             (1+\sqrt{\cosh u})du\ll1.
\]

用 tanh u<=u、`sqrt(cosh u)<=exp(u/2)`，完成平方后缩放
即可证明这个界。故 G_K(c)<<N||b||^2。
对 c>N^2，使用不依赖 theta 的 Weil 二次和界，得到
`G_K(c)<<tau(c)^2c^(-1/2)N^2||b||^2`。

合起来，G_K(c)/||b||^2 的低参数主界为

\[
 \ll_\epsilon
 \begin{cases}
 K^2c^{1/2}N^{1/2+\epsilon},&c\le N/K^2,\\
 c^{-1/2}N^{3/2+\epsilon},&N/K^2<c\le N,\\
 N,&N<c\le N^2,\\
 \tau(c)^2c^{-1/2}N^2,&c>N^2,
 \end{cases}
 \tag{Maass-four-ranges}
\]

且前两段都须再加上 (explicit-high-u-error)。
这里“低参数主界”只是误差预算的命名，不是一个未证明的渐近主项。

## 7. 全部 Maass 模数求和

令 X=N/K^2>0。对第一段，若有模数可求和，则

\[
 K^2N^{1/2+\epsilon}
       \sum_{q\mid c,\ c\le X}c^{-1/2}
 \ll\frac{K^2N^{1/2+\epsilon}\sqrt X}{q}
 =\frac{K N^{1+\epsilon}}q.
\]

若 X<q，第一段为空。第二段用对任意 X>0 都成立的

\[
 \sum_{q\mid c,\ c>X}c^{-3/2}
     \ll q^{-1}\max(X,q)^{-1/2}\le q^{-1}X^{-1/2}.
\]

这在 X>=q 时是积分比较，X<q 时是从 c=q 开始的收敛级数。
乘 N^(3/2+epsilon)，同样得到 `O(q^(-1)K N^(1+epsilon))`。
第三、四段已由第4节的谐和求和及约数尾项控制，结果至多
`O_epsilon(q^(-1)N^(1+epsilon))`，而 K>=1。

最后，不能只把高 u 项称作“可忽略”：其全部模数和精确被

\[
 C K e^{-K^2/4}N^2\sum_{q\mid c}c^{-2}
 =C\zeta(2)\,\frac{K e^{-K^2/4}N^2}{q^2}
\]

控制。吸收各处 epsilon 的小倍数后，证明 (Maass-moduli-bound)。
以上同时证明了两个模数级数的绝对收敛，且覆盖 q>N、K^2>N
以及相应空区间的边界情形。

最低的 n=1 单点也可独立处理，不要求把它放进 I_1=(1,2]。
此时 m=n=1；由积分质量有 `|E_K(4 pi/c)|<=4 pi/c`，由
第5节有 `|Phi_K(4 pi/c)|<<1`。任意模数 Weil 界因 gcd(1,1,c)=1
给出 H_K、G_K 各自的 `O(tau(c)c^(-1/2)|b_1|^2)` 上界。
所以两份模数和均为 `O(q^(-1)|b_1|^2)`：

\[
 \sum_{q\mid c}\frac{\tau(c)}{c^{3/2}}
 \le\frac{\tau(q)}{q^{3/2}}
       \sum_{j\ge1}\frac{\tau(j)}{j^{3/2}}
 \le\frac2q\zeta(3/2)^2.
\]

这里用到了逐素数可证的 tau(qj)<=tau(q)tau(j)、约数配对给出的
tau(q)<=2sqrt(q)，以及非负双重级数的 Tonelli。因 K>=1，
这也在所需 Maass 预算内，最低 dyadic 单点没有被漏掉。

## 8. 原刊符号差异的逐式证据与剩余谱边界

本篇按 PDF 原刊逐页核对 DI82 §5.2--5.3，pp.258--261：
[原刊第5节](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0024.pdf)。
印刷文本中有两处符号不一致，本篇使用实际推导的式子，而不是
无说明地改写原文：

1. p.258 的 (E-series) 一阶项为 `-exp(-1/K)x`，但该页随后印出的
   正号积分式一阶项为 `+exp(-1/K)x`。第2节证明全部系数匹配的
   正确关系是 E_K=-R_K；不是仅凭数值猜测一个负号。
2. 同页底部的角度分部积分把 (angular-IBP) 的最后两项印成了
   相反符号。令 y 趋于0，印刷右端变成 `2Delta-pi/2`，而左端为
   pi/2；例如 Delta=pi/6，两边为 -pi/6 和 pi/2。第3节从导数及
   两个端点证明了正确式。下一页写出的“第一项减第二项加第三项”
   与正确角度式相符，但仍需连同第一个整体负号一起区分 E 与 R。

这些符号差异不反驳原刊的绝对值估计：本篇对三部分取模求和，
整体符号不改变该界。它们也不影响前篇已证明的三条二次和。
Maass 的 (5.6)--(5.7) 则在第5节所写的向上轮廓和归一化下得到原符号。

本篇的真正交付是 (holomorphic-moduli-bound) 与
(Maass-moduli-bound) 的证明，而不只是印刷差异清单。
它们正是谱大筛几何侧的两份实际加权 Kloosterman 和。
要从这里完成谱 Theorem 2，仍需独立建立 Petersson/预 Kuznetsov
公式、相应谱侧正性、合法谱展开和截断接合；DI11 的 exceptional
加权谱估计仍另列。不能将这些未完成步骤解释为已由本文证明。

English summary: prove the exact holomorphic and Gaussian/Macdonald
weights and their uniform geometric modulus-sum bounds, including the
imaginary-endpoint limit and an explicit high-parameter error. The spectral
trace formulas and exceptional-spectrum estimates remain unproved here.

独立审查应检查全部系数递推边界、角度分部积分符号、统一权重质量、
负相位与系数缩放、Macdonald 虚轴主化、轮廓方向、Gaussian 因子、
两种表示的低/高参数分工，以及 q,K 使区间为空时的模数求和。
最终 SHA 只运行允许的 Python/目标分类/chain-gap/diff 验证；
有限或浮点诊断不是一般数学证明。未获专属资源通知前不启动 Lean/Lake，
源验证不替代最终 main 集成验证或原生数学验收。
