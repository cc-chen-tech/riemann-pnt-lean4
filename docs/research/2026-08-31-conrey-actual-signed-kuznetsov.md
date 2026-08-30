# Conrey 的 DI 谱路线：同号、异号及实际跨尖点 Kuznetsov

先说结论：本篇把完整 L2 谱分解和实际 Bessel 反演接到一起，
证明当前 DI11 的 S=1 应用所需的同号、异号及 infinity 到0/1
跨尖点测试核公式。全纯、Maass（含异常参数）和全尖点连续谱
都保留；几何模数和与每一种谱的换序分别给出绝对主化。

冻结基点 6c5b8d4dea1eb2f7bfcf4dd0d1c670884aac8308。
反演输入是本次配套的
[实际 Bessel 测试核反演](2026-08-31-conrey-bessel-test-kernel-inversion.md)，
不是引用未证的 Kuznetsov 公式。只新增纸面证明，无 Lean、Lake
或契约变更。一般 S、X 放大异常谱和 DI11 的完整参数预算仍在
后续；本篇不宣布原生 Conrey 严格 >2/5 完成。

## 1. 对象及必须冻结的归一化

令 Gamma=Gamma_0(q)，q>=1，dmu=dxdy/y^2，内积第一变量线性。
当前尖点缩放取

\[
 \sigma_\infty=I,\qquad
 \sigma_0=W_q=\begin{pmatrix}0&-q^{-1/2}\\q^{1/2}&0\end{pmatrix},
 \qquad \sigma_1=T_1W_q.
 \tag{actual-cusp-scalings}
\]

0与1为同一尖点类，不是两个不同的连续谱通道。q=1 时 infinity
与0也等价。delta_ab 表示所选两个标签等价；在上述缩放中，
对应对角相位是1。连续谱索引 c 则遍历 Gamma 的全部不等价尖点。

实际正交归一 Maass 基写成
u_j(sigma_a z)=sqrt(y)sum_(n!=0)rho_ja(n)K_(ir_j)(2pi|n|y)e(nx)。
可取实值基，或在公式中保留负频指标；r_j 为非负实数或
r_j=i nu_j，0<nu_j<=1/4。实际 Eisenstein 系数继续采用

\[
 \rho^E_{ca}(n,1/2+ir)
      =\frac{2\pi^{1/2+ir}|n|^{ir}}{\Gamma(1/2+ir)}
                                      \varphi_{can}(1/2+ir).
\]

这是已有实际级数的系数，没有因最终公式而重新缩放基或测度。
定义谱乘积

\[
 M^\epsilon_{ab,j}(m,n)=\overline{\rho_{ja}(m)}\rho_{jb}(\epsilon n),
 \qquad \epsilon\in\{+1,-1\},
\]

\[
 C^\epsilon_{ab}(m,n;r)=\sum_{c\in A}
       \left(\frac nm\right)^{ir}
       \overline{\varphi_{cam}(1/2+ir)}
                 \varphi_{cb,\epsilon n}(1/2+ir).
 \tag{actual-signed-spectral-products}
\]

全纯基 B_k(q) 按不除面积的 Petersson 内积正交归一，
(f|_k sigma_a)(z)=sum_(n>=1)a_fa(n)e(nz)。

对 phi in C_c^infty(0,infinity)，定义

\[
 \widetilde\phi(l)=\int_0^\infty J_l(x)\phi(x)\frac{dx}{x},\qquad
 \widehat\phi(r)=\frac{\pi i}{2\sinh(\pi r)}
                \int_0^\infty(J_{2ir}(x)-J_{-2ir}(x))\phi(x)\frac{dx}{x},
\]

\[
 \check\phi(r)=2\cosh(\pi r)
                         \int_0^\infty K_{2ir}(x)\phi(x)\frac{dx}{x}.
 \tag{actual-test-transforms}
\]

hat 在0按可去极限；两种谱变换在 |Im r|<1/2 全纯，故包含
所有已证明允许的异常参数。不能在 r=i nu 时擅自换成实 r。

## 2. 实际跨尖点 Kloosterman 和

对 sigma_a^(-1)Gamma sigma_b 的左右平移双陪集，选正下行
gamma>0。若代表为 ((alpha,beta),(gamma,delta))，定义
S_ab(m,n;gamma)=sum e((m alpha+n delta)/gamma)。
左右平移正好将 alpha、delta 各改变 gamma 的整数倍，故相位
定义良好。c=0 的双陪集只贡献第1节的 delta_ab 对角项。

同尖点 a=b=infinity 或0时，Fricke 共轭给
gamma=c、q|c，S_aa(m,n;c)=Kl_c(m,n)，已在前篇逐矩阵证明。
现在将真正跨尖点另行计算，不能用同尖点结论替换。

\[
 \begin{pmatrix}a&b\\qc&d\end{pmatrix}W_q
       =\begin{pmatrix}b\sqrt q&-a/\sqrt q\\d\sqrt q&-c\sqrt q\end{pmatrix}.
\]

因此正下行是 gamma=d sqrt(q)，d>=1且(d,q)=1。
行列式条件 ad-qbc=1 给 q b(-c)=1 mod d。令 v=-c mod d，
则 v 为单位、b=bar(q)bar(v) mod d，且每个单位 v 都能提升：
先选 b 满足该同余，再取 a=(1+qbc)/d。左右平移与余数类
的对应是完整且不重复的。于是

\[
 \boxed{S_{\infty0}(m,\epsilon n;d\sqrt q)
                  =\operatorname{Kl}_d(m\bar q,\epsilon n),\qquad(d,q)=1.}
 \tag{actual-cross-cusp-Kloosterman}
\]

q=1 时同一计算仍成立；此外存在下行0的双陪集，它恰是对角
项而不是这条正下行和中的一个项。反向尖点由取逆并变号使
下行仍为正得到，或直接重复上述计算。

对于固定 q,m,n，所有这些几何和满足
|S_ab(m,epsilon n;gamma)| <= C_(q,m)tau(d)sqrt(d)，其中 gamma
是 d 或 d sqrt(q)。因此 sum_gamma |S|gamma^(-2)(1+|log gamma|)
收敛。此处固定参数的收敛常数仅用于证明等式；后续 DI 的
统一尺度估计不能从它直接读出。

DI 原刊 S=1 使用的另一缩放可写为

\[
 \sigma_1^{DI}=T_1W_qT_{1/q}
       =\begin{pmatrix}\sqrt q&0\\\sqrt q&1/\sqrt q\end{pmatrix}.
\]

右乘 T_u 使 rho_b(n) 与 a_fb(n) 乘 e(nu)，使对应几何相位
乘 e(nu)。因此原刊外面的 e(-n/q) 正好抵消正号跨尖点的该
平移相位；异号按 epsilon n 同时改变。这里保留实际 sqrt(q)
模数和相位，不把 q 或尖点宽度吸进未指明的常数。

## 3. 实际有符号 Poincare 配对

定义 U_(a,epsilon m)(z;s) 为宽度1 Poincare 级数，种子
y^s e(epsilon m x)exp(-2pi m y)，m>=1。
负号的对象为 conjugate(U_(a,m)(z;conjugate(s)))。
infinity 的 L2 全纯延拓 Re s>3/4 已证明；0、1的由 Fricke
酉作用和平移得到，负号由共轭得到。

与任意实际谱特征函数的配对是前篇同一个 Gamma 积分，只需
把 Fourier 指标改成 epsilon m：

\[
 \langle U_{a,\epsilon m}(s),u_j\rangle
  =\overline{\rho_{ja}(\epsilon m)}
    \frac{\sqrt\pi\Gamma(s-1/2+ir_j)\Gamma(s-1/2-ir_j)}
         {(4\pi m)^{s-1/2}\Gamma(s)}.
 \tag{signed-actual-pairing}
\]

Eisenstein 配对亦保留实际 rho^E 与 phi 的转换。
与常数的配对为0：先绝对 unfolding，水平非零频积分为0，
再用 L2 全纯性延拓。因此完整 Parseval 没有遗漏常数残余项。

令 st=sinh(pi t)/t（t=0 时 st=pi），
D(t,r)=cosh(pi(t-r))cosh(pi(t+r))，H(r,t)=cosh(pi r)/D(t,r)。
实际 Gamma 积分与完整 Parseval 给

\[
 \begin{split}
 \langle U_{a,m}(1+it),U_{b,\epsilon n}(1+it)\rangle
   =\frac{st}{4\sqrt{mn}}\left(\frac nm\right)^{it}
       \left\{\pi\sum_j\frac{M^\epsilon_{ab,j}(m,n)}{D(t,r_j)}
                  +\int_{\mathbb R}C^\epsilon_{ab}(m,n;r)H(r,t)dr\right\}.
 \end{split}
 \tag{actual-signed-spectral-Gram}
\]

这里的谱前因子对正负号完全相同。s=1,r=0 的标量配对等于
pi/(2sqrt(m))，平方为 pi^2/(4m)，可单独核对其中的 pi。
这个标量检验不假设存在特征值1/4。

### 3.1 同号几何 Gram 与跨尖点

对 Re s_1,Re s_2>1，实际双陪集展开和 Fubini 绝对合法。
与前篇同尖点相同的二维积分，只将模数 c 换为 gamma，并把
有限相位和换为 S_ab。由于2节给出相同幂次的 Weil 主化，
该计算与其 L2 延拓完全适用于当前跨尖点，不需要新谱假设。
取 s_1=1+it、s_2=1-it，得到

\[
 G^+_{ab}=\frac{\delta_{ab}\delta_{mn}}{4\pi n}
   -2i\left(\frac nm\right)^{it}\sum_\gamma\frac{S_{ab}(m,n;\gamma)}{\gamma^2}
              \int_{\gamma_\uparrow}K_{2it}(x_\gamma v)\frac{dv}{v},
 \qquad x_\gamma=\frac{4\pi\sqrt{mn}}\gamma.
\]

gamma_up 是从 -i 到 i 的右半单位圆，与几何模数 gamma 是不同
符号。核取 D_(2it)=-(2it/sinh(pi t))乘该积分，与冻结前篇一致。
和谱 Gram 相等并乘4sqrt(mn)(m/n)^(it)/st，得

\[
 \sum_\gamma\frac{4\sqrt{mn}}{\gamma^2}S_{ab}(m,n;\gamma)D_{2it}(x_\gamma)
    +\frac{\delta_{ab}\delta_{mn}}{\pi st}
 =\pi\sum_j\frac{M^+_{ab,j}}{\cosh(\pi r_j)}H(r_j,t)
                   +\int_{\mathbb R}C^+_{ab}(r)H(r,t)dr.
 \tag{actual-positive-pre-Kuznetsov}
\]

### 3.2 异号二维积分的因子2

必须重新算异号几何积分，不能照搬原刊的系数。其非对角积分为

\[
 \int_0^\infty\int_{\mathbb R}
  y^{s_1+s_2-2}(x^2+y^2)^{-s_1}
    e\left(n(x+iy)-\frac{m}{\gamma^2(x+iy)}\right)dxdy.
\]

令 x=y xi、v=s_2-s_1。内层 y 积分由实际 K 积分表示为

\[
 2\left(\frac{m}{\gamma^2n}\right)^{v/2}
          (1-i\xi)^{-v}K_v(x_\gamma).
\]

这里的2来自 integral_0^infty y^(v-1)exp(-Ay-B/y)dy，
其值为2(B/A)^(v/2)K_v(2sqrt(AB))。A、B 实部为正，复幂取
连续于 xi=0 的分支。剩余 xi 积分为

\[
 \int_{\mathbb R}(1+i\xi)^{-s_1}(1-i\xi)^{-s_2}d\xi
     =\pi 2^{2-s_1-s_2}
               \frac{\Gamma(s_1+s_2-1)}{\Gamma(s_1)\Gamma(s_2)}.
\]

此 Beta 积分可先用两份正半轴 Gamma 积分与 Fourier 配对得到，
也可令 xi=tan(theta) 作 Beta 积分。故完整几何积分系数是
pi 2^(3-s_1-s_2)，不是 pi 2^(2-s_1-s_2)。在 s_1=s_2=1
时尤其清楚：内层为2K_0，剩余 integral(1+xi^2)^(-1)dxi=pi。

因此在目标参数处，实际异号 Gram 为

\[
 G^-_{ab}=2st\left(\frac nm\right)^{it}
                     \sum_\gamma\frac{S_{ab}(m,-n;\gamma)}{\gamma^2}
                                      K_{2it}(x_\gamma).
\]

它没有对角项，因为种子的水平频率相反且 m,n>0。
在初始区间完成计算，随后用实际 U 的 L2 延拓及几何和的局部
一致收敛到达上述参数；K 的小参数界给可求和的 log(gamma)
主化。与同一个谱 Gram 比较，得到

\[
 \sum_\gamma\frac{8\sqrt{mn}}{\gamma^2}S_{ab}(m,-n;\gamma)K_{2it}(x_\gamma)
 =\pi\sum_j\frac{M^-_{ab,j}}{\cosh(\pi r_j)}H(r_j,t)
                    +\int_{\mathbb R}C^-_{ab}(r)H(r,t)dr.
 \tag{actual-negative-pre-Kuznetsov}
\]

## 4. 无穷谱与参数积分的绝对换序

### 4.1 实际谱累计界

已有两尖点大筛，取单个 m 或 n 系数，并用 Cauchy--Schwarz，给

\[
 \sum_{0\le r_j\le R}\frac{|M^\epsilon_{ab,j}(m,n)|}{\cosh(\pi r_j)}
       \ll_{q,m,n}1+R^2,
 \qquad
 \int_{-R}^R\sum_{c\in A}
       |\overline{\varphi_{cam}(1/2+ir)}\varphi_{cb,\epsilon n}(1/2+ir)|dr
       \ll_{q,m,n}1+R^2.
 \tag{actual-spectral-mass-bounds}
\]

负频 Maaß 可使用实值基 rho(-n)=conjugate(rho(n))。
连续谱则用 phi_(c,b,-n)(s)=conjugate(phi_(c,b,n)(conjugate(s)))
并把 r 变为 -r。故负频不需要一个另行假设的大筛。
异常特征参数有界且总重数有限，已由实际尖点空间紧性证明。

### 4.2 正号三种换序

乘正号预公式以配套篇的 f(t) 并积分。几何项的绝对总量受控于
sum_gamma |S|gamma^(-2)(1+|log x_gamma|)，由2节收敛。
谱侧不能仅援引 hat 的快速衰减，因为那可能来自相消；实际使用
配套篇的 integral |H(r,t)f(t)|dt <<_(phi,N)(1+r)^(-N)。
它与累计界按 dyadic r 分组相乘，N>3即绝对可和、可积。
有限异常谱使用紧参数可积主化。因此几何、离散及全部连续
通道各自满足 Fubini/Tonelli 条件。

### 4.3 异号三种换序

令 g(t)=integral K_(2it)(y)phi(y)dy/y^2，乘异号预公式以
(4/pi^2)t sinh(2pi t)g(t)。几何项用配套篇的绝对 K 测试界，
仍只有同一个可求和的 log(gamma) 主化。
谱侧使用 integral |H(r,t)t sinh(2pi t)g(t)|dt 的快速衰减，
再接同一真实累计界。并不依赖一个只在离散谱有效的估计来
处理连续通道，也不将异常谱删掉。

## 5. 同号完整公式及全纯补项

由配套篇 D 的 J 尾表示和积分反演，
integral D_(2it)(x)f(t)dt=2pi phi_H(x)/x。
因此正号预公式的几何前系数变成2/gamma。
另外两条标量卷积给对角 integral J_0 phi 和
integral Hf=(2/pi)hat phi。整体除以2，得到

\[
 \sum_\gamma\frac{S_{ab}(m,n;\gamma)}\gamma\phi_H(x_\gamma)
   +\frac{\delta_{ab}\delta_{mn}}{2\pi}\int_0^\infty J_0(x)\phi(x)dx
 =\sum_j\frac{M^+_{ab,j}}{\cosh(\pi r_j)}\widehat\phi(r_j)
                 +\frac1\pi\int_{\mathbb R}C^+_{ab}(r)\widehat\phi(r)dr.
 \tag{actual-nonholomorphic-positive-test}
\]

全纯 Petersson 在当前跨尖点亦成立：对已构造的实际 P_(a,m,k)
在 b 取 Fourier 系数，双陪集的每个二维项与同尖点计算相同。
k=2 使用已有 Hecke 延拓的 L2 极限；Fricke 把 a=0 的源级数
移到 infinity，而 b 尖点的 Fourier 和由2节的 Weil 主化控制。
所以包括最低权重的实际恒等式是

\[
 \frac{\Gamma(k-1)}{(4\pi\sqrt{mn})^{k-1}}
       \sum_{f\in B_k(q)}\overline{a_{fa}(m)}a_{fb}(n)
 =\delta_{ab}\delta_{mn}
   +2\pi i^{-k}\sum_\gamma\frac{S_{ab}(m,n;\gamma)}\gamma
                              J_{k-1}(x_\gamma).
 \tag{actual-cross-Petersson}
\]

对 l=k-1 为正奇数，乘2l tilde phi(l)并求和。
配套篇的阶乘界与小参数 J_l(A/gamma) 界使几何双重和绝对
收敛；谱侧可先用两份同尖点 Petersson 的非负对角项做 Cauchy。
经 Gamma 归一后的单点谱质量一致有界于 k，故阶乘衰减也保证
谱 k 和绝对收敛。这里没有用一般权重大筛去隐藏最低权重。

利用
sum_(l odd>0)l i^(l+1)J_l(x)=-xJ_0(x)/2
（由 lJ_l=x(J_(l-1)+J_(l+1))/2 逐项相消），对角项正好消去。
最终得到

\[
 \boxed{\begin{split}
 \sum_\gamma\frac{S_{ab}(m,n;\gamma)}\gamma\phi(x_\gamma)
  ={}&\sum_{\substack{k\ge2\\k\ {m even}}}
       \frac{i^k\Gamma(k)}{\pi(4\pi\sqrt{mn})^{k-1}}
       \widetilde\phi(k-1)
          \sum_{f\in B_k(q)}\overline{a_{fa}(m)}a_{fb}(n)\\
    &+\sum_j\frac{M^+_{ab,j}(m,n)}{\cosh(\pi r_j)}\widehat\phi(r_j)
       +\frac1\pi\int_{\mathbb R}C^+_{ab}(m,n;r)\widehat\phi(r)dr.
 \end{split}}
 \tag{actual-positive-Kuznetsov}
\]

系数1/pi来自2l乘 Petersson 反解的1/(2pi)，不能改成1/(2pi)。
phi_B 在0的 O(x) 尾与 phi_H 的尾相互消去，最后几何侧才恢复
原始紧支撑 phi；中间步骤没有错误地假设 phi_H 紧支撑。

## 6. 异号完整公式

第4.3节合法换序后，K 反演将几何侧变成
sum_gamma (2/(pi gamma))S_ab(m,-n;gamma)phi(x_gamma)。
H-K 卷积则给 x cosh(pi r)K_(2ir)(x)，而不是省去 cosh 的式子。
将等式乘 pi/2，正好得到

\[
 \boxed{\sum_\gamma\frac{S_{ab}(m,-n;\gamma)}\gamma\phi(x_\gamma)
 =\sum_j\frac{M^-_{ab,j}(m,n)}{\cosh(\pi r_j)}\check\phi(r_j)
             +\frac1\pi\int_{\mathbb R}C^-_{ab}(m,n;r)\check\phi(r)dr.}
 \tag{actual-negative-Kuznetsov}
\]

其中 check phi 恰为第1节的2cosh(pi r)乘 K 积分。它没有全纯
谱项，也没有对角项；这些缺席由实际积分和谱反演说明，不是
在陈述时删去。所有谱求和、积分均绝对收敛。

## 7. 原刊归一化核对与交付边界

以下差异只针对这里固定的标准 K、未除面积的内积及 Fourier
系数；每项都由上文实际积分或有限代数确定，而非为了匹配打印
结果重新缩放对象。冻结前篇的同号 Gram 不需要改动。

| 原刊位置 | 所印系数/式子 | 本篇实际计算 |
|---|---|---|
| pp.251--252 Lemmas 4.3--4.4 | 异号径向-Beta 系数 pi 2^(2-s1-s2) | pi 2^(3-s1-s2)，径向2不能省略 |
| p.253 Lemma 4.6 | 谱前因子 st/(4pi sqrt(mn)) | st/(4sqrt(mn))，同一 Gamma 配对 |
| p.254 (4.9) | 异号几何4pi sqrt(mn)/gamma^2 | 8sqrt(mn)/gamma^2 |
| p.254 (4.11) | 负 H-K 积分等于 xK | 正积分等于 x cosh(pi r)K |
| p.228 (1.19) | 全纯 Gamma 项前1/(2pi) | 1/pi，由2l与 Petersson2pi合成 |
| p.228 (1.23) | K 变换前4cosh(pi r)/pi | 2cosh(pi r) |

来源：[DI82 定义与定理，pp.225--228](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0020.pdf)，
[§4，pp.250--255](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0023.pdf)。
比较的是逐页印刷式与本篇实际归一化，不主张发现新的谱定理。
本篇公式与原刊目标测试公式的相应谱项只差已明确的固定常数；
因此这些常数本身不改变 DI 的幂次预算，但仍必须保持准确。

[DI82 §9.1，pp.278--280](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0028.pdf)
使用 infinity 到1/s 的同号和异号公式；当前 S=1 的实际跨尖点
对象已由2节覆盖。并非只完成一个不足以进入 DI11 的对角版本。

下一步的实质缺口仍有：变化尺度测试核的定量估计、区间 m
系数所需的 X 放大异常谱估计、DI11 全部参数接合以及机器形式化。
本篇闭合测试核公式，不把上述后续难点包装成假设后宣布完成。
没有新 Lean/Lake 运行，最终源验证不等于最终 main 集成通过。

English summary: derive actual same-sign and opposite-sign Kuznetsov test
identities at the cusps used by the S=1 application, including the mixed cusp
Kloosterman parametrization, holomorphic contribution and full continuous
spectrum. Retain the radial factor two and exact scalar-transform constants;
justify all exchanges using separately proved absolute bounds. Amplified
exceptional spectrum and DI11's uniform parameter budget remain open.
