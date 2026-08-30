# Conrey 的 DI 谱路线：完整 L2 谱分解与实际预 Kuznetsov 等式

先说结论：本篇补上前篇尚未证明的“没有遗漏的正交补”。
由实际不完全 Eisenstein 级数的 Mellin 展开和尖点空间的紧
resolvent，证明 Gamma_0(q) 上常数、Maass 尖点形式、Eisenstein
波包构成完整 L2 正交分解。再将前篇的真实 Poincare 配对代入，
得到谱 Gram 等式以及同尖点的固定实参数预 Kuznetsov 等式。

本篇不把等式限于一个假设的完备基，也不以有限维 Bessel 代替
Parseval。任意测试核的 Kuznetsov 变换/反演、X 放大异常谱和
完整 DI11 仍在后续；原生 Conrey 严格 >2/5 仍未完成。

冻结基点 9dec9ce5613e22ea1a20187fc2fc5ffaca90780e。
只新增纸面证明，不改冻结祖先、Lean、Lake 或契约。
这是经典谱理论的逐步推导，不主张发现新谱定理。

## 1. 记号与要证明的满射

令 X=Gamma_0(q)\H，q 为正整数，dmu=dxdy/y^2，
Delta=-y^2(partial_x^2+partial_y^2)。内积第一变量线性。
各尖点均采用宽度1缩放，A 是全部不等价尖点的有限集合。
记 V=vol(X)，E_a(z,s) 和 Phi_ab(s) 均为前篇实际构造的对象：

\[
 E_a(\sigma_b z,s)=\delta_{ab}y^s+\Phi_{ab}(s)y^{1-s}
             +\text{指数衰减的非零 Fourier 模}.
\]

前篇已经证明临界线正则性、散射酉性/函数方程、四项
Maass--Selberg，以及正频波包
W_h=sum_a integral_0^infty h_a(r)E_a(1/2+ir)dr 的等距式
||W_h||^2=2pi||h||^2。其闭像记为 H_cont。
这里不预先假设 H_cont 的正交补是什么。

本篇证明存在由实际光滑 Maass 尖点特征函数组成的正交归一族
u_j，使每个 f in L2(X) 有 L2 意义下的展开

\[
 f=\frac{\langle f,1\rangle}{V}\,1
       +\sum_j\langle f,u_j\rangle u_j
       +\frac1{4\pi}\sum_{a\in A}\int_{\mathbb R}
                 \langle f,E_a(1/2+ir)\rangle E_a(1/2+ir)\,dr.
 \tag{actual-full-spectral-expansion}
\]

一般 L2 的 Eisenstein 配对按前篇波包等距嵌入的对偶解释；
有绝对可积配对时就是通常积分。连续项由 L2 波包极限定义，
不要求对任意 f 逐点绝对收敛。相应 Parseval 为

\[
 \|f\|_2^2=\frac{|\langle f,1\rangle|^2}{V}
       +\sum_j|\langle f,u_j\rangle|^2
       +\frac1{4\pi}\sum_a\int_{\mathbb R}
                         |\langle f,E_a(1/2+ir)\rangle|^2dr.
 \tag{actual-full-Parseval}
\]

## 2. 右半平面只有一个实际残余项

### 2.1 本原化矩阵的绝对收敛逆

沿用前篇本原模 q 行的有限向量空间。令 T_k 将行 v 送到
k^(-1)v，(k,q)=1；则 T_m T_n=T_(mn)，且 T_k 是置换矩阵。
前篇实际矩阵

\[
 M_q(s)=\sum_{(k,q)=1}k^{-2s}T_k
\]

在 Re s>1/2 已绝对收敛。在同一半平面，定义

\[
 N_q(s)=\sum_{(k,q)=1}\mu(k)k^{-2s}T_k.
 \tag{actual-Mobius-matrix-inverse}
\]

两个绝对收敛级数可相乘，n 项系数为 sum_(d|n) mu(d)，等于
n=1 时的1、其余0。因此 M_q(s)N_q(s)=N_q(s)M_q(s)=I。
特别地 ||M_q(s)^(-1)|| <= zeta(2 Re s)，可取有限维 l2 或行和范数。
没有在这里假设某个 Dirichlet L 函数不为零。

前篇 H_v 的 Fourier 展开在 Re s>1/2 只有 s=1 可能有极点：
非零模全纯，y^s 零模的 Dirichlet 变量为2s，另一零模为2s-1，
Gamma(s-1/2) 在该开半平面无极点。周期 Dirichlet 展开的
s=1 极点是一阶。因此 E_a 在 Re s>1/2 也只有 s=1 的至多一阶极点。

### 2.2 留数、尖点宽度和体积

对任何模 q 行 v，正负整数 c 的周期和
sum_(c!=0,c=v_1 mod q) |c|^(1-2s) 在 s=1 的留数为1/q。
前篇 H_v 的零模前因子在 s=1 为 pi/q，所以
Res_(s=1) H_v(z,s)=pi/q^2，与 z、v 无关。

令 L_q(2)=sum_(k,q)=1 k^(-2)=zeta(2) product_(p|q)(1-p^(-2))。
常向量是 M_q(1) 的特征向量，特征值 L_q(2)，故
Res P_v=pi/(q^2 L_q(2))。
恢复实际 E_a 的公式为 E_a=w_a^(-s) sum_(v in R_a)P_v/2。
准确的有限计数是

\[
                     |R_a|=w_a\varphi(q).
 \tag{actual-residue-row-count}
\]

证明：Gamma_0(q) 在模 q 的像是上三角行列式1矩阵，大小
q phi(q)。其在 tau_a^(-1) 后取下行的每个纤维大小为 q/w_a：
相同下行的上行只差整数倍下行，合法倍数恰为 w_a 的倍数。
模 q 上三角矩阵确实都可提升：SL_2(Z/q) 由初等矩阵生成，
消元时先在每个素幂因子选择单位枢轴，再以 CRT 合并；
初等矩阵各自有整数提升，其下左模 q 为0保证提升在 Gamma_0(q)。
这个计数也包括 q=1、2；-I 已通过恢复 E 时的1/2处理。

所以每个 a 的留数同为

\[
 c_q=\frac{\pi\varphi(q)}{2q^2 L_q(2)}
       =\frac{3}{\pi q\prod_{p\mid q}(1+1/p)}
       =\frac1V.
 \tag{actual-E-residue}
\]

这里 zeta(2)=pi^2/6 可由区间锯齿函数的 Fourier Parseval 得到。
指数 q product_(p|q)(1+1/p) 则是本原模 q 行数
q^2 product_(p|q)(1-p^(-2)) 除以单位数 phi(q)，也就是
Gamma_0(q) 在 SL_2(Z) 的指数。SL_2(Z) 基本域双曲面积为
integral_(-1/2)^(1/2) (1-x^2)^(-1/2)dx=pi/3，给出 V。

于是 s=1 留数是实际常函数 1/V，非零；右半平面没有其他
残余系列。这一结论还不是完整谱分解，只是后面移线所需的
准确极点账本。

## 3. 不完全 Eisenstein 级数和小高度计数

取 eta in C_c^infty((0,infinity))，定义实际局部有限和

\[
 E_a[\eta](z)=\sum_{\gamma\in\Gamma_a\backslash\Gamma}
                    \eta(\operatorname{Im}(\sigma_a^{-1}\gamma z)).
 \tag{actual-incomplete-Eisenstein}
\]

其光滑且在 X 上有紧支撑。局部有限性来自整数下行的椭圆界；
在另一尖点高度 y 趋于无穷时，零下行给出的高度是固定常数
乘 y，非零下行的高度至多 C_q/y，最终都离开 eta 的紧支撑。
因此

\[
             \Delta E_a[\eta]=E_a[-y^2\eta''(y)].
 \tag{actual-incomplete-Laplacian}
\]

若 f in L2(X)，展开配对合法，并得到

\[
 \langle f,E_a[\eta]\rangle
       =\int_0^\infty f_a^0(y)\overline{\eta(y)}\,\frac{dy}{y^2},
 \qquad f_a^0(y)=\int_0^1 f(\sigma_a(x+iy))dx.
 \tag{actual-horocycle-duality}
\]

f_a^0 在每个紧 y 区间可积；绝对展开由
integral_X |f| E_a[|eta|] dmu < infinity 保证，后者用
紧支撑和 Cauchy--Schwarz 即得。

下面的小高度估计将用于真实 resolvent，而不是替代谱计数。
固定 eta，令 eta_epsilon(y)=eta(y/epsilon)，0<epsilon<=1。
则

\[
                  \|E_a[\eta_\epsilon]\|_\infty
                         \ll_{q,\eta}\epsilon^{-1}.
 \tag{actual-small-height-count}
\]

给出计数：在归一化尖点 b、y>=Y>=1，写 z 的整数缩放坐标为
w_b(x+iy)。非零整数下行 c 的贡献要求
|c w_b(x+iy)+d|^2 <= C_(q,eta) y/epsilon，从而
0<|c| <= C/sqrt(epsilon y)；每个 c 的 d 数至多
C sqrt(y/epsilon)+1。若没有非零 c 则此部分为0；否则相乘
至多 C(epsilon^(-1)+(epsilon y)^(-1/2)) << epsilon^(-1)。
本原零行只有 d=+/-1，贡献 O(1)。在紧核的有限坐标片内，
c,d 分别处于 O(epsilon^(-1/2)) 长度的区间，同样得 O(epsilon^(-1))。
省去互素/同余条件只增大计数。有限体积也给出
||E_a[eta_epsilon]||_2 <<_(q,eta) epsilon^(-1)。

## 4. Mellin 移线的边界控制

### 4.1 固定正距离的竖直增长

对 sigma in [1/2+delta,2]、delta>0、|r|>=2，前篇 H_v
展开与2.1给出在任意固定 z 紧集、任意有限阶 z 导数上

\[
                  E_a(z,\sigma+ir)\ll_{q,\delta,\Omega}(1+|r|)^B
 \tag{fixed-strip-polynomial-growth}
\]

（B 可随导数阶和紧集改变）。细节如下。零模的 Gamma 比值用
Stirling，周期 Dirichlet 级数用前篇的两次 Euler--Maclaurin，
得到多项式增长。对非零模，令 T=1+|r|，在
K_nu(X)=1/2 integral_R exp(-X cosh u+nu u)du 中把 u 平移
i sign(r)(pi/2-1/T)。竖直端边由双指数衰减消失，得到

\[
 |K_{\alpha+ir}(X)|
       \le e^{-\pi|r|/2+1}K_\alpha(X\sin(1/T)).
\]

对固定有界 alpha，可用
K_alpha(v) <= C_A(1+v^(-A)) exp(-v/2)，A 取足够大。
Gamma(s)^(-1) 的 e^(pi|r|/2) 与之抵消，剩下非零模的
多项式 n 权乘 exp(-c n y/T)，其和仍是 T 的多项式。
置换矩阵 Möbius 逆的范数至多 zeta(1+2delta)，完成估计。
这足够支持先移线到任何固定 sigma>1/2，尚未声称 delta 一致。

### 4.2 从 Maass--Selberg 非负性取得统一散射界

固定尖点截断高度 Y>1，令 s=1/2+delta+ir，0<delta<=1/4。
对 E_a(s) 的 Maass--Selberg 对角式，记
B_a(s)^2=sum_b |Phi_ab(s)|^2，则

\[
 \|\Lambda^Y E_a(s)\|_2^2
    =\frac{Y^{2\delta}-B_a(s)^2Y^{-2\delta}}{2\delta}
       +2\operatorname{Re}
               \frac{\overline{\Phi_{aa}(s)}Y^{2ir}}{2ir}.
 \tag{actual-MS-diagonal-bound}
\]

当 |r|>=1 时，末项绝对值<=B_a(s)/|r|，而左边非负。因此
若 x=B_a(s)Y^(-2delta)，则
x^2 <= 1+(2delta/|r|)x，给出

\[
 B_a(s)\le Y^{2\delta}
        \left(\frac{\delta}{|r|}
                   +\sqrt{1+\frac{\delta^2}{r^2}}\right)\ll_Y1.
\]

在 |r|<=1、1/2<=sigma<=3/4 的紧矩形，2节的极点排除和前篇
临界线正则性保证 Phi 有界。故

\[
               \sup_{\substack{1/2\le\sigma\le3/4\\r\in\mathbb R}}
                        \|\Phi(\sigma+ir)\|\le C_q<\infty.
 \tag{actual-uniform-boundary-scattering}
\]

q 固定时的此常数只用于谱分解存在性；最终 Parseval 系数是
准确的1/(4pi)，不会把 C_q 传入后续的大筛主尺度。

### 4.3 截断波包的统一 L2 算子界

对 h in C_c^infty(R)^A，设
S_delta^Y h=sum_a integral_R h_a(r)Lambda^Y E_a(1/2+delta+ir)dr。
将前篇四项 Maass--Selberg 代入其范数；写 L=log Y、
k(r)=h(r)Phi(1/2+delta+ir)（h 视作行向量）。
前两项分别含 Cauchy 核
exp(+-i(r-t)L)/(2delta+i(r-t))，作用于 h 或 k。
由

\[
 \frac1{2\delta+iu}=\int_0^\infty e^{-2\delta x}e^{-iux}dx
\]

及实 Fourier Plancherel，每个相应二次型绝对值至多
2pi ||h||^2 或 2pi ||k||^2，另乘 Y^(+-2delta)。
交叉两项按主值写为核 exp(+-i(r+t)L)/(i(r+t))；
反射 t 后是 Hilbert 核，其 L2 算子范数为 pi。它们合计至多
2pi||h||||k||。主值与原式相符：在 r+t=0，两项的分子因
Phi 的实共轭/对称性恰好相消；不能把其中一项单独当作通常积分。

Hilbert 界本身可由对称截断的 Fourier 乘子证明：
PV integral exp(-i xi u)du/u=-i pi sign(xi)，先加
exp(-epsilon |u|)，积分给出 arctan，继而用有界乘子极限。
因此无需另引一个曲面谱输入。

结合4.2得到，统一于0<delta<=1/4，

\[
                       \|S_\delta^Yh\|_2\le C_{q,Y}\|h\|_2.
 \tag{actual-uniform-truncated-packet}
\]

在 delta=0，前篇正频等距及函数方程也给全轴波包界
||integral_R h(r)E(1/2+ir)dr||^2 <= 4pi||h||^2；
Lambda^Y 是在各尖点柱去掉水平常数模的 L2 正交投影，所以同样有界。

对紧支撑 h，临界线附近 Lambda^Y E 是 L2 值全纯函数：
紧核局部一致，尖点上非零模及参数导数统一指数衰减。
故 S_delta^Y h -> S_0^Y h 强收敛。由统一算子界和
C_c^infty(R)^A 的 L2 稠密性，此结论推广为

\[
 h_\delta\longrightarrow h_0\text{ in }L^2
 \quad\Longrightarrow\quad
 S_\delta^Yh_\delta\longrightarrow S_0^Yh_0\text{ in }L^2(X).
 \tag{actual-truncated-boundary-limit}
\]

## 5. 不完全 Eisenstein 的实际谱展开

定义 Mellin 变换
eta_hat(s)=integral_0^infty eta(y)y^(-s)dy/y。
它在每个固定竖条带内快速衰减，来自 log(y) 变量反复分部积分。
Mellin 反演及初始绝对展开给出

\[
 E_a[\eta]=\frac1{2\pi}\int_{\mathbb R}
                   \widehat\eta(2+ir)E_a(2+ir)dr.
\]

先移到 sigma=1/2+delta，0<delta<1/4。2节证明只跨过 s=1，
4.1保证水平边趋于0，且在每个 z 紧集可连同有限阶导数移线。
所以

\[
 E_a[\eta]=\frac{\widehat\eta(1)}V\,1
       +\frac1{2\pi}\int_{\mathbb R}
          \widehat\eta(\sigma+ir)E_a(\sigma+ir)dr.
 \tag{actual-interior-Mellin-shift}
\]

现在证明 delta 趋于0时确实为全 X 的 L2 极限，而不只是逐点
形式移线。取 h_delta 只有第 a 分量为 eta_hat(sigma+ir)。
这些 h_delta 在 L2(R)^A 趋于 h_0，且有统一任意阶快速衰减。
由4.2和临界线正则性，
k_delta=h_delta Phi(sigma+ir) -> k_0 也在 L2 中成立。

截断部分的强极限由4.3给出。各尖点常数项中，入射部分按
Mellin 反演恰为 delta_ab eta(y)，与 delta 无关；出射部分是

\[
 y^{1/2-\delta}\frac1{2\pi}
                    \int_{\mathbb R}k_{\delta,b}(r)e^{-ir\log y}dr.
 \tag{actual-outgoing-packet-tail}
\]

令 x=log y。其在 y>Y 的平方范数就是常数因子乘
integral_(log Y)^infty exp(-2delta x)|Fourier(k_delta)(x)|^2 dx。
实 Fourier Plancherel、k_delta 的 L2 强收敛和乘子
exp(-delta x)->1 的强收敛（x>=log Y>0，模长<=1），给出
出射常数模的 L2 极限。与截断部分相加，得到完整的

\[
 \boxed{E_a[\eta]=\frac{\widehat\eta(1)}V\,1
       +\frac1{2\pi}\int_{\mathbb R}
           \widehat\eta(1/2+ir)E_a(1/2+ir)dr\quad\text{in }L^2(X).}
 \tag{actual-incomplete-spectral-expansion}
\]

这里的临界线积分是前篇已经定义的全轴波包。该证明没有依赖
任何假设的全谱完备性、零点自由线或未核对的任意高频点值界。

H_cont 与常数正交也可直接证明。临界线 E 在 X 上可积；
积分 Delta E=lambda E 时，尖点顶边导数为 O(y^(-1/2))，
趋于0，lambda=1/4+r^2>0。因此 integral_X E_a(1/2+ir)dmu=0。
先对紧谱支撑波包绝对换序，再由 L2 极限，得到 H_cont perp 1。

## 6. 真正尖点空间的紧 resolvent 和特征基

### 6.1 由水平平均定义闭空间，不预置特征函数

令 S 是全部 E_a[eta] 在 L2 中生成的闭空间，令 C=S^perp。
由3节实际展开，

\[
 C=\{f\in L^2(X): f_a^0(y)=0
               \text{ for a.e. }y>0,\text{ every cusp }a\}.
 \tag{actual-closed-cuspidal-space}
\]

这里要求全部高度，而不是只在截断尖点柱上为0。
接下来证明 C 本身由实际 Delta 特征函数张成，不能先把这当作定义。

### 6.2 先在全空间构造负参数 resolvent

在 C_c^infty(X) 上取非负能量型
Q(u,v)=integral_X (u_x overline(v_x)+u_y overline(v_y))dxdy。
该型可闭：若 u_n 在 L2 趋于0、弱导数在能量范数 Cauchy，
对任意局部光滑紧支撑测试函数分部积分可知导数极限为0。
以 Q(u,u)+2||u||^2 完成其型域。Riesz 定理给每个 f in L2
唯一 u=Rf，使

\[
              Q(u,v)+2\langle u,v\rangle=\langle f,v\rangle
                         \quad(\text{所有型域 }v).
 \tag{actual-global-resolvent}
\]

所以 R 有界、正、自伴，||R||<=1/2，且 R 单射：
Rf=0 时 f 与稠密的 C_c^infty 正交。局部分布意义下
(Delta+2)u=f。此构造没有先引用曲面 Delta 的完整谱定理。

### 6.3 R 保持全部高度的尖点平均为0

若 f in C，用紧支撑测试 E_a[eta] 以及3节的 Delta 恒等式，
得 u=Rf 的平均 A_a(y)=u_a^0(y) 满足分布 ODE

\[
                      -y^2A_a''(y)+2A_a(y)=0.
\]

一维局部正则性或直接分布积分给
A_a(y)=c_+ y^2+c_- y^(-1)。在 y 趋于无穷时，Jensen 与
u in L2 的尖点柱积分排除 c_+。还不能据此排除 c_-。

取非负、非零固定 eta。由3节小高度计数，

\[
 |\langle u,E_a[\eta_\epsilon]\rangle|
      \le\|u\|_2\,O_{q,\eta}(\epsilon^{-1}).
\]

而平均 ODE 与实际展开使左边准确等于
|c_-| epsilon^(-2) integral_0^infty eta(t)t^(-3)dt。
令 epsilon 趋于0，得到 c_-=0。因此 u in C，R 确实保持 C。
由于 R 自伴，C 的正交补也被保持；R|C 是正自伴单射。

### 6.4 紧性和真正的 Maass 特征基

对 ||f||<=1，u=Rf 的范数和能量由6.2统一有界。
在每个宽度1尖点柱，u 的水平平均为0，所以一维圆周 Poincare
不等式给出

\[
 \int_{y>Y}|u|^2\,d\mu
       \le\frac1{4\pi^2Y^2}
                     \int_{y>Y}|u_x|^2dxdy.
 \tag{actual-cuspidal-tail-compactness}
\]

对全部互不相交尖点柱求和，右边仍由总能量控制，尾部统一趋于0。
紧核上的 H1 有界族在 L2 预紧：有限坐标片、分割函数和实
Fourier 截断给出高频尾至多 O(R^(-2)) 乘 H1 范数平方，
低频部分的紧性再用有限网格逼近。因此 R|C 为紧算子。

紧正自伴算子的特征基结论可在这里直接应用，或按以下论证：
在单位球上用紧性达到最大非零 Rayleigh 值，取得特征向量；
逐次在其正交补重复。若所得族的闭包还有非零正交补，单射性
使 R 在该补上非零，紧性又会给一个非零特征向量，矛盾。
故有 C 的完整正交归一族 u_j，R u_j=mu_j u_j，mu_j>0。

由全空间分布方程，
Delta u_j=(mu_j^(-1)-2)u_j=lambda_j u_j，不是带隐藏
Lagrange 乘子的受限方程。局部椭圆正则性给 u_j 光滑：
将方程除以 y^2，在紧坐标片用截断后的 Euclidean Fourier
估计逐次从 H1 提升到 H2、H3 等，系数 y^(-2) 光滑；
有限椭圆稳定子处在上半平面局部覆盖上应用同一论证。
能量使 lambda_j>=0；等号会迫使 u_j 为全局常数，与 C 的零
平均条件矛盾。故 lambda_j>0，u_j 是实际 Maass 尖点形式。
前篇已经证明的3/16谱隙可应用于该完整族。

## 7. 排除遗漏的正交补，得到完整 Parseval

5节证明 S subset span{1} + H_cont；右边是闭正交和。
6节证明 C=S^perp 由实际尖点特征函数 u_j 张成。
每个 u_j 与常数正交（积分 Delta u_j=lambda_j u_j，指数尖点
尾使边界项为0），也与 H_cont 正交（前篇实际 Eisenstein/尖点
配对为0）。因此 span{1}+H_cont subset C^perp=S。
两个包含合起来给出

\[
          L^2(X)=\mathbb C1\ \mathbin{\widehat\oplus}\
                      C\ \mathbin{\widehat\oplus}\ H_{\rm cont}.
 \tag{actual-full-orthogonal-decomposition}
\]

这一步确实排除了遗漏的正交补，而不是重述波包等距性。
按正频等距，连续投影为
(1/(2pi)) sum_a integral_0^infty <f,E_a(r)>E_a(r)dr。
前篇函数方程同时给系数向量
v(-r)=overline(Phi(1/2-ir))v(r) 和
E(-r)=Phi(1/2-ir)E(r)；酉性使
sum_a v_a(-r)E_a(-r)=sum_a v_a(r)E_a(r)。
因此换成全轴时准确因子是1/(4pi)。
普通正交投影与正频等距遂给1节的展开及 Parseval。

对任意 f,g in L2，还得到极化后的准确配对恒等式

\[
 \langle f,g\rangle=\frac{\langle f,1\rangle\overline{\langle g,1\rangle}}V
   +\sum_j\langle f,u_j\rangle\overline{\langle g,u_j\rangle}
   +\frac1{4\pi}\sum_a\int_{\mathbb R}
              \langle f,E_a(r)\rangle\overline{\langle g,E_a(r)\rangle}dr.
 \tag{actual-polarized-Parseval}
\]

谱和及连续积分的绝对收敛由已证 Parseval 和 Cauchy--Schwarz
保证，不需再假定点态 Fourier 系数的额外增长界。

## 8. 实际 Poincare 谱 Gram 与固定参数预 Kuznetsov

### 8.1 消去真实常数投影

对当前宽度1尖点 a=infinity、0/1，取实际 U_am(z;s)。
无穷尖点的 Re s>3/4 L2 延拓已在前篇证明；0/1 的对象由实际
Fricke 酉变换取得，同样成立。初始 Re s>1 绝对展开常数配对，
x 积分 integral_0^1 e(mx)dx=0，所以 <U_am(s),1>=0；
L2 值解析唯一性把它延拓到 Re s>3/4。
这里没有忽略一个未计算的残余谱项。

记
u_j(sigma_a z)=sqrt(y)sum_(n!=0)rho_ja(n)K_(ir_j)(2pi|n|y)e(nx)，
lambda_j=1/4+r_j^2；r_j 实非负或 r_j=i nu_j、0<nu_j<=1/4。
对 E_c(s_r)，保留前篇
rho^E_ca(n,s_r)=2pi^(s_r)n^(ir)phi_can(s_r)/Gamma(s_r)。
令 t 为实数，D(t,r)=cosh(pi(t-r))cosh(pi(t+r))。
前篇实际配对与7节 Parseval 得到

\[
\begin{split}
 &\langle U_{am}(1+it),U_{bn}(1+it)\rangle\\
 &\quad=\frac1{4\sqrt{mn}}\left(\frac nm\right)^{it}
       \frac{\sinh(\pi t)}t
       \left\{\pi\sum_j
              \frac{\overline{\rho_{ja}(m)}\rho_{jb}(n)}{D(t,r_j)}
       +\sum_{c\in A}\int_{\mathbb R}
          \left(\frac nm\right)^{ir}
          \overline{\varphi_{cam}(1/2+ir)}
                    \varphi_{cbn}(1/2+ir)
                    \frac{\cosh(\pi r)}{D(t,r)}dr\right\}.
\end{split}
 \tag{actual-Poincare-spectral-Gram}
\]

这包括当前两尖点的交叉配对。t=0 用可去极限；异常参数的 D
按前篇 Gamma 配对定义，仍为正。所有无穷谱项由极化 Parseval
绝对收敛。它把此前仅有的 Bessel 上界真正升级为等式。

### 8.2 代表尖点的实际几何等式

先取 a=b=infinity。前篇从二维积分已经证明几何 Gram

\[
 \langle U_m(1+it),U_n(1+it)\rangle
   =\frac{\delta_{mn}}{4\pi n}
       -2i\left(\frac nm\right)^{it}
           \sum_{q\mid c}\frac{\operatorname{Kl}_c(m,n)}{c^2}
                  \int_{\gamma_\uparrow}
                    K_{2it}\left(\frac{4\pi\sqrt{mn}}c v\right)\frac{dv}{v},
\]

其中 gamma_up 是右半单位圆从 -i 到 i，端点按此前已证的
连续极限取值。其绝对模数和由实际 Weil 和 Macdonald 边界估计
保证。定义精确核

\[
 \mathcal D_{2it}(x)=\frac{2it}{\sinh(\pi t)}
                    \int_{\gamma_\uparrow}K_{2it}(xv)\frac{dv}{v},
 \qquad
 \mathcal H(r,t)=\frac{\cosh(\pi r)}{D(t,r)}.
 \tag{actual-pre-Kuznetsov-kernels}
\]

乘4sqrt(mn)(m/n)^(it)t/sinh(pi t)，将几何和移到左侧，得到

\[
\begin{split}
 &\sum_{q\mid c}\frac{4\sqrt{mn}}{c^2}\operatorname{Kl}_c(m,n)
                  \mathcal D_{2it}\left(\frac{4\pi\sqrt{mn}}c\right)
       +\frac{\delta_{mn}t}{\pi\sinh(\pi t)}\\
 &\quad=\pi\sum_j
       \frac{\overline{\rho_j(m)}\rho_j(n)}{\cosh(\pi r_j)}
                              \mathcal H(r_j,t)
   +\sum_{a\in A}\int_{\mathbb R}\left(\frac nm\right)^{ir}
           \overline{\varphi_{a\infty m}(1/2+ir)}
                     \varphi_{a\infty n}(1/2+ir)
                              \mathcal H(r,t)dr.
\end{split}
 \tag{actual-fixed-parameter-pre-Kuznetsov}
\]

纯同尖点0/1的等式也可由 Fricke 酉变换和全部谱通道的重编号
取得。这里未把尚未逐项展开的跨尖点几何模数和冒充本式；
跨尖点的谱 Gram 已由8.1单独明确给出。

此式是固定 t 的真实预 Kuznetsov。它尚不是任意紧支撑测试
函数在几何侧的完整变换公式：从本式到所需测试核还必须证明
相应 Bessel 变换/反演、参数移线与全部谱尾换序。
也未自动提供带 X^(2nu_j) 的异常谱估计。

## 9. 原刊对应与精确交付边界

- [DI82 第3节](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0022.pdf)：
  p.248 的 Lemma 3.7、(3.12)、(3.13) 和 Lemma 3.8：
  实际留数及原刊引用的 L2 谱分解/Parseval。本篇给出自己的满射论证，
  不把该引用当成已经原生证明的事实。
- [DI82 第4节](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0023.pdf)，
  pp.252--253 的 Lemma 4.5、(4.7)、(4.8)：对应本篇实际
  Poincare 谱 Gram、dv/v 半圆核与固定 t 预 Kuznetsov。

本篇已证明的对象是完整 L2 正交分解、常数残余项的准确留数、
全尖点不完全 Eisenstein 展开、真正尖点特征基及实际谱等式。
这些是数学论证，不是新条件接口或仅仅文件分类通过。

后续仍需：目标测试核的 Kuznetsov 变换与换序、X 放大异常谱、
DI11 的完整接合，以及把已审查数学逐步形式化。原生 Conrey
严格 >2/5 尚未达到，不以本篇 PR 或测试作为完成凭据。
所有 Lean/Lake 构建继续等待独占资源通知。

独立审查重点：Möbius 矩阵逆与留数、1/2及宽度计数、临界
散射的一致界、Cauchy/Hilbert 核主值、Mellin 的全 X 强极限、
全部高度平均的 resolvent 不变性、小高度 epsilon^(-1) 对
epsilon^(-2) 的排除、紧性/全特征方程、连续投影1/(4pi)及
预 Kuznetsov 的符号和半圆方向。

English summary: prove the full L2 spectral decomposition rather than
assuming completeness of the previously constructed wave packets.
An explicit Mobius inverse controls residual poles, Mellin-shifted
incomplete Eisenstein series identify the continuous-plus-constant
space, and a compact resolvent on the actual zero-horocycle-average
space supplies a complete cuspidal eigenbasis. Polarized Parseval
then gives the actual Poincare spectral Gram and fixed-parameter
pre-Kuznetsov identity. General test-kernel inversion, amplified
exceptional spectrum and native Conrey >2/5 remain separate work.
