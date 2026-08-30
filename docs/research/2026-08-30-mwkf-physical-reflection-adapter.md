# 从 (4.5) 到 reflection：共同截断、正确坐标与完整 signed operator

白话结论：可以把原 Poisson 主和完整地接回 reflection，但必须先恢复整数格，保留整个 Mellin 参数，并把四个 reflection 项放在同一个截断里。原 mollifier 系数与它的除数卷积不是同一个向量；原 AFE 对角与零核补回的对角也不是同一个对象。这些区别不能靠给 packet 改名消除。

本节修正主研究笔记 §§9.194–9.198 的三处过强表述，并给出全局恒等式的 adapter。没有证明 coupled-kernel gate，也没有证明新的 (T^2) saving。数值/有限测试只检验下面的有限代数，不替代连续分析证明。

## 1. 固定记号和三个不能混同的对象

沿用主笔记的 (a_N(d)=\mu(d)(1-\log d/\log N))、(N\ge2\)、(W\in C_c^\infty([1,2])\) 及精确 AFE 权 (V_t\)。设 (N\le T^3\)、(T\ge2\)。

原式的三类系数分别是

\[
 a=(a_N(d))_{d\le N},\qquad
 c_d=a_N(d)/\sqrt d,\qquad
 B_{N,z}(x)=\sum_{d\mid x,\ d\le N}a_N(d)d^z.
\tag{PA1}
\]

§9.194 的 Fourier Gram 用的是 (c_d\)，不是 (B_{N,0}(d)\)。因此“直接将 (B=F-R\) 代入该 Gram”是错误的，除非同时转换核。即使在有限模型 (N=2\)、(a=(1,-2)\)、(B(1),B(2)=(1,-1)\) 中，核

\[
 G=\begin{pmatrix}0&3\\3&0\end{pmatrix}
 \quad\Longrightarrow\quad
 a^TGa=-12,\qquad (1,-1)G(1,-1)^T=-6.
\tag{PA2}
\]

同样，原 AFE 对角是 (me=nd\)，可含 (d\ne e\)（例如 (d=1,e=2,m=1,n=2\)）。零核补回的 mollifier 对角是 (d=e\)。后者补回确实得到一个完整 Fourier Gram，但不能因此宣称它就是原 AFE 对角 (2.10)。

## 2. 从 (4.5) 恢复整数格：必须先重组所有 (h\)

固定一个有限 dyadic box 和 (q,r,s,\delta\)，令 (f(x)\) 为 (4.4) 中去掉 (e(-hx/s)\) 的完整光滑函数。它延拓为 (C_c^\infty(\mathbb R)\)。按 (4.3b) 的 Fourier 约定，

\[
 {1\over s}\sum_{h\in\mathbb Z}
 e(-h\delta\bar r/s)\widehat f(h/s)
 =\sum_{n\equiv-\delta\bar r\pmod s}f(n).
\tag{PA3}
\]

这只是带平移/缩放的 Poisson 公式；可对照 [NIST DLMF §1.8(iv)](https://dlmf.nist.gov/1.8.iv)。这里 (s=1\) 的相位取 1。对整数 (A>1,H\ge1\)，分部积分和 (\sum_{h>H}h^{-A}\le H^{1-A}/(A-1)\) 给出显式尾界

\[
 {1\over s}\sum_{|h|>H}|\widehat f(h/s)|
 \le {2s^{A-1}\over(2\pi)^A(A-1)}
 H^{1-A}\|f^{(A)}\|_1.
\tag{PA4}
\]

在有限 box 中，(\delta\) 也只有有限多个可能值：若 (x\asymp M\)、((rx+\delta)/s\asymp K\)，则 (\delta\in[sK/2-2rM,2sK-rM/2]\)。因此先在每个有限 box 令 (H\to\infty\) 是合法的。恢复格点后，

\[
 d=qr,\quad e=qs,\quad
 m={nr+\delta\over s},\quad
 x_0=dn,\quad y_0=em,\quad y_0-x_0=q\delta.
\tag{PA5}
\]

反向唯一地由 (q=(d,e)\)、(r=d/q,s=e/q\)、(\delta=(me-nd)/q\) 得到。Poisson 的 (1/s\) 保留在 (PA3)；恢复格点后外系数是 (2/(q\sqrt{rs})=2/\sqrt{de}\)，没有额外 Jacobian。

然后才求和 dyadic partition。原整数点上的局部有限 partition-of-unity 与 (2.5a) 的绝对收敛保证无端点误差。**单个固定 (h\) 的积分变量不是整数，(PA5) 的整数乘积 regrouping 不能逐 (h\) 使用。** 在 Poisson 表达式中保留 (h,\delta\) 和 (h\delta\) 是正确的；将全局重组后的乘积核伪标成某一个原 (h\) 则不正确。

## 3. 空小尺度必须正则化；零核依赖明确的延拓选择

若直接把所有空小尺度也加入“共同零模”，(9.381) 会产生

\[
 \int_0^\infty V_t(u^2)\,{du\over u}.
\tag{PA6}
\]

由 (V_t(u^2)=1+O_t(u^{2c})\)、(0<c<1/4\)，它在 0 对数发散。不能把它称为一个已定义的有限公共权 (\Omega\)。

固定一次 (\chi\in C^\infty(\mathbb R)\)，满足 (0\le\chi\le1\)、(\chi(u)=0\) 当 (u\le1/4\)、(\chi(u)=1\) 当 (u\ge1/2\)。在 (4.4) 中乘上

\[
 \chi(x)\chi((rx+\delta)/s).
\tag{PA7}
\]

它在所有正整数 zeta 变量上恒为 1，故不改变原 AFE。记相应第一层 Poisson 零项与非零项为 (Z_\chi,O_\chi^{\ne0}\)，原项为 (Z,O^{\ne0}\)。逐有限 box 的 (PA3) 给出

\[
 (Z_\chi-Z)+(O_\chi^{\ne0}-O^{\ne0})=0,
 \qquad
 \mathcal R=\mathcal D_{\rm AFE}+Z_\chi+O_\chi^{\ne0}-T\mathcal Q.
\tag{PA8}
\]

差 (Z_\chi-Z\) 必须保留；没有证明它小。这也说明改变连续延拓可以在零模与非零补集之间移动质量，虽然完整余项不变。使用原式 (4.8) 时，同一账本就是 (\mathcal R=\mathcal E_{\rm arch}+O^{\ne0}\)，不能另丢 (\mathcal E_{\rm arch}\)。

现在 (9.380) 所指定的短模数双 completion 零系数可以严格计算。令 (b=r-s\ne0\)。去掉 Fourier 因子后的 (f_\chi(x,\delta)\) 是 Schwartz 函数：两个 zeta 变量均远离 0，且 (V_t\) 在它们的乘积上任意阶衰减。部分 Fourier 变换仍是 Schwartz，故 (9.380) 的 (h,\delta\) 积分绝对收敛。先对 (h\) 反演得到 (s f_\chi(-\delta/b,\delta)\)，再置 (\delta=-bu\)。相应 (s\) 与 (1/s\)、(|b|\) 与 (1/|b|\) 恰好抵消，且两个 zeta 变量都等于 (u\)。于是所选延拓的零核为

\[
 \begin{aligned}
 \Omega_\chi(t)&=2W(t/T)\int_0^\infty
             \chi(u)^2 V_t(u^2)\,{du\over u},\\
 G_{\chi;d,e}&={\mathbf1_{d\ne e}\over\sqrt{de}}
       \int_{\mathbb R}\Omega_\chi(t)(e/d)^{it}\,dt.
 \end{aligned}
\tag{PA9}
\]

因子 2 已包含两个相同 AFE 方向，不能再乘一次 2。这里的“canonical”只能指**固定了此延拓与此 completion 后**的零核，不能指延拓无关的次主常数。恢复离散 completion 时，删除的 (h=0\)、(\delta=0\) 轴与其他非零对偶频率都必须进入补集。由 (2.5)，(\Omega_\chi\) 至多多一个 (\log(2T)\) 因子；若需要正性，仍须另外验证该权的正性。

## 4. 完整 Mellin reflection 与共同乘积截断

在原绝对收敛直线 (z=2+i\tau\) 上，对整数 (X\ge N\) 只保留 (x,y\le X\)。令

\[
 \begin{aligned}
 F_z(x)&=\sum_{D\mid x}\mu(D)
          (1-\log D/\log N)D^z
        =P_x(z)-P'_x(z)/\log N,\\
 R_{N,z}(x)&=\sum_{D\mid x,\ D>N}\mu(D)
          (1-\log D/\log N)D^z,\qquad
 P_x(z)=\prod_{p\mid x}(1-p^z).
 \end{aligned}
\tag{PA10}
\]

包括 (x=1\) 的空积约定后，对每个复数 (z\) 都有

\[
 B_{N,z}(x)=F_z(x)-R_{N,z}(x),\qquad
 Dk=x,\ D>N\Longrightarrow kN<x\le X.
\tag{PA11}
\]

严格端点 (kN<x\) 没有 floor 误差。只有在已限制 (X\asymp NT^{1/2}\) 的局部范围才可说 (k\ll T^{1/2}\)，不能把这个长度断言推广到任意全局截断。

定义有限双线性泛函（两侧是同一个 (z\)，不是共轭 Mellin 参数）

\[
 \mathcal A_X(U,V)=\frac2{2\pi i}\int_\mathbb R W(t/T)
 \int_{(2)}{g_t(z)G_t(z)\over z}
 \sum_{x,y\le X}{U_z(x)V_z(y)\over(xy)^{1/2+z}}
                (y/x)^{it}\,dz\,dt.
\tag{PA12}
\]

有限求和及 Gaussian Mellin 衰减使这里每个有限-(X\) 项可积。原四变量求和严格等于

\[
 I_X=\mathcal A_X(B,B)
 =\mathcal A_X(F,F)-\mathcal A_X(F,R)
  -\mathcal A_X(R,F)+\mathcal A_X(R,R).
\tag{PA13}
\]

这是整个 (z\) 家族的 reflection，不是只取 (z=0\)。(F_0\) 的 prime-power 稀疏性不能用于其他 (z\)。四项必须共用同一个 (X\)；未证明它们在 (X\to\infty\) 时分别收敛。

为证明组合极限，设 (A_z=\sum_x|B_{N,z}(x)|x^{-5/2}\)，(E_z(X)\) 为其 (x>X\) 尾。因为 (|a_N(d)|\le1\)，

\[
 A_z\le\zeta(5/2)\sum_{d\le N}d^{-1/2}\ll\sqrt N,
 \quad E_z(X)\ll X^{-3/2}\sum_{d\le N}d\ll N^2X^{-3/2}.
\tag{PA14}
\]

这两个界对所有 (\tau\) 一致；第二个界用 (X/d\ge1\) 和 (\sum_{n>u}n^{-5/2}\ll u^{-3/2}\)。矩形外的双和至多 (2A_zE_z(X)\)。再由 (2.5b) 在 (Re z=2\) 上的 Gaussian 可积 majorant 得到

\[
 \boxed{|I-I_X|\ll_W T^3N^{5/2}X^{-3/2}.}
\tag{PA15}
\]

因此 (N\le T^3\) 时，(X\ge T^{7+2A/3}\) 给出 (O_W(T^{-A})\)。这是全局 adapter 的充分截断，不是最优 core 长度。由 (4.8)、(PA13)–(PA15)，

\[
 \boxed{\mathcal E_{\rm arch}+\sum_{q,R,S,K,M}O^{\ne0}_{q;R,S,K,M}
 =\lim_{X\to\infty}\{
 \mathcal A_X(F,F)-\mathcal A_X(F,R)-\mathcal A_X(R,F)
 +\mathcal A_X(R,R)-T\mathcal Q\}.}
\tag{PA16}
\]

左边按 (PA3) 的 box-first Poisson 顺序，右边按共同-(X\) 顺序。没有逐频率 reflection，也没有换序后将四个无穷项分别估计的授权。

## 5. 在正确的共同坐标上构造 signed operator

令 (C_{z,X}(x,d)=\mathbf1_{d\mid x}d^z\)，(d\le N,x\le X\)；令 (K_{z,t}(x,y)=(xy)^{-1/2-z}(y/x)^{it}\)。全 AFE 核（已包含 dyadic partition 的总和）为

\[
 H_X={2\over2\pi i}\int W(t/T)\int_{(2)}
      {g_t(z)G_t(z)\over z}\,C_{z,X}^{T}K_{z,t}C_{z,X}\,dz\,dt,
 \quad I_X=a^TH_Xa.
\tag{PA17}
\]

设 (L\) 是满足 (a^TLa=T\mathcal Q\) 的原 LCM 主项核。(H_X\) 的各个矩阵元收敛（(N\) 固定有限，或用同样绝对值尾界），记 (H=\lim_XH_X\)。在原 (d,e\) 坐标上定义

\[
 R=H-L,\qquad J_\chi=H-L-G_\chi,\qquad
 R=G_\chi+J_\chi,\qquad \mathcal R=a^TRa.
\tag{PA18}
\]

这是从完整物理 AFE 核计算出的补集，不是任意供应的测试矩阵。(J_\chi\) 保留所有非零频率、轴修正、延拓补偿、主项减法与原 AFE 对角账本；除非另外证明这些修正已分别归并，不能把它简称为“只有非零 determinant 的谱核”。

若一定要在 (B\) 坐标上写 canonical Gram，设有限 Möbius 反演矩阵 (U(d,x)=\mathbf1_{x\mid d}\mu(d/x)\)，并令 (L_z=D_{-z}P_NU\)。则

\[
 a=L_zB_{N,z},\qquad
 a^TG_\chi a=B_{N,z}^T L_z^T G_\chi L_z B_{N,z}.
\tag{PA19}
\]

在 Hermitian 能量形式中应相应使用共轭转置 (L_z^*\)，不能把 Mellin 双线性转置与 Hilbert 伴随混用。最安全的统一空间是 (PA18) 的原 mollifier 坐标。

给定原坐标上的概率密度 (p,q\)，只中心化 (J_\chi\)：

\[
 C=(I-\mathbf1p^T)J_\chi(I-q\mathbf1^T),\quad
 R_{\rm res}=G_\chi+J_\chi-C,
 \quad R=R_{\rm res}+C,\quad p^TC=Cq=0.
\tag{PA20}
\]

随后只做一次全局 (TT^*\)，保留 (RR^*,RC^*,CR^*,CC^*\) 四项。改变 (\chi\) 或密度只改变分配，不改变总核 (R\)。一个有限有理 fixture 的总余项是 (-49\)，直接能量是 (490\)，四个分量依次为

\[
 557/2,\quad171/2,\quad171/2,\quad81/2,
 \qquad557/2+171/2+171/2+81/2=490.
\tag{PA21}
\]

## 6. 对 coupled-kernel gate 的实际影响与未证边界

这次闭合了 (4.5) 与共同截断 reflection 的**全局恒等式**，并给出了原坐标上的完整余项算子。没有闭合早先 core 多面体上“固定 (h,\delta\) 的 packetwise 等距 adapter”；那种直接 reflection 本来就不是合法恒等式。

更不能把坐标转换当作范数无损：仅 (d=1\) 一列就有

\[
 \|C_{z,X}e_1\|_2^2=X.
\tag{PA22}
\]

所以 §§9.197–9.198 的形式 exponent saving 不能通过一个未经证明的等距假设转移到 (PA18)。USZNTT 仍是未证明的范数目标；其已有有限恒等式不等于它对原物理占据能量 (\mathfrak E_{\rm occ}\) 的比较定理。

下一项真正的解析工作必须直接处理 (PA18)/(PA20)，或证明从它到既有 WRFE/GDTM/USZNTT 的、带准确权重与范数成本的转移。仍须保留两侧 Möbius/Type 符号及原 Poisson 表示中的 (a=h\delta\)。目前没有新不等式给出缺少的幂次 saving，完整 twisted moment 仍未证明。

有限 helper `physical_mellin_convolution_signed_operator_sides` 从完整除数格计算 (B,F,R\)、原四变量和、乘积和、拉回核及反演后的零核；它拒绝漏掉反射除数的输入。它还测试非零 Mellin 权模型 (d^z\) 和密度改变下总核不变。`MellinProductPacket` 故意不含伪造的单个 (h\) 标签。脚本不声称验证连续积分或 (PA15) 的分析证明，更不声称证明算子范数界。
