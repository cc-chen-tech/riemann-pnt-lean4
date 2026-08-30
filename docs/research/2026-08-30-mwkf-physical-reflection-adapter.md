# 从 (4.5) 到 reflection：共同截断、正确坐标与完整 signed operator

白话结论：可以把原 Poisson 主和完整地接回 reflection，但必须先恢复整数格，保留整个 Mellin 参数，并把四个 reflection 项放在同一个截断里。原 mollifier 系数与它的除数卷积不是同一个向量；原 AFE 对角与零核补回的对角也不是同一个对象。这些区别不能靠给 packet 改名消除。

本节修正主研究笔记 §§9.194–9.198 的三处过强表述，并给出全局恒等式的 adapter。§§7–9 进一步证明物理归一化的卷积/逆只需亚幂次范数成本，并排除不保留系数结构的全算子目标。没有证明 coupled-kernel gate，也没有证明新的 \(T^2\) saving。数值/有限测试只检验下面的有限代数，不替代连续分析证明。

## 1. 固定记号和三个不能混同的对象

沿用主笔记的 \(a_N(d)=\mu(d)(1-\log d/\log N)\)、\(N\ge2\)、\(W\in C_c^\infty([1,2])\) 及精确 AFE 权 \(V_t\)。设 \(N\le T^3\)、\(T\ge2\)。

以下 \(\mathcal Q\) 是主笔记 (1.1) 的精确 gamma 版本，而非已将
\(\lambda(Tu)\) 替换为 \(\log(Tu/(2\pi))\) 的任务 A 简写；
该替换的有限矩阵误差在 (PA32) 后单独列出。

原式的三类系数分别是

\[
 a=(a_N(d))_{d\le N},\qquad
 c_d=a_N(d)/\sqrt d,\qquad
 B_{N,z}(x)=\sum_{d\mid x,\ d\le N}a_N(d)d^z.
\tag{PA1}
\]

§9.194 的 Fourier Gram 用的是 \(c_d\)，不是 \(B_{N,0}(d)\)。因此“直接将 \(B=F-R\) 代入该 Gram”是错误的，除非同时转换核。即使在有限模型 \(N=2\)、\(a=(1,-2)\)、\(B(1),B(2)=(1,-1)\) 中，核

\[
 G=\begin{pmatrix}0&3\\3&0\end{pmatrix}
 \quad\Longrightarrow\quad
 a^TGa=-12,\qquad (1,-1)G(1,-1)^T=-6.
\tag{PA2}
\]

同样，原 AFE 对角是 \(me=nd\)，可含 \(d\ne e\)（例如 \(d=1,e=2,m=1,n=2\)）。零核补回的 mollifier 对角是 \(d=e\)。后者补回确实得到一个完整 Fourier Gram，但不能因此宣称它就是原 AFE 对角 (2.10)。

## 2. 从 (4.5) 恢复整数格：必须先重组所有 \(h\)

固定一个有限 dyadic box 和 \(q,r,s,\delta\)，令 \(f(x)\) 为 (4.4) 中去掉 \(e(-hx/s)\) 的完整光滑函数。它延拓为 \(C_c^\infty(\mathbb R)\)。按 (4.3b) 的 Fourier 约定，

\[
 {1\over s}\sum_{h\in\mathbb Z}
 e(-h\delta\bar r/s)\widehat f(h/s)
 =\sum_{n\equiv-\delta\bar r\pmod s}f(n).
\tag{PA3}
\]

这只是带平移/缩放的 Poisson 公式；可对照 [NIST DLMF §1.8(iv)](https://dlmf.nist.gov/1.8.iv)。这里 \(s=1\) 的相位取 1。对整数 \(A>1,H\ge1\)，分部积分和 \(\sum_{h>H}h^{-A}\le H^{1-A}/(A-1)\) 给出显式尾界

\[
 {1\over s}\sum_{|h|>H}|\widehat f(h/s)|
 \le {2s^{A-1}\over(2\pi)^A(A-1)}
 H^{1-A}\|f^{(A)}\|_1.
\tag{PA4}
\]

在有限 box 中，\(\delta\) 也只有有限多个可能值：若 \(x\asymp M\)、\((rx+\delta)/s\asymp K\)，则 \(\delta\in[sK/2-2rM,2sK-rM/2]\)。因此先在每个有限 box 令 \(H\to\infty\) 是合法的。恢复格点后，

\[
 d=qr,\quad e=qs,\quad
 m={nr+\delta\over s},\quad
 x_0=dn,\quad y_0=em,\quad y_0-x_0=q\delta.
\tag{PA5}
\]

反向唯一地由 \(q=(d,e)\)、\(r=d/q,s=e/q\)、\(\delta=(me-nd)/q\) 得到。Poisson 的 \(1/s\) 保留在 (PA3)；恢复格点后外系数是 \(2/(q\sqrt{rs})=2/\sqrt{de}\)，没有额外 Jacobian。

然后才求和 dyadic partition。原整数点上的局部有限 partition-of-unity 与 (2.5a) 的绝对收敛保证无端点误差。**单个固定 \(h\) 的积分变量不是整数，(PA5) 的整数乘积 regrouping 不能逐 \(h\) 使用。** 在 Poisson 表达式中保留 \(h,\delta\) 和 \(h\delta\) 是正确的；将全局重组后的乘积核伪标成某一个原 \(h\) 则不正确。

## 3. 空小尺度必须正则化；零核依赖明确的延拓选择

若直接把所有空小尺度也加入“共同零模”，(9.381) 会产生

\[
 \int_0^\infty V_t(u^2)\,{du\over u}.
\tag{PA6}
\]

由 \(V_t(u^2)=1+O_t(u^{2c})\)、\(0<c<1/4\)，它在 0 对数发散。不能把它称为一个已定义的有限公共权 \(\Omega\)。

固定一次 \(\chi\in C^\infty(\mathbb R)\)，满足 \(0\le\chi\le1\)、\(\chi(u)=0\) 当 \(u\le1/4\)、\(\chi(u)=1\) 当 \(u\ge1/2\)。在 (4.4) 中乘上

\[
 \chi(x)\chi((rx+\delta)/s).
\tag{PA7}
\]

它在所有正整数 zeta 变量上恒为 1，故不改变原 AFE。记相应第一层 Poisson 零项与非零项为 \(Z_\chi,O_\chi^{\ne0}\)，原项为 \(Z,O^{\ne0}\)。逐有限 box 的 (PA3) 给出

\[
 (Z_\chi-Z)+(O_\chi^{\ne0}-O^{\ne0})=0,
 \qquad
 \mathcal R=\mathcal D_{\rm AFE}+Z_\chi+O_\chi^{\ne0}-T\mathcal Q.
\tag{PA8}
\]

差 \(Z_\chi-Z\) 必须保留；没有证明它小。这也说明改变连续延拓可以在零模与非零补集之间移动质量，虽然完整余项不变。使用原式 (4.8) 时，同一账本就是 \(\mathcal R=\mathcal E_{\rm arch}+O^{\ne0}\)，不能另丢 \(\mathcal E_{\rm arch}\)。

现在 (9.380) 所指定的短模数双 completion 零系数可以严格计算。令 \(b=r-s\ne0\)。去掉 Fourier 因子后的 \(f_\chi(x,\delta)\) 是 Schwartz 函数：两个 zeta 变量均远离 0，且 \(V_t\) 在它们的乘积上任意阶衰减。部分 Fourier 变换仍是 Schwartz，故 (9.380) 的 \(h,\delta\) 积分绝对收敛。先对 \(h\) 反演得到 \(s f_\chi(-\delta/b,\delta)\)，再置 \(\delta=-bu\)。相应 \(s\) 与 \(1/s\)、\(|b|\) 与 \(1/|b|\) 恰好抵消，且两个 zeta 变量都等于 \(u\)。于是所选延拓的零核为

\[
 \begin{aligned}
 \Omega_\chi(t)&=2W(t/T)\int_0^\infty
             \chi(u)^2 V_t(u^2)\,{du\over u},\\
 G_{\chi;d,e}&={\mathbf1_{d\ne e}\over\sqrt{de}}
       \int_{\mathbb R}\Omega_\chi(t)(e/d)^{it}\,dt.
 \end{aligned}
\tag{PA9}
\]

因子 2 已包含两个相同 AFE 方向，不能再乘一次 2。这里的“canonical”只能指**固定了此延拓与此 completion 后**的零核，不能指延拓无关的次主常数。恢复离散 completion 时，删除的 \(h=0\)、\(\delta=0\) 轴与其他非零对偶频率都必须进入补集。由 (2.5)，\(\Omega_\chi\) 至多多一个 \(\log(2T)\) 因子。[canonical 零权求值](2026-08-30-mwkf-canonical-zero-weight.md) 的 (ZW12) 进一步给出 \(\Omega_\chi=W(t/T)(\lambda(t)+\kappa_\chi+O_A(t^{-A}))\)，保留了深移线的全部移动 gamma 留数。当 \(W\ge0\)、\(T\) 足够大时，该权非负；补回 mollifier 对角后 Gram 正半定。因此 Selberg 系数的零核负部为 \(O(T\log T\log(2N))\)，但正部的长 Möbius 均方上界及配对非零频补集仍未控制。

## 4. 完整 Mellin reflection 与共同乘积截断

在原绝对收敛直线 \(z=2+i\tau\) 上，对整数 \(X\ge N\) 只保留 \(x,y\le X\)。令

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

包括 \(x=1\) 的空积约定后，对每个复数 \(z\) 都有

\[
 B_{N,z}(x)=F_z(x)-R_{N,z}(x),\qquad
 Dk=x,\ D>N\Longrightarrow kN<x\le X.
\tag{PA11}
\]

严格端点 \(kN<x\) 没有 floor 误差。只有在已限制 \(X\asymp NT^{1/2}\) 的局部范围才可说 \(k\ll T^{1/2}\)，不能把这个长度断言推广到任意全局截断。

定义有限双线性泛函（两侧是同一个 \(z\)，不是共轭 Mellin 参数）

\[
 \mathcal A_X(U,V)=\frac2{2\pi i}\int_\mathbb R W(t/T)
 \int_{(2)}{g_t(z)G_t(z)\over z}
 \sum_{x,y\le X}{U_z(x)V_z(y)\over(xy)^{1/2+z}}
                (y/x)^{it}\,dz\,dt.
\tag{PA12}
\]

有限求和及 Gaussian Mellin 衰减使这里每个有限-\(X\) 项可积。原四变量求和严格等于

\[
 I_X=\mathcal A_X(B,B)
 =\mathcal A_X(F,F)-\mathcal A_X(F,R)
  -\mathcal A_X(R,F)+\mathcal A_X(R,R).
\tag{PA13}
\]

这是整个 \(z\) 家族的 reflection，不是只取 \(z=0\)。\(F_0\) 的 prime-power 稀疏性不能用于其他 \(z\)。四项必须共用同一个 \(X\)；未证明它们在 \(X\to\infty\) 时分别收敛。

为证明组合极限，设 \(A_z=\sum_x|B_{N,z}(x)|x^{-5/2}\)，\(E_z(X)\) 为其 \(x>X\) 尾。因为 \(|a_N(d)|\le1\)，

\[
 A_z\le\zeta(5/2)\sum_{d\le N}d^{-1/2}\ll\sqrt N,
 \quad E_z(X)\ll X^{-3/2}\sum_{d\le N}d\ll N^2X^{-3/2}.
\tag{PA14}
\]

这两个界对所有 \(\tau\) 一致；第二个界用 \(X/d\ge1\) 和 \(\sum_{n>u}n^{-5/2}\ll u^{-3/2}\)。矩形外的双和至多 \(2A_zE_z(X)\)。再由 (2.5b) 在 \(\Re z=2\) 上的 Gaussian 可积 majorant 得到

\[
 \boxed{|I-I_X|\ll_W T^3N^{5/2}X^{-3/2}.}
\tag{PA15}
\]

因此 \(N\le T^3\) 时，\(X\ge T^{7+2A/3}\) 给出 \(O_W(T^{-A})\)。这是全局 adapter 的充分截断，不是最优 core 长度。由 (4.8)、(PA13)–(PA15)，

\[
 \boxed{\mathcal E_{\rm arch}+\sum_{q,R,S,K,M}O^{\ne0}_{q;R,S,K,M}
 =\lim_{X\to\infty}\{
 \mathcal A_X(F,F)-\mathcal A_X(F,R)-\mathcal A_X(R,F)
 +\mathcal A_X(R,R)-T\mathcal Q\}.}
\tag{PA16}
\]

左边按 (PA3) 的 box-first Poisson 顺序，右边按共同-\(X\) 顺序。没有逐频率 reflection，也没有换序后将四个无穷项分别估计的授权。

## 5. 在正确的共同坐标上构造 signed operator

令 \(C_{z,X}(x,d)=\mathbf1_{d\mid x}d^z\)，\(d\le N,x\le X\)；令 \(K_{z,t}(x,y)=(xy)^{-1/2-z}(y/x)^{it}\)。全 AFE 核（已包含 dyadic partition 的总和）为

\[
 H_X={2\over2\pi i}\int W(t/T)\int_{(2)}
      {g_t(z)G_t(z)\over z}\,C_{z,X}^{T}K_{z,t}C_{z,X}\,dz\,dt,
 \quad I_X=a^TH_Xa.
\tag{PA17}
\]

设 \(L\) 是满足 \(a^TLa=T\mathcal Q\) 的原 LCM 主项核。\(H_X\) 的各个矩阵元收敛（\(N\) 固定有限，或用同样绝对值尾界），记 \(H=\lim_XH_X\)。在原 \(d,e\) 坐标上定义

\[
 R=H-L,\qquad J_\chi=H-L-G_\chi,\qquad
 R=G_\chi+J_\chi,\qquad \mathcal R=a^TRa.
\tag{PA18}
\]

这是从完整物理 AFE 核计算出的补集，不是任意供应的测试矩阵。\(J_\chi\) 保留所有非零频率、轴修正、延拓补偿、主项减法与原 AFE 对角账本；除非另外证明这些修正已分别归并，不能把它简称为“只有非零 determinant 的谱核”。

若一定要在 \(B\) 坐标上写 canonical Gram，设有限 Möbius 反演矩阵 \(U(d,x)=\mathbf1_{x\mid d}\mu(d/x)\)，并令 \(L_z=D_{-z}P_NU\)。则

\[
 a=L_zB_{N,z},\qquad
 a^TG_\chi a=B_{N,z}^T L_z^T G_\chi L_z B_{N,z}.
\tag{PA19}
\]

在 Hermitian 能量形式中应相应使用共轭转置 \(L_z^*\)，不能把 Mellin 双线性转置与 Hilbert 伴随混用。最安全的统一空间是 (PA18) 的原 mollifier 坐标。

给定原坐标上的概率密度 \(p,q\)，只中心化 \(J_\chi\)：

\[
 C=(I-\mathbf1p^T)J_\chi(I-q\mathbf1^T),\quad
 R_{\rm res}=G_\chi+J_\chi-C,
 \quad R=R_{\rm res}+C,\quad p^TC=Cq=0.
\tag{PA20}
\]

随后只做一次全局 \(TT^*\)，保留 \(R_{\rm res}R_{\rm res}^*,R_{\rm res}C^*,CR_{\rm res}^*,CC^*\) 四项（不能将这里的 \(R_{\rm res}\) 换成总核 \(R\)）。改变 \(\chi\) 或密度只改变分配，不改变总核 \(R\)。一个有限有理 fixture 的总余项是 \(-49\)，直接能量是 \(490\)，四个分量依次为

\[
 557/2,\quad171/2,\quad171/2,\quad81/2,
 \qquad557/2+171/2+171/2+81/2=490.
\tag{PA21}
\]

## 6. 对 coupled-kernel gate 的实际影响与未证边界

这次闭合了 (4.5) 与共同截断 reflection 的**全局恒等式**，并给出了原坐标上的完整余项算子。没有闭合早先 core 多面体上“固定 \(h,\delta\) 的 packetwise 等距 adapter”；那种直接 reflection 本来就不是合法恒等式。

未经归一化不能把坐标转换当作等距：仅 \(d=1\) 一列就有

\[
 \|C_{z,X}e_1\|_2^2=X.
\tag{PA22}
\]

但 (PA22) 本身并不是物理范数下的幂次障碍：下面 §7 补齐正确权重后，得到实际的双向亚幂次比较。§§9.197–9.198 的形式 exponent saving 仍不能通过一个等距假设转移到 (PA18)；USZNTT 的有限恒等式也不等于它对原物理占据能量 \(\mathfrak E_{\rm occ}\) 的比较定理。

下一项真正的解析工作必须直接处理 (PA18)/(PA20)，或证明从它到既有 WRFE/GDTM/USZNTT 的、带准确权重与范数成本的转移。§7 的系数范数界只解决其中的除数卷积部分，尚不处理所有 packet 的占据能量。仍须保留两侧 Möbius/Type 符号及原 Poisson 表示中的 \(a=h\delta\)。目前没有新不等式给出缺少的幂次 saving，完整 twisted moment 仍未证明。

有限 helper `physical_mellin_convolution_signed_operator_sides` 从完整除数格计算 \(B,F,R\)、原四变量和、乘积和、拉回核及反演后的零核；它拒绝漏掉反射除数的输入。它还测试非零 Mellin 权模型 \(d^z\) 和密度改变下总核不变。`MellinProductPacket` 故意不含伪造的单个 \(h\) 标签。脚本不声称验证连续积分或 (PA15) 的分析证明，更不声称证明算子范数界。

## 7. 物理归一化消除了除数坐标转移的幂次成本

这是一个真正的不等式，不再只是有限展开恒等式。令 \(X\ge N\) 为整数，
\(E_N:\mathbb C^N\to\mathbb C^X\) 是补零嵌入；以下也适用于 Hilbert 空间值系数。
设 \(z=\sigma+i\tau,\ \sigma\ge0\)，并定义

\[
 (S_{z,X}v)(x)=\sum_{d\mid x}v(d)(x/d)^{-1/2-z},
 \qquad
 (U_{z,X}v)(x)=\sum_{d\mid x}\mu(x/d)v(d)(x/d)^{-1/2-z}.
\tag{PA23}
\]

它们与物理权重的精确关系是

\[
 b_z(x):=x^{-1/2-z}B_{N,z}(x)=S_{z,X}E_Nc(x),
 \qquad c_d=a_N(d)/\sqrt d,\qquad
 U_{z,X}S_{z,X}=S_{z,X}U_{z,X}=I_X.
\tag{PA24}
\]

**逆映射证明。** 合成后，固定 \(d\mid x\) 的系数为
\((x/d)^{-1/2-z}\sum_{n\mid x/d}\mu(n)\)，只有 \(x=d\) 时为 1。
全部除数仍在 \([1,X]\)，故没有截断边界余项。

令 \(D_X=\max_{n\le X}\tau(n)\)、\(H_X=\sum_{n\le X}1/n\) 和
\(\mathcal B_X=D_XH_X\)。对每个 \(v\)，直接在除数集合上 Cauchy 得到

\[
 \begin{aligned}
 \|S_{z,X}v\|_2^2
 &\le\sum_{x\le X}\tau(x)
       \sum_{dn=x}\|v(d)\|^2n^{-1-2\sigma}\\
 &\le D_X\sum_{d\le X}\|v(d)\|^2
       \sum_{n\le X/d}n^{-1}
 \le\mathcal B_X\|v\|_2^2.
 \end{aligned}
\tag{PA25}
\]

对 \(U_{z,X}\) 使用 \(|\mu|\le1\) 给出相同证明，因此

\[
 \boxed{\mathcal B_X^{-1}\|v\|_2^2
       \le\|S_{z,X}v\|_2^2
       \le\mathcal B_X\|v\|_2^2,\quad
       \|S_{z,X}^{\pm1}\|_{2\to2}\le\sqrt{\mathcal B_X}.}
\tag{PA26}
\]

这对 \(\tau\) 一致。在虚轴上还有精确的酉对角共轭：
\(S_{i\tau,X}=D_{-i\tau}S_{0,X}D_{i\tau}\)。
初等地，对任意 \(\eta>0\)，大素数 \(p\ge2^{1/\eta}\) 满足
\(\alpha+1\le2^\alpha\le p^{\eta\alpha}\)；剩余有限小素数的
\(\sup_{\alpha\ge0}(\alpha+1)p^{-\eta\alpha}\) 有限。
逐素因子相乘即得 \(\tau(n)\ll_\eta n^\eta\)。
再用 \(H_X\le1+\log X\)，有 \(\mathcal B_X\ll_\eta X^\eta\)
（调整 \(\eta\)）。若 \(X\le T^A\) 且 \(A\) 固定，
任意固定次这样的范数转移都只花 \(O_{\varepsilon,A}(T^\varepsilon)\)。
(PA15) 可以选择一个固定幂次的 \(X\)；但此结论不提供
\(X\to\infty\) 时在 \(\sigma=0\) 的一致算子界，也不授权移动 Mellin 线。

原直线 \(\sigma=2\) 更好。令
\((V_nv)(x)=\mathbf1_{n\mid x}v(x/n)\)，则 \(\|V_n\|\le1\)，
\(S_z=\sum_{n\le X}n^{-1/2-z}V_n\)，
\(U_z=\sum_{n\le X}\mu(n)n^{-1/2-z}V_n\)。
所以对 \(\sigma>1/2\)

\[
 \|S_{z,X}^{\pm1}\|\le\sum_{n\le X}n^{-1/2-\sigma}
 \le\zeta(1/2+\sigma).
\tag{PA27}
\]

特别是 \(\sigma=2\) 的成本独立于 \(X,N,\tau\)。
这里仅在已重组的系数映射上用了三角不等式，没有对物理
\(h,\delta\)、dyadic 或 Type 主和取绝对值。

### 精确 LCM Gram 与所有截断端点

在原系数坐标使用范数 \(\|a\|_{1/x}^2=\sum_{x\le X}|a_x|^2/x\)。
对完全乘性权 \(w(n)=n^{-z}\)，令
\(\mathscr S_wa(x)=\sum_{d\mid x}a_dw(x/d)\)。
固定 \(d,e\le X\)、\(\ell=[d,e]\)，其 Gram 为

\[
 \Gamma_w(d,e)
 =\sum_{\substack{x\le X\\d,e\mid x}}
       {\overline{w(x/d)}w(x/e)\over x}
 ={\overline{w(\ell/d)}w(\ell/e)\over\ell}
       \sum_{k\le X/\ell}{|w(k)|^2\over k}.
\tag{PA28}
\]

\(\ell>X\) 时和为空；\(\ell=X\) 时恰有 \(k=1\)，不能丢掉该端点。
特别是 \(\Gamma_1(d,e)=H_{\lfloor X/[d,e]\rfloor}/[d,e]\)，约定 \(H_0=0\)。
普通 \(\ell^2\) 上的 \(S_z^*S_z\) 矩阵是
\(\sqrt{de}\,\Gamma_w(d,e)\)，不能漏掉这两个平方根。

## 8. 统一 signed 核的转移，以及它没有证明的事情

先把原 \(a\) 坐标核改到 \(c\) 坐标：
\(R_c=D_{\sqrt d}RD_{\sqrt d}\)，同理定义 \(G_{\chi,c},J_{\chi,c}\)。
在固定 \(z\) 和同一个有限 \(X\) 上，可把任何 Hermitian 核 \(K_c\)
推到整个乘积空间：

\[
 \widetilde K_z
 =U_{z,X}^*E_NK_cE_N^*U_{z,X},
 \quad
 (S_zE_Nc)^*\widetilde K_z(S_zE_Nc)=c^*K_cc,
 \quad \|\widetilde K_z\|\le\mathcal B_X\|K_c\|.
\tag{PA29}
\]

于是 \(R_c=G_{\chi,c}+J_{\chi,c}\) 的三项都使用同一个变换，
包括 canonical zero Gram。对乘积空间 Hermitian 核 \(K\) 的拉回，
\(\|E_N^*S_z^*KS_zE_N\|\le\mathcal B_X\|K\|\)。
更精确地，把 \(K\) 的二次型压缩到物理值域
\(\mathcal V_z=S_zE_N\mathbb C^N\)，该压缩范数与拉回范数
双向相差至多 \(\mathcal B_X\)，由 (PA26) 和 Rayleigh 商即得。
这不是任意 \(\mathbb C^X\) 向量与 \(\mathbb C^N\) 向量的等价。

对 (PA12) 的复双线性 Mellin integrand，必须把 (PA29) 的星号
改为转置，并使用同一 \(z\) 的两个因子；相应算子范数上界成本不变。
不能为了使用 Hermitian Gram 把其中一个 \(z\) 改成 \(\bar z\)。
也不能把含不同 \(z\) 的整个积分当作一个固定 \(S_z\) 的共轭。

若已经合法地得到系数分解 \(v=\sum_\alpha v_\alpha\)，其中符号包含在
\(v_\alpha\) 内，则

\[
 \|S_zv\|^2
 =\sum_{\alpha,\beta}\langle S_zv_\alpha,S_zv_\beta\rangle
 \le\mathcal B_X\Big\|\sum_\alpha v_\alpha\Big\|^2.
\tag{PA30}
\]

右边不是 \(\mathcal B_X\sum_\alpha\|v_\alpha\|^2\)，更不是逐块
绝对值之和。两侧不同 \(z\) 或不同边界映射的共同有限核也满足
\(\|A^*KB\|\le\|A\|\|K\|\|B\|\)，取 \(TT^*\) 只将该转移成本平方。
在固定幂次截断下仍只损失 \(T^\varepsilon\)，但没有产生
\(T^{-2\eta_{\rm imb}}\) 的 saving。

必须保留的限制有四个：

1. 同一 \(z,X\) 的 signed 块先相加再转移，不能额外构造一个块标签
   direct-sum 范数替代原范数；变化的 Mellin 参数仍在原 signed 积分内。
2. (PA24) 只识别系数空间。早先 WRFE/GDTM/USZNTT 的占据范数、
   斜率和模数关联仍须逐项比较；本节不自动给出那个比较定理。
3. \(B_{N,z}=F_z-R_{N,z}\) 保持全 \(z\) 和共同截断。
   Type 分解必须来自精确算术恒等式，不因标签叫 Type I/II 就成立。
4. 从 (4.5) 返回格点仍须先重组 \(h\)。本节不恢复“固定 \(h\) 的
   reflection adapter”，也不删去原表示中 \(a=h\delta\) 的因子关系。

## 9. 为什么不能把目标升级成任意系数的全物理算子界

下面是对错误升级的反例，不是对实际 Selberg–Möbius 目标的反例。
先证明主项在正确系数范数下确实小。令
\(A_N(d,e)=(d,e)/\sqrt{de}\)，使用必需的 totient 对角化：

\[
 \begin{aligned}
 c^*A_Nc
 &=\sum_{r\le N}\varphi(r)
       \left|\sum_{\substack{d\le N\\r\mid d}}{c_d\over\sqrt d}\right|^2\\
 &=\sum_{r\le N}{\varphi(r)\over r}
       \left|\sum_{n\le N/r}{c_{rn}\over\sqrt n}\right|^2
 \le H_N\sum_{d\le N}\tau(d)|c_d|^2
 \le\mathcal B_N\|c\|^2.
 \end{aligned}
\tag{PA31}
\]

这里先在内和 Cauchy，再用 \(\varphi(r)/r\le1\)，无渐近误差。
为保留主笔记 (1.1) 的精确 gamma 归一化，令
\(\omega_W=\int_1^2W(u)\,du\)、
\(\alpha_W(T)=\int_1^2W(u)(\lambda(Tu)+2\gamma)\,du\)。
于是
\(L_c(d,e)=T A_N(d,e)
[\alpha_W(T)-\omega_W\log(de/(d,e)^2)]\)。
因为 \(0\le\log(de/(d,e)^2)\le2\log N\)，精确地有

\[
 \|L_c\|\le T\bigl(|\alpha_W(T)|+2|\omega_W|\log N\bigr)\mathcal B_N
 \ll_{\varepsilon,W}T^{1+\varepsilon}\quad(N\le T^3).
\tag{PA32}
\]

证明对任意两个向量取绝对值，用非负矩阵 \(A_N\) 支配矩阵元；
并未宣称含对数的 \(L_c\) 正定。主笔记 (1.3) 给出
\(\alpha_W(T)=\omega_W\log(T/(2\pi))
+\int W(u)(\log u+2\gamma)\,du+O_W(T^{-2})\)。
故替换 gamma 主项的矩阵算子误差至多
\(O_W(T^{-1}\mathcal B_N)\)；在精确恒等式中仍使用未替换的 \(L_c\)。
若 \(\omega_W\ne0\)，可定义
\(C_W=2\gamma+\omega_W^{-1}\int W(u)\log u\,du\) 得到任务 A 的简写，
但不能在精确的 (PA32) 中省略上述误差或权重质量。

现在只为反例取固定 \(W\ge0\)、\(W\not\equiv0\)，并令

\[
 \mathfrak H_T[c]
 =\int W(t/T)|\zeta(1/2+it)|^2
           \left|\sum_{d\le N}c_dd^{-it}\right|^2dt,
 \qquad A_T=\int W(t/T)|\zeta(1/2+it)|^2dt.
\tag{PA33}
\]

经典二次矩公式给出 \(A_T\asymp_W T\log T\)；所需输入可查
[Ivić–Zhai, arXiv:1502.00406v2](https://arxiv.org/pdf/1502.00406v2)
的 (1.2) 与 Lemma 1，再对固定光滑 \(W\) 分部积分。
下面的聚相推理是本节的直接推导，不是引用该论文的新结论。

把 \([T,2T]\) 分成 \(J=\lceil T\rceil\) 个长度至多 1 的半开区间
（最后一个含右端点）。非负测度总质量为 \(A_T\)，某区间
\(I\) 的质量至少 \(A_T/J\)。取它的中点 \(t_0\) 以及
\(\mathcal D=\{\lfloor N/2\rfloor+1,\ldots,N\}\)、\(M=|\mathcal D|\)，令
\(c_d=M^{-1/2}d^{it_0}\mathbf1_{\mathcal D}(d)\)。
它的范数为 1。对 \(t\in I\)，乘一个单位相位后，
和式每项的角度至多 \((\log2)/2\)，所以

\[
 \mathfrak H_T[c]\ge
 \cos^2((\log2)/2)\,M\,{A_T\over\lceil T\rceil}
 \gg_W N\log T.
\tag{PA34}
\]

这是完整物理矩的 Hermitian 二次型；与原实系数形式一致。
若坚持只允许实系数，把此 \(c=u+iv\) 分开。
\(\mathfrak H_T[u]+\mathfrak H_T[v]
=(\mathfrak H_T[c]+\mathfrak H_T[\bar c])/2
\ge\mathfrak H_T[c]/2\)，且 \(\|u\|^2+\|v\|^2=1\)。
故实系数空间也存在同阶 Rayleigh 商。

结合 (PA32)，在 \(N=\lfloor T^3\rfloor\) 时，
完整余项的全系数算子范数满足

\[
 \|\mathfrak H_T-L_c\|_{2\to2}\gg_W T^3\log T
 \quad(T\ \hbox{充分大}).
\tag{PA35}
\]

所以 \(\|\mathfrak H_T-L_c\|\ll_\varepsilon T^{1+\varepsilon}\)
对任意系数的版本不成立。聚相向量不是
\(c_d=\mu(d)(1-\log d/\log N)/\sqrt d\)，也未证明属于此前受限
双 Möbius/Type 系数类。本反例**不否定**该受限目标，不评价单独中心化
\(C\) 的范数，更不允许忽略与它相加的 resonant 和混合项。
它排除的是把整个 gate 替换为无系数结构的全矩阵范数定理。

### 可直接形式化的有限命题与验证范围

(PA24) 的双边逆恒等式、(PA25)–(PA26) 的有限范数界、
(PA28) 的精确 LCM Gram、(PA30) 的 signed 重组和 (PA31) 的
totient 平方和都是任意整数截断下的有限命题，可分别形式化，
不需要假设 Möbius 相关消去。复数版本的共轭位置已在公式中指定。

脚本 `mwkf_normalized_mellin_transfer.py` 使用有理完全乘性
收缩权测试这些命题的有限模型；\(w=1\) 对应 \(z=0\)，
\(w(n)=1/n\) 对应 \(z=1\)，完全乘性符号权检测反演的权重是否遗漏。
它不声称有理 fixture 覆盖全部复 Mellin 参数；一般情形由上述证明处理。
一个 signed Type fixture 的交叉 Gram 是 \(-11/2\)，全 signed 能量
为 \(581/20\)，而逐块绝对值给出 \(1021/20\)，明确区分两者。
LCM 的空和/端点、零向量、\(X=1\)、不完整/非乘性权和越界输入
均有独立测试。没有 Lean 源码变更，也没有把测试通过当作解析 gate 证明。

至此，**除数系数坐标转移已经有初等不等式；受限 coupled signed
估计仍未证明**。后续应在这个正确归一化下保留两重 Möbius、
\(h\delta\) 因子化和共同零/非零补集，攻击剩余参数楔形；
不能靠忽略这些限制而改用 (PA35) 已排除的任意系数目标。
