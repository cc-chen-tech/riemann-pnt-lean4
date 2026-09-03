# 高高度 \(14/17\) 的共同有限输出：投影、端点、零模与全谱残项的一次重组

## 结论边界

本文首先构造一个共同的有限 Hermitian 输出 contract：它同时为实际
零点自适应系数、唯一共同投影、quotient 两端点、Poisson 零模与轴、
Maaß/holomorphic/Eisenstein 全谱、exact valuation-one shell、连续谱
PP/PQ/QP/QQ 四行及局部余项预留坐标。CF0A、CF1 与 CF3 的有限
恒等式在本文自含证明；尚未从公开原 atom 逐项验证的全谱/physical
adapter 必须留在 native complement，不能因写入 contract 就算关闭。
所有操作先在有限截断上进行；没有先对 level、box、谱型或端点分别取
绝对值。

此外本文证明若干独立 supplier：exact zero-alias Fourier isometry、
cross-prime contraction、短逆边实际 Riesz 平方能量、affine
physical-shift 导数/尾引理，以及 actual-Riesz 四阶矩的共同 Hilbert
列扩张；CF19B 还把经典 Andersen--Kıral level reciprocity 的三项
prime completion 无损张量化到互素平方自由 levels，并证明该
reciprocity 本身不含第二份 shell half-root；CF19Z--CF19Z6 则在
不交换无限谱和的前提下，直接给出 odd--Hecke 零列的若干 exact-shell
辅助几何绝对界，并用一次有限 level Möbius 容斥把该辅助壳精确识别为
包含 oldforms 与连续谱的整体 regulated full-spectrum trace。CF19Z7
进一步给出一个反向审计修正：这个 exact-shell trace 不能再与已经包含
shell local coefficient 的 CF19.32c 串联，否则单素数局部和精确为零；
正确的物理候选必须降到 level \(B\)，相应绝对界只有 \(A^{-2+\varepsilon}\)
而不是重复壳密度所得的 \(A^{-3+\varepsilon}\)。CF19Z8 再在共同有限
谱 regulator 内证明这个 lower-level candidate 逐 datum 精确等于
unramified oldclass multiplier；CF19Z9 再精确计算 Steinberg rank-one
行、证明导子指数至少二的正 index 消失，并在有限 regulator 内把全部
导子模式平方合计为 \(O(A^{-1})\)。CF19Z10 再把这些正交模式组成
一个算子范数 \(O(A^{-1/2})\) 的对角谱乘子，证明在共同 ambient
Bessel measure 已经建立时一次标量大筛便足够，不会产生
\(2^{\omega(A)}\)。CF19Z11 又把 actual zero--zero 行中不含额外
quotient mask 的 \(A\)-valuation-one 壳精确写成使用同一 Bessel test
的有限 full-level trace 差，并在共同 regulator 内把它逐 newdatum
重组为 CF19Z10 的乘子；这关闭了该裸壳的 Maaß/holomorphic/Eisenstein
归一化，而没有关闭其余 quotient masks、非负 Bessel majorant、
共同解除 regulator 或标量大筛本身。
反向审计同时撤回一个
错误推断：这些 norm-one/isometry supplier 本身不产生所需
\(P^{-1/12}\) centered contraction。

本文不证明这个共同输出的所需上界。最后剩下的命题准确等于 CF9.1，
而不是一个较窄的 balanced fixed-level core。因而本文不证明高高度或
全高度 \(14/17\) 零点区域，也不进入 Lean。

## CF0. 冻结来源与符号纪律

使用以下已审计对象，不沿用错误的 direct cusp identity (4.845ap)：

1. 原物理 QCT/MWKF atom 来自定义源
   `49cfacd70c60372757280177c7b63fd4f7760817`；其唯一外权为
   \(2T/(q_0RS)\)。
2. squarefree lift 使用主笔记 §412--416 的
   \[
   S(Ak,-n;As)=c_A(n)S(k,-n\bar A;s),
   \qquad (A,s)=1, A\ \text{squarefree}.
   \tag{CF0.1}
   \]
3. 共同 TT* 的公开来源为已经进入本 PR base 的提交
   `0c9f90f969f6e248a44b7bb26776813939af2c39`。本稿所用的一次有限
   投影修正不再引用不可达的研究提交；它在 CF0A 中从定义重证。
4. exact-shell 的全部局部公式及范数也不再把本地长母稿当作来源；
   CF7A 从旧空间 Gram 定义开始重证所需结论。后文括号中的
   (344)、(386)--(387)、(446)、(465)、(472)、(475)、(477)、(488)
   仅是推导过程中的历史交叉索引：相应公式若未在本文显示写出，便只
   属于待验证的 physical adapter，不作为本文已证结论的前提。

因此 fresh checkout 的规范来源只有上述两个已进入 base 的提交和本
文件本身。早期本地研究 SHA 不构成可复核证明来源，也不用于
`source gate`。特别地，完整 height reassembly、实际共同 Mellin 列与
原核到 CF19.D 的坐标迁移在本文中保持 open contract。

有两个不能混合的 Möbius 记号约定。

- native 行直接携带
  \(b^\sharp_{q_0r}\overline{b^\sharp_{q_0s}}\)，不得再乘一个
  “原 mollifier” Möbius 符号；
- 在平方自由 canonical 子域使用本稿的 Möbius 重写时，先定义
  \(B(d)=\mu(d)b^\sharp_d\)，再且只再出现一次
  \(\mu(r)\mu(s)B(q_0r)\overline{B(q_0s)}\)。

下面 CF3.2 中的 \(\mu(A)\mu(B)\) 是 quotient 展开的符号，
不是第三份 mollifier 符号。exact shell 内的
\(\mu(A)/c_A(h\delta)\) 只进入 CF7.5 的归一化局部核一次，也不再
作为一个独立 level 系数复制。

### CF0A. 一次有限投影修正的自含构造

固定有限可见整数上界 \(J\)、\(N>1\)、窗口 \(Xy<n\le Xy+H\)，并
设 ambient coefficient support 至少包含 \([1,2J]\)，原有限系数
\(b\) 满足 \(\sum_db_d/d=0\)。令
\(B_i\) 是同一加权 \(L^2\) 空间中的有限低响应列。先按固定原顺序
删去零列及落在前列 span 中的列，得到同一低响应空间的线性无关
基底；这是有限基约简，不改变正交投影 \(\Pi\)。令 \(G\) 是该基底的
Gram 矩阵，即 \(G_{ij}=\langle B_i,B_j\rangle\)，并令
\(v_i=\langle B_i,F_b\rangle\)（内积在第二变量线性）。则 \(G\) 正定，
\(z=G^{-1}v\) 是原输出 \(F_b\) 在这个固定基底中的唯一投影系数；
空表时下列和均为空。每个保留的 \(B_i\) 连同产生它的 \(u_i\) 一起
保留。任选固定 cutoff \(\chi\)，使它在全部可见窗口上为一，
并对 \(1\le n\le J\) 置（其余 \(D_n=0\)）
\[
 D_n={\chi(n/X)\over H}\sum_i z_i u_i(n/X),\qquad
 A_i(y)={1\over H}\sum_{Xy<n\le Xy+H}\chi(n/X)u_i(n/X).
                                                               \tag{CF0A.1}
\]
于是有限换序精确给
\[
             \sum_{Xy<n\le Xy+H}D_n=\sum_i z_iA_i(y).  \tag{CF0A.2}
\]
先在 \(d\le J\) 作一次有限 Möbius 反演：
\[
 e_d^{(0)}={1\over\log N}\sum_{a\mid d}\mu(d/a)D_a,
 \qquad s_J=\sum_{d\le J}{e_d^{(0)}\over d},\qquad
 c_J=\sum_{J<d\le2J}{1\over d}.
\]
因 \(J\ge1\)，有 \(c_J>0\)。定义
\[
 e_d=\begin{cases}
 e_d^{(0)},&d\le J,\\
 -s_J/c_J,&J<d\le2J,\\
 0,&d>2J,
 \end{cases}
 \qquad b_d^\sharp=b_d-e_d.                             \tag{CF0A.3}
\]
则直接有
\[
 \sum_d{e_d\over d}=0,
 \qquad
 (\log N)\sum_{d\mid n}e_d=D_n\quad(1\le n\le J).     \tag{CF0A.4}
\]
第二式包含 \(n=1\)：展开后内和是
\(\sum_{r\mid n/a}\mu(r)={\bf1}_{a=n}\)，而补偿壳严格大于 \(J\)，
不会整除可见 \(n\)。因此 \(b^\sharp\) 仍有 reciprocal mean zero，且
若
\[
 F_\sharp(y)=(\log N)\sum_{Xy<n\le Xy+H}
                              \sum_{d\mid n}b_d^\sharp,
 \qquad \delta_i=A_i-B_i,
\]
则
\[
 F_\sharp=F_b-\sum_i z_iA_i,
 \qquad
 (I-\Pi)F_b=F_\sharp+\sum_i z_i\delta_i.               \tag{CF0A.5}
\]
这证明后文所用的唯一共同投影恒等式。它不证明
\(A_i-B_i\) 的解析小量估计，也不证明 \(b^\sharp\) 的共同 Mellin
分解；这两项必须在应用 CF8--CF9 时另外供应。

## CF1. 原共同投影等于一个增广有限 Gram 形式

固定实际零点 \(\rho\)、其有限低响应表、\(P\)、\(X\)、\(H\)、
\(I_P\) 与权 \(\omega_K\)。在
\(\mathcal H=L^2(I_P,\omega_K(y)\,dy)\) 中置
\[
 w_n(y)={\bf1}_{Xy<n\le Xy+H}.
\]
所有可见 \(n\) 构成有限集合。令
\[
 c_b(n)=(\log N)\sum_{d\mid n}b_d,
 \qquad
 c_\sharp(n)=(\log N)\sum_{d\mid n}b^\sharp_d.
 \tag{CF1.1}
\]
采用 CF0A 的同一 \(z=G^{-1}v\)、离散低响应 \(A_i\) 与连续低响应
\(B_i\)。记
\[
 \delta_i=A_i-B_i,
 \qquad
 F_\sharp=\sum_n c_\sharp(n)w_n,
 \qquad
 \Delta_z=\sum_i z_i\delta_i.
 \tag{CF1.2}
\]
CF0A.5 逐点给出精确等式
\[
             (I-\Pi_P)F_b=F_\sharp+\Delta_z.             \tag{CF1.3}
\]

令指标集合为可见整数与有限低表的不交并，并定义
\[
 \mathbb K=
 \begin{pmatrix}
  (\langle w_n,w_m\rangle)_{n,m}&
  (\langle w_n,\delta_j\rangle)_{n,j}\\
  (\langle\delta_i,w_m\rangle)_{i,m}&
  (\langle\delta_i,\delta_j\rangle)_{i,j}
 \end{pmatrix},
 \qquad a=(c_\sharp(n))_n\oplus(z_i)_i .                \tag{CF1.4}
\]
内积在第二变量线性。直接展开 (CF1.3) 得
\[
 \boxed{\quad
 \mathcal E_{\rho,P,\mathcal L}
       =X\,a^*\mathbb K a .
 \quad}                                                   \tag{CF1.5}
\]
这是正半定的一个 Gram 形式。其左上块是带全部物理端点的短移位核；
交叉块与右下块是**同一个**投影修正的离散化误差。它们不是另一个
投影，也不能在每个 QCT box 中重新计算。

证明只用了有限和的线性与 Gram 展开。特别地，若直接消去
\(b^\sharp\)，(CF1.5) 退回 Schur complement
\(K-q^*G^{-1}q\)；反之，(CF1.5) 是把这个 dense correction 送入
一次有限系数修正后的精确增广形式，不遗漏长距离 cross terms。
\(\Delta_z\) 的解析控制不是 (CF1.5) 的前提，也未由 CF0A 证明。
CF5A 还从 prime-power Ramanujan 和的二维离散差分构造同一个
quotient-zero divisor 核，使 nonaxis、两条 axis 与 origin 共享一套
有限系数；这关闭的是有限重组，不是其 signed analytic 上界。

## CF2. 物理层只展开左上短移位块，外权只出现一次

CT/AFE 把 (CF1.5) 的左上块送到临界线 moment；它给的是上界传输，
不是把输出 Gram 与一个谱和宣称相等。对每个固定高度壳 \(T\)、
原 smooth partition、AFE 方向、符号、\(q_0,R,S,H_1,H_2\) 与
原有限整数支撑，物理 atom 的输入系数仍是同一个
\[
       b^\sharp_{q_0r}\overline{b^\sharp_{q_0s}}.        \tag{CF2.1}
\]
在采用 CF0 的平方自由 Möbius 约定时，(CF2.1) 只是记号重写，
不是更换系数。

每个 atom 的字面标量为
\[
                 \frac{2T}{q_0RS}.                       \tag{CF2.2}
\]
本文把 quotient Poisson 的 Jacobian \(R\) 定义在 native trace 外。
故任何谱估计的物理恢复顺序必须是
\[
 \frac{2T}{q_0RS}\ \times R\ \times
       (\text{frequency sum})\ \times(\text{one native trace}).
 \tag{CF2.3}
\]
不能再从 Blomer--Milićević 的 \(C^{-1/2}\) convention 引入一个
\(\sqrt{AS}\)：在 CF2.3 的 normalized trace 定义中，该量已经与
test 的 \((AS)^{-1/2}\) 配对。把此 normalized trace 与公开原 atom
逐项相等仍属于 CF19.D 的 physical adapter，而不是这里新增的估计。

## CF3. quotient 两端点必须先组成同一个四行列

在 \(r,s>1\)、\((r,s)=1\) 与平方自由 \(q_0\) 的有限行，定义
\[
 \gamma_A={\bf1}_{(A,q_0)=1},\qquad
 \gamma_B={\bf1}_{(B,q_0)=1}.
\]
对任意尚未拆开的物理权 \(\Phi\)，把 quotient 两端点的有限
inclusion--exclusion 定义为
\[
 \mathcal U_{A,B}[\Phi]
 =\mathcal B_{A,B}[\Phi]
  -\gamma_A\mathcal E^L_{A,B}[\Phi]
  -\gamma_B\mathcal E^R_{A,B}[\Phi]
  +\gamma_A\gamma_B\mathcal E^{LR}_{A,B}[\Phi].         \tag{CF3.1}
\]
完整 expanded-expanded sector 是
\[
 \sum_{(A,B)=1}\mu(A)\mu(B)\mathcal U_{A,B}[\Phi].      \tag{CF3.2}
\]
单位入口 \(r=1\) 或 \(s=1\) 另作同一 master row 的 unit tags，
不塞入 CF3.1 的 expanded--expanded 行。

固定 \(r,s\) 把所有 divisor labels 求完时，CF3.1 的前三行各自为零，
最后一行恢复原系数。这证明 CF3.1 不是 contraction；它是端点选择器。
所以 joint Poisson、Kuznetsov 或 reciprocity 必须作用于
\(\mathcal U_{A,B}\) 整体。只估 bulk 后称端点较小会删除原和本身。

## CF4. 非零 quotient frequency 的全谱共同列

本节固定**待核对的全谱 adapter contract**，不把不可达母稿当作
证明。对 \(k\ne0\)，先使用 corrected lift (CF0.1) 与 exact-shell
resummation。固定所有局部 Hecke 截断 \(\boldsymbol J\)，且
\(J_p\ge(a_p+b_p)/2\)。对 Maaß 两 parity、holomorphic 与
Eisenstein 分别采用其真实 Bessel/Petersson test；holomorphic 行不把
\(t=i/2\) 插入 Maaß multiplier。把两 Maaß parity 在使用同号与异号
Kuznetsov 前写成 average/difference。

对每个这样的共同 test，所需有限核等式是
\[
 \mathcal T^h_{A,B,z,d}
     =\mathfrak D^h_{A,B,z,d}
       +\mathcal O^h_{\boldsymbol J;A,B,z,d}
       +\mathcal R^h_{\boldsymbol J;A,B,z,d}.             \tag{CF4.1}
\]
其对角必须逐 normalization 核对为
\[
 \delta_{m,n}\mathfrak D[h]
 \prod_{p\mid A}\{-(1-t_p)\tau_p(a_p+b_p)\}
 \prod_{p\mid B}\{{\bf1}_{a_p=b_p}
               -(1-t_p)\tau_p(a_p+b_p)\}.               \tag{CF4.2}
\]
只有一个全局 \(\mathfrak D[h]\)。非零 Hecke shifts 全留在
\(\mathcal O\)，含任一 exact local remainder 的项全留在
\(\mathcal R\)。

contract 的连续谱部分还要求：在 trivial-character exact shell 中，
非平凡 primitive
Eisenstein 数据因第一 Fourier index 含 shell prime 而逐系数为零；
剩下 level-one Eisenstein，native measure 是
\[
       \frac{dt}{\zeta(1+2it)\zeta(1-2it)}.              \tag{CF4.3}
\]
对其两个原 shift 变量，必须在系数层逐项得到
\[
 \sum_{h,\delta}\mathcal K_{AB,k}(h\delta;t)W_1(h/Y_1)W_2(\delta/Y_2)
 =\lambda_t(m_0)\sum_{e,f\mid AB}C_{e,f}(t)
  \sum_{\substack{d\ge1\\(d,AB)=1}}\mu(d)
       A_t(Y_1/(de))A_t(Y_2/(df)).                       \tag{CF4.4}
\]
原和在 \(d\) 上有限。将每个 \(A_t=P_t+Q_t\) 后，PP、PQ、QP、QQ
四行具有**相同**的 \(C_{e,f}(t)\mu(d)\)。四行一起延长到无限
\(d\) 时，原有限支撑之外按
\[
       PP+P(-P)+(-P)P+(-P)(-P)=0                         \tag{CF4.5}
\]
逐 \(d\) 精确抵消；这一抵消本身是有限代数，且只延长 PP 不合法。
但 CF4.1--CF4.4 与公开原 atom 的逐 normalization 等同性尚未在本稿
自含证明，因而属于 CF19.D/CF19.L 的来源 adapter，而不是已关闭的
全谱估计。即使该 adapter 完成，连续谱 residues 与物理
principal/axis 的共同抵消仍须另证。

## CF5. quotient 零模与双 Poisson 轴是不同的共同坐标

本文所需 quotient Poisson 的 \(k=0\) contract 行定义为
\[
 Z^{(0)}_{A,B}=\frac{\mu(A)\mu(B)R}{A}\widehat f(0)
 \sum_{\substack{B\mid s\\(A,s)=1}}\frac{g(s/S)}s
 \sum_{h,\delta}v(h/H_1)w(\delta/H_2)c_s(h\delta).       \tag{CF5.1}
\]
对每个 prime power modulus，所需有限二维差分核写成
\[
 c_s(h\delta)=
 \sum_{\substack{d\mid s,d\mid h\\e\mid s,e\mid\delta}}b_s(d,e),
 \qquad
 \sum_{d,e\mid s}\frac{b_s(d,e)}{de}=\frac{\varphi(s)}s,
 \quad
 \sum_{d,e\mid s}\frac{|b_s(d,e)|}{de}\le\tau(s)^2.   \tag{CF5.2}
\]
CF5.2 实际上是一个纯有限恒等式；下面 CF5A 从每个 prime-power
Ramanujan kernel 重证它。这个证明只授权把 CF5.1 的核改写成共同二维
divisor 输出；它不估计 CF5.1，也不把它与后面的 Poisson axes 合并。

双 Poisson 的 nonunit axes contract 则含两条 sampling line 与
一次负的 double integral，其系数分别为 \(1/C,1/C,-g_C/C^2\)。
当 \(g_C\ne1\) 时不可把它们写成同一系数。它们与 CF5.1 是不同
tags；“都是 principal-looking”不构成等同或抵消证明。CF5B 会在
不改动这三个系数的前提下作一次精确 centering；它不是把三系数
强行改成相等。

### CF5A. quotient 零模的共同二维 divisor 系数

令 \(p^a\Vert s\)，并对 \(0\le i,j\le a\) 置
\[
 F_{p^a}(i,j)=c_{p^a}(p^{i+j}),
 \qquad
 b_{p^a}(p^i,p^j)=\Delta_i\Delta_jF_{p^a}(i,j),          \tag{CF5.3}
\]
其中
\(\Delta_iF(i,j)=F(i,j)-F(i-1,j)\)，负指标的 \(F\) 约定为零。
Ramanujan 和的 prime-power 公式是
\[
 F_{p^a}(i,j)=
 \begin{cases}
 0,&i+j<a-1,\\
 -p^{a-1},&i+j=a-1,\\
 p^{a-1}(p-1),&i+j\ge a.
 \end{cases}                                               \tag{CF5.4}
\]
所以二维差分只支撑在三条相邻对角线上，并且精确为
\[
 b_{p^a}(p^i,p^j)=
 \begin{cases}
 -p^{a-1},&i+j=a-1,\\
 p^a,&i+j=a,\ \min(i,j)=0,\\
 p^{a-1}(p+1),&i+j=a,\ i,j\ge1,\\
 -p^a,&i+j=a+1,\ i,j\ge1,\\
 0,&\text{其余情形}.
 \end{cases}                                               \tag{CF5.5}
\]

对任意整数 \(h,\delta\)，令
\(r=\min\{a,v_p(h)\}\)、\(t=\min\{a,v_p(\delta)\}\)，并在
零整数处采用 \(v_p(0)=+\infty\)。二维 telescoping 给
\[
 \sum_{0\le i\le r}\sum_{0\le j\le t}
      b_{p^a}(p^i,p^j)
 =F_{p^a}(r,t)=c_{p^a}(h\delta).                            \tag{CF5.6}
\]
这里最后一个等号也覆盖 \(h=0\) 或 \(\delta=0\)，因为此时截断
valuation 为 \(a\)，而 \(c_{p^a}(0)=\varphi(p^a)\)。

现在若
\(s=\prod_{p^a\Vert s}p^a\)、\(d=\prod p^{i_p}\)、
\(e=\prod p^{j_p}\)，定义
\[
                     b_s(d,e)=\prod_{p^a\Vert s}
                        b_{p^a}(p^{i_p},p^{j_p}).           \tag{CF5.7}
\]
Ramanujan 和的乘法性、CF5.6 与有限乘积的 Fubini 立刻给 CF5.2 的
第一式。其余两式也可逐 prime 精确核算。由 CF5.5，
\[
 \begin{aligned}
 \sum_{i,j=0}^a{b_{p^a}(p^i,p^j)\over p^{i+j}}
   &=-a+2+(a-1){p+1\over p}-{a\over p}=1-{1\over p},\\
 \sum_{i,j=0}^a{|b_{p^a}(p^i,p^j)|\over p^{i+j}}
   &=2a+1+{2a-1\over p}\le(a+1)^2.
 \end{aligned}                                             \tag{CF5.8}
\]
第一行张量后是 \(\varphi(s)/s\)，第二行张量后至多
\(\prod_{p^a\Vert s}(a+1)^2=\tau(s)^2\)。因此 CF5.2 的三个陈述
已经全部证明，而且同一个 \(b_s(d,e)\) 同时覆盖 nonaxis、两条 axis
与 origin。尚未证明的是 CF5.1 连同 CF3/CF4 的 signed 上界，以及
CF5.1 与物理 principal/axis/residue 行在 CF19.C 中的共同压缩；不能
因 CF5.8 的正主质量就分别估计或删除其中任何一行。

CF5.5 还给出比总质量更精确的两个边缘恒等式：对每个 \(d,e\mid s\)，
\[
 \boxed{\quad
 \sum_{e\mid s}{b_s(d,e)\over e}
   =\varphi(s){\bf1}_{d=s},\qquad
 \sum_{d\mid s}{b_s(d,e)\over d}
   =\varphi(s){\bf1}_{e=s}.
 \quad}                                                     \tag{CF5.9}
\]
逐 prime 验证第一式即可；当 \(d=p^i\) 时，CF5.5 的至多三个非零
项相加，\(i<a\) 时为零，\(i=a\) 时为
\(p^a-p^a/p=\varphi(p^a)\)。第二式由对称性，随后张量得到一般
\(s\)。CF5.8 的 signed 总质量也可由 CF5.9 再对 \(d\) 平均得到。

这使“bulk、两轴、origin 必须共同投影”成为一个精确有限正交等式。
在 \((\mathbb Z/s\mathbb Z)^2\) 上取归一化计数内积，并令
\(R_s(h,\delta)=c_s(h\delta)\)。直接从 Ramanujan 和的 Fourier 定义
（或从 CF5.2 与 CF5.9）得到
\[
 \mathbb E_\delta R_s(h,\delta)
   =\varphi(s){\bf1}_{h=0},\qquad
 \mathbb E_hR_s(h,\delta)
   =\varphi(s){\bf1}_{\delta=0},\qquad
 \mathbb E_{h,\delta}R_s={\varphi(s)\over s}.             \tag{CF5.10}
\]
故置
\[
 R_s^\circ(h,\delta)=R_s(h,\delta)
  -\varphi(s){\bf1}_{h=0}-\varphi(s){\bf1}_{\delta=0}
  +{\varphi(s)\over s},                                    \tag{CF5.11}
\]
便有精确的共同四项分解
\[
 \begin{aligned}
 R_s={}&R_s^\circ
 +\varphi(s)\left({\bf1}_{h=0}-{1\over s}\right)
 +\varphi(s)\left({\bf1}_{\delta=0}-{1\over s}\right)
 +{\varphi(s)\over s},\\
 \|R_s\|_2^2={}&\|R_s^\circ\|_2^2
   +2{\varphi(s)^2(s-1)\over s^2}+{\varphi(s)^2\over s^2}.
 \end{aligned}                                             \tag{CF5.12}
\]
四项两两正交：\(R_s^\circ\) 的两个边缘均为零，两条 axis 函数各只
依赖一个坐标且均值为零，最后一项为常数。于是任何 complete-shift
不等式若使用完整 residue projection，必须在**同一个**范数里先放入
CF5.12 的双中心、两轴和常数，而不能只保留 \(R_s^\circ\) 后把正的
origin mass 丢掉。

不完整的 \((h,\delta)\) 光滑窗口对 **CF5.1 本身** 也不造成代数
adapter。对任意有限支撑的复权 \(\Psi(h,\delta)\)，定义其共同
residue periodization
\[
 W_s(a,b)=\sum_{\substack{h\equiv a\pmod s\\
                           \delta\equiv b\pmod s}}
                         \Psi(h,\delta).                   \tag{CF5.13}
\]
若 \(P_h,P_\delta,P_0\) 分别表示在第二坐标平均、在第一坐标平均及
全平均，并令
\[
 W_s^\circ=(I-P_h)(I-P_\delta)W_s,\quad
 W_s^h=P_hW_s-P_0W_s,\quad
 W_s^\delta=P_\delta W_s-P_0W_s,                           \tag{CF5.14}
\]
则有限换序与 CF5.12 的正交性给出
\[
 \begin{aligned}
 \sum_{h,\delta\in\mathbb Z}\Psi(h,\delta)c_s(h\delta)
 =s^2\{&\langle R_s^\circ,W_s^\circ\rangle
 +\langle \varphi(s)({\bf1}_{h=0}-s^{-1}),W_s^h\rangle\\
 &+\langle \varphi(s)({\bf1}_{\delta=0}-s^{-1}),
                         W_s^\delta\rangle
 +{\varphi(s)\over s}\,P_0W_s\},                         \tag{CF5.15}
 \end{aligned}
\]
其中所有内积使用归一化剩余类测度并在第二变量线性；最后一个
\(P_0W_s\) 是常数值。特别地，一次共同 Cauchy 给
\[
 \begin{aligned}
 \left|\sum_{h,\delta}\Psi(h,\delta)c_s(h\delta)\right|
 \le s^2\bigg{&\|R_s^\circ\|_2\|W_s^\circ\|_2
 +{\varphi(s)\sqrt{s-1}\over s}
      (\|W_s^h\|_2+\|W_s^\delta\|_2)\\
 &+{\varphi(s)\over s}|P_0W_s|\bigg\}.                   \tag{CF5.16}
 \end{aligned}
\]
所以 CF5.1 的任意有限 smooth/AFE weight 已经可在**同一个**四项
不等式中处理；不需要先把窗口补成矩形再分别估计边界。

CF5.15--CF5.16 仍不是整个物理行的闭合。双 Poisson 另外产生的两条
sampling line 与 double-integral correction 具有 CF5 中记录的实际
系数。尚须证明这些额外 physical axes 在共同 Abel/Fourier 展开后恰
映到 CF5.15 的三个低秩分量，或把差项原样留在 CF6 的 native tags。
这个要求现在是一个明确的 coefficient identity，而不再是含糊的
“principal-looking”抵消；CF5.16 自身也没有提供 centered power
saving。

### CF5B. unequal-gcd 双 Poisson 轴的精确共同 centering

上一段所说的物理映射中，有一部分其实可以在不使用任何解析估计时
完成。固定 \(C\ge1\)，令
\[
 g_C=(D,C),\qquad c={C\over g_C},qquad
 I(F)=\iint_{(0,\infty)^2}F(m,n)\,dm\,dn,
\]
其中 \(F\) 连续可积且紧支撑于正象限。定义两条实际 sampling line
及其零密度中心化为
\[
 \begin{aligned}
 S_c^m(F)&=\sum_{j\ge1}\int_0^\infty F(cj,n)\,dn,&
 \Lambda_c^m(F)&=S_c^m(F)-{I(F)\over c},\\
 S_c^n(F)&=\sum_{j\ge1}\int_0^\infty F(m,cj)\,dm,&
 \Lambda_c^n(F)&=S_c^n(F)-{I(F)\over c}.
 \end{aligned}                                           \tag{CF5.17}
\]
两个和因紧支撑而有限。因为 \(1/(Cc)=g_C/C^2\)，逐 \(C\) 有恒等式
\[
 \boxed{\quad
 {S_c^m(F)+S_c^n(F)\over C}-{g_C\over C^2}I(F)
 ={\Lambda_c^m(F)+\Lambda_c^n(F)\over C}
   +{g_C\over C^2}I(F).
 \quad}                                                   \tag{CF5.18}
\]
所以原来负的 double integral 只扣掉两条 sampling line 的两个平均
副本中的**一个**；另一个平均副本必须保留。把两轴都称为 mean zero
并同时删掉 integral 会错一个 \(g_C I(F)/C^2\)。CF5.18 对
\(g_C=1\) 与所有 unequal-gcd 层同时成立，没有平均 gcd 或另付
\(O(1/p)\)。

更具体地，对任意有限集
\(\mathcal C\subset\{C:B\mid C,(A,C)=1\}\)，以及每个
\(C\in\mathcal C\) 的实际权 \(F_C=F_{k,C}\)，令
\[
 u_C=c_C(q)\left(C^{-1},C^{-1},g_C C^{-2}\right),\qquad
 v_C=\left(\Lambda_c^m(F_C),\Lambda_c^n(F_C),I(F_C)\right).
\]
在 \(\bigoplus_{C\in\mathcal C}\mathbb C^3\) 中使用第二变量线性的
标准内积，则完整有限 nonunit-axis 包精确为
\[
 \mathcal A_{\mathcal C}
 ={\mu(A)\over A}\sum_{C\in\mathcal C}\langle u_C,v_C\rangle,
\]
从而一次共同 Cauchy 给出
\[
 \boxed{
 |\mathcal A_{\mathcal C}|\le {1\over A}
 \left\{\sum_{C\in\mathcal C}|c_C(q)|^2
       \left({2\over C^2}+{g_C^2\over C^4}\right)\right\}^{1/2}
 \left\{\sum_{C\in\mathcal C}
  (|\Lambda_c^m(F_C)|^2+|\Lambda_c^n(F_C)|^2+|I(F_C)|^2)
 \right\}^{1/2}.}                                       \tag{CF5.19}
\]
这正是所要求的“同一个不等式”在双 Poisson axes 上的有限版本：
两条 centered sampling axes、double-integral 留下的常数及全部
unequal gcd 不再被分别取绝对值。其证明只有 CF5.17、
\(C=g_Cc\) 与有限维 Cauchy。

CF5.19 没有声称第二个大括号具有所需 power saving。它也没有把
连续 comb functional 与 CF5.15 的有限 residue kernel 认成同一对象；
目前只证明二者具有相同的“两条 centered axes 加常数”低秩形状。
要和 quotient-zero、diagonal、principal residue 发生真正抵消，仍须
从原 atom 证明共同 \(F_C\)/\(W_s\) 映射及外权完全一致。

### CF5C. 真正零模的 nonunit Ramanujan 核精确降到 reduced modulus

CF5B 与 CF5A 在 quotient-zero 上的算术系数可以进一步逐项对齐。
仍令 \(g=(D,C)\)、\(c=C/g\)。定义 \(C_\parallel\) 为 \(C\) 的最大
unitary divisor 且 \(C_\parallel\mid g\)，也就是
\[
 C_\parallel=\prod_{\substack{p^a\Vert C\\p^a\mid g}}p^a,
 \qquad g_*=g/C_\parallel,\qquad
 \kappa(C,g)=\varphi(C_\parallel)g_* .                   \tag{CF5.20}
\]
则对每个整数 \(x\) 有
\[
 \boxed{\qquad c_C(gx)=\kappa(C,g)c_c(x),\qquad
              \kappa(C,g)\varphi(c)=\varphi(C).\qquad}  \tag{CF5.21}
\]
证明是逐 prime-power 的。若 \(p^a\Vert C\)、\(p^j\Vert g\) 且
\(j<a\)，Ramanujan 和的三段公式直接给
\[
 c_{p^a}(p^jx)=p^j c_{p^{a-j}}(x).
\]
若 \(j=a\)，左边恒为 \(\varphi(p^a)\)。将两类局部式相乘得到
CF5.21；第二式逐素数同样显然。这个证明包含 \(c=1\) 的退化层。

在 nonunit double-Poisson 原式中，\(D/g\) 在模 \(c\) 下可逆；令
\(\delta(D/g)\equiv1\pmod c\)。又因 \((A,C)=1\)，\(A\delta\) 是
模 \(c\) 的单位。所以在真正零模 \(q=Lk=0\) 上，CF5.21 给
\[
 \boxed{
 c_C(gA\delta uv)=\kappa(C,g)c_c(uv).}                  \tag{CF5.22}
\]
因此对任何有限 dual-frequency 截断，可先把其任意权按
\((u,v)\bmod c\) periodize，再原样使用 CF5.10--CF5.16；bulk、
两轴与 origin 都在同一个 reduced-modulus Ramanujan 核中。

这个 finite residue 描述与 CF5B 的 continuous-comb 描述在轴上也
逐系数吻合。零模轴的 Ramanujan 值为 \(c_C(0)=\varphi(C)\)。原
nonunit 双变换系数 \(g/C^2\) 在一条轴上作 spacing-\(c\) 的一维
Poisson 后乘 \(c\)，故
\[
 {g\over C^2}\,c\,\varphi(C)={\varphi(C)\over C};       \tag{CF5.23}
\]
这正是 CF5B 中 \(c_C(0)/C\) 的 sampling coefficient。被两轴重复
计入而只应保留一次的 dual origin，其系数则是
\(g\varphi(C)/C^2\)，正是 CF5B 的 double-integral coefficient。
所以 zero-frequency 的 finite residue、两条 sampling lines 与
deleted origin 已经完成 coefficient-level 对齐；没有第二个
\(g\)、\(C\) 或 \(A^{-1/2}\) 可再收取。

CF5.22 不能外推到 \(q\ne0\)。最小反例是
\[
 C=3,\quad g=1,\quad q=1:\qquad
 (c_3(1+x))_{x=0,1,2}=(-1,-1,2),
 \quad(c_3(x))_{x=0,1,2}=(2,-1,-1),                    \tag{CF5.24}
\]
两向量不成比例。因此 nonzero quotient frequencies 仍必须留在 CF4
的真实 shifted kernel；CF5C 只关闭零模的 unequal-gcd coefficient
adapter。把 CF5.22 用于 CF4 会是可执行有限反例已经排除的错误。

### CF5D. centered Ramanujan 核的精确质量及复合壳障碍

CF5.12 中唯一尚未求值的有限量 \(\|R_s^\circ\|_2\) 也有闭式。
若 \(p^a\Vert s\)，模 \(p^a\) 的一个剩余类的截断 valuation 为
\(0\le i\le a\)，其中 \(i<a\) 的类数是
\(p^{a-i-1}(p-1)\)，而 \(i=a\) 只含零类。于是
\[
 \#\{(h,\delta):v_p(h)+v_p(\delta)\ge a\}
 =p^{a-1}\{a(p-1)+p\},
\]
以及
\[
 \#\{(h,\delta):v_p(h)+v_p(\delta)=a-1\}
 =a p^{a-1}(p-1)^2.                                    \tag{CF5.25}
\]
把 CF5.4 的两个非零值平方后代入，得到
\[
 \mathbb E_{h,\delta\bmod p^a}|c_{p^a}(h\delta)|^2
 =(a+1)p^{a-2}(p-1)^2.
\]
中国剩余定理使不同素数的核与归一化测度都张量分解，故
\[
 \boxed{
 \|R_s\|_2^2
 =s\tau(s)\left({\varphi(s)\over s}\right)^2.}         \tag{CF5.26}
\]
再从 CF5.12 精确扣除两轴与常数，便有
\[
 \boxed{
 \|R_s^\circ\|_2^2
 =\left({\varphi(s)\over s}\right)^2
      \{s\tau(s)-2s+1\}.}                              \tag{CF5.27}
\]
特别地，\(s=p\) 为素数时
\(\|R_p^\circ\|_2=(p-1)/p\)，而
\(\|R_p\|_2\asymp\sqrt{2p}\)：共同两轴 centering 在 prime shell
上确实给出一个平方根量级的下降。这份下降已经完全包含在
CF5.27 中，不能再与 valuation-one 或 harmonic normalization 的
半根相乘一次。

但 CF5.27 也给出不能回避的复合壳反例。若 \(s=pq\) 是两个不同素数
的乘积，则
\[
 {\|R_{pq}^\circ\|_2^2\over\|R_{pq}\|_2^2}
 ={2pq+1\over4pq}\longrightarrow {1\over2}.             \tag{CF5.28}
\]
所以不存在固定 \(\delta>0\)，使所有平方自由 \(s\) 都有
\(\|R_s^\circ\|_2\ll s^{-\delta}\|R_s\|_2\)。共同投影本身只关闭
prime-shell 的低秩质量；两个及更多活动素数的 centered bulk 仍必须
由保留两侧 Möbius 符号的 varying-level dispersion/reciprocity 支付。
CF5.28 是这个需求的核级反例，不是说实际带符号物理和没有额外抵消。

### CF5E. squarefree 壳的四状态张量与 alternating cofactors

CF5D 的复合壳质量还可分解成一套显式正交坐标。对素数 \(p\) 令
\[
 f_p(x)={\bf1}_{p\mid x}-{1\over p}\qquad(x\bmod p).
\]
直接检查 \(p\mid h\delta\) 与 \(p\nmid h\delta\) 两种情形，得到
\[
 c_p(h\delta)=-p f_p(h)f_p(\delta)
 +(p-1)f_p(h)+(p-1)f_p(\delta)+{p-1\over p}.            \tag{CF5.29}
\]
其中 \(1\) 与 \(f_p\) 正交，且
\(\|f_p\|_2^2=(p-1)/p^2\)。若 \(s\) 平方自由，记
\(\mathcal P(s)=\{p:p\mid s\}\)，并对 \(U\subseteq\mathcal P(s)\) 置
\(f_U(x)=\prod_{p\in U}f_p(x_p)\)。由 CRT 与 CF5.29，
\[
 \boxed{
 R_s^\circ(h,\delta)=
 \sum_{\substack{\varnothing\ne U,V\subseteq\mathcal P(s)}}
 K_s(U,V)f_U(h)f_V(\delta),}                             \tag{CF5.30}
\]
其中
\[
 K_s(U,V)=
 \prod_{p\in U\cap V}(-p)
 \prod_{p\in U\triangle V}(p-1)
 \prod_{p\in\mathcal P(s)\setminus(U\cup V)}{p-1\over p}.
                                                               \tag{CF5.31}
\]
不同 \((U,V)\) 两两正交。CF5.30 的限制 \(U,V\ne\varnothing\) 恰是
全局双 centering：\(U=\varnothing\) 或 \(V=\varnothing\) 正好是
CF5.12 已抽出的常数/axis 坐标。将 CF5.31 的平方乘
\(\|f_U\|_2^2\|f_V\|_2^2\) 后求和，也逐素数重得 CF5.27。

现在固定一个有限素数集 \({\cal P}\)，把每个 \(R_s^\circ\)
（\(s\mid\prod_{p\in\mathcal P}p\)）按 CRT 提升到共同空间，在
\(p\nmid s\) 的坐标上取常数。对固定非空 \(U,V\subseteq\mathcal P\)，
完整 squarefree cofactor cube 的带符号系数为
\[
 \boxed{
 \sum_{\substack{s\mid\prod_{p\in\mathcal P}p\\U\cup V\subseteq
                    \mathcal P(s)}}
 \mu(s)K_s(U,V)
 =(-1)^{|U\triangle V|}
   \prod_{p\in U\triangle V}(p-1)
   \prod_{p\in U\cap V}p
   \prod_{p\in\mathcal P\setminus(U\cup V)}{1\over p}.} \tag{CF5.32}
\]
证明完全局部：\(p\in U\cap V\) 时
\((-1)(-p)=p\)；\(p\in U\triangle V\) 时得到 \(-(p-1)\)；
而未激活的 \(p\) 在“不进 \(s\)”和“进入 \(s\) 的常数态”之间给
\[
                    1-{p-1\over p}={1\over p}.
\]
这正是 alternating cofactor 不能在取范数前丢掉的逐素数收益。

CF5.32 不是对实际 dyadic level shell 的估计。它要求同一个提升后的
列在完整 Boolean cube 上出现；物理的 product interval、taper、
exact-valuation 条件与 AFE/Bessel 权都会删去或改变部分顶点。真正的
CF19.L 必须证明这些变化能由共同 Abel/reflection operator 承担，或
直接对缺顶点的 signed cube 给出同强度界。逐 \(s\) 取绝对值会把
CF5.32 最后一个 \(1/p\) 精确变回 \(1+(p-1)/p\)，因而不是允许的
替代证明。

### CF5F. product shell 可精确冻结 Möbius parity

CF5.32 的完整 cube 收益不能只靠“权很光滑”迁到每个 dyadic product
shell。固定 inactive prime 集 \({\cal I}\) 及
\(1\le r\le|\mathcal I|\)，记
\(r_p=(p-1)/p\)。若一个权只保留 \(|T|=r\) 的顶点，则
\[
 \boxed{
 \sum_{T\subseteq\mathcal I}(-1)^{|T|}
       \prod_{p\in T}r_p\,{\bf1}_{|T|=r}
 =(-1)^r e_r((r_p)_{p\in\mathcal I}),}                  \tag{CF5.33}
\]
其中 \(e_r\) 是第 \(r\) 个初等对称多项式。右边所有项同号；若
每个 \(p\ge2\)，其绝对值至少为
\(2^{-r}\binom{|\mathcal I|}{r}\)。完整 cube 的
\(\prod_{p\in\mathcal I}p^{-1}\) 在这里完全没有出现。

而 CF5.33 确实能由通常的平滑 product cutoff 实现。取
\({\cal I}\) 中所有不同素数都在 \([X,(1+\epsilon)X]\)，固定
\((1+\epsilon)^r<3/2\)，并令 \(X\) 足够大，使
\((1+\epsilon)^{r-1}/X<1/2\) 且 \(X>2\)。可选
\(F\in C_c^\infty((1/2,2))\) 在
\([1,(1+\epsilon)^r]\) 上恒为一。于是逐顶点精确有
\[
 F\left({\prod_{p\in T}p\over X^r}\right)
 ={\bf1}_{|T|=r}.                                       \tag{CF5.34}
\]
事实上 \(|T|\le r-1\) 时自变量小于 \(1/2\)，\(|T|=r\) 时落在
上述平台，而 \(|T|\ge r+1\) 时自变量大于 \(2\)。所以一个标准
smooth dyadic shell 可以冻结 \(\mu(\prod_{p\in T}p)=(-1)^r\)，并
把 CF5.32 所依赖的不同 cardinality 之间抵消全部切断。

这是否定一条具体路线，而不是停止点：**complete Boolean cube
+ smooth Abel** 不能单独提供实际 shell 的 varying-level saving。
后续估计必须在固定 \(\omega(s)=r\) 的同号层内部保留两侧 level、
shift 与 Bessel 相位并产生 dispersion，或证明物理重组在取 shell
cutoff 前就已把相邻 cardinality 重新耦合。CF5.34 不排除这两种真正
的 signed analytic 机制。

### CF5G. 分离平滑权把 centered 零模化为倍数采样误差

CF5.1 的实际非零 dyadic \((h,\delta)\)-权是分离的，因而 centered
bulk 还有一条不需要 level reciprocity 的精确约化。令
\(v,w\in C_c^1(\mathbb R\setminus\{0\})\)，
\(H_1,H_2>0\)，并定义
\[
 V_d=\sum_{d\mid h}v(h/H_1),\qquad
 W_e=\sum_{e\mid\delta}w(\delta/H_2),
\]
以及相对于完整整数格平均的误差
\[
 E_d^v=V_d-{V_1\over d},\qquad
 E_e^w=W_e-{W_1\over e}.                                \tag{CF5.35}
\]
所有和都因紧支撑而有限，且 \(E_1^v=E_1^w=0\)。将 CF5.2 插入
加权和，并使用 CF5.9 的两个边缘恒等式与 CF5.8 的总质量，逐项展开
即得
\[
 \boxed{
 \sum_{h,\delta}v(h/H_1)w(\delta/H_2)R_s^\circ(h,\delta)
 =\sum_{d,e\mid s}b_s(d,e)E_d^vE_e^w.}                 \tag{CF5.36}
\]
例如右边展开后的三条校正分别是
\(-\varphi(s)V_sW_1\)、\(-\varphi(s)V_1W_s\) 与
\(\varphi(s)V_1W_1/s\)，恰好就是 CF5.11 的两轴与常数；没有
额外 endpoint remainder。

一维误差有 uniform discrepancy 界。若
\(u\in C_c^1(\mathbb R\setminus\{0\})\)，
则存在只依赖 \(u\) 支撑、\(\|u\|_\infty\)、\(\|u\|_1\) 与
\(\|u'\|_1\) 的常数 \(C_u\)，使所有 \(H>0,d\ge1\) 都有
\[
 \boxed{
 \left|\sum_{d\mid n}u(n/H)-{1\over d}\sum_nu(n/H)\right|
 \le C_u\min\left(1,{H\over d}\right).}                \tag{CF5.37}
\]
证明不使用指数和。把整数按模 \(d\) 的剩余类分组；零类与第 \(r\)
类逐项平移比较，区间
\([dk/H,(dk+r)/H]\) 对固定 \(r\) 不交叠，故差至多
\(\|u'\|_1\)。对所有 \(r\) 平均给 \(O_u(1)\)。若 \(d>H\)，
因支撑避开零，紧支撑内每个非空采样本身迫使
\(H/d\gg_u1\)，而采样点数是
\(O_u(H/d)\)；若采样为空，只剩
\(d^{-1}\sum_nu(n/H)=O_u(H/d)\)。这给第二个界并与第一个取小。

CF5.36--CF5.37 因而给出完全显式的 centered 零模上界
\[
 \boxed{
 \left|\sum_{h,\delta}v(h/H_1)w(\delta/H_2)R_s^\circ(h,\delta)\right|
 \ll_{v,w}
 \sum_{d,e\mid s}|b_s(d,e)|
 \min\left(1,{H_1\over d}\right)
 \min\left(1,{H_2\over e}\right).}                    \tag{CF5.38}
\]
在 prime shell \(s=p\) 上，\(E_1=0\) 与 CF5.5 只留下
\(b_p(p,p)=-p\)，所以右边精确缩成
\[
 p|E_p^vE_p^w|\ll_{v,w}
 p\min(1,H_1/p)\min(1,H_2/p),                           \tag{CF5.39}
\]
特别在 \(H_1,H_2\le p\) 时为 \(O(H_1H_2/p)\)。

CF5.38 已经证明一个适用于全部模数和端点的 centered analytic bound，
但尚未证明其 divisor cost 在所有物理复合壳都达到 CF9.1 的指数。
也没有估计 CF5.12 的两条低秩轴与常数；它们仍须和 CF5B 的 sampling
axes、diagonal 及 principal/residue ledger 在同一原子中压缩。
因此这关闭的是“任意平滑权仍需二维 residue 大筛”的假障碍，并把
真实剩余义务缩成 CF5.38 的复合 divisor cost 加低秩共同 ledger。

### CF5H. 短于最小素因子的偶 parity 零模见证

CF5.38 的复合 divisor cost 在一个重要物理范围不能继续逐模数改善。
设 \(s>1\) 平方自由，并记 \(P^-(s)=\min_{p\mid s}p\)。若
\((h\delta,s)=1\)，则 Ramanujan 和等于 \(c_s(h\delta)=\mu(s)\)，
而 CF5.11 的两个 residue axes 均为零。因此
\[
 \boxed{
 R_s^\circ(h,\delta)=\mu(s)+{\varphi(s)\over s}
 \qquad((h\delta,s)=1).}                                \tag{CF5.40}
\]
若 CF5G 的权支撑还满足：每个被采样的非零整数 \(h,\delta\) 都有
\(|h|,|\delta|<P^-(s)\)，则它们自动与 \(s\) 互素，故整个矩形上
逐项相同，得到精确式
\[
 \boxed{
 \sum_{h,\delta}v(h/H_1)w(\delta/H_2)R_s^\circ(h,\delta)
 =\left(\mu(s)+{\varphi(s)\over s}\right)V_1W_1.}       \tag{CF5.41}
\]
这也可从 CF5.36 看出：所有 \(d,e>1\) 的倍数采样为零，故
\(E_d^v=-V_1/d\)、\(E_e^w=-W_1/e\)，而 CF5.9 给
\[
 \sum_{\substack{d,e\mid s\\d,e>1}}{b_s(d,e)\over de}
 =\mu(s)+{\varphi(s)\over s}.
\]

于是 parity 的差别是结构性的：
\[
 \begin{cases}
 \mu(s)+\varphi(s)/s>1,&\omega(s)\text{ 为偶数},\\
 |\mu(s)+\varphi(s)/s|
 =1-\prod_{p\mid s}(1-p^{-1})\le\sum_{p\mid s}p^{-1},
   &\omega(s)\text{ 为奇数}.
 \end{cases}                                             \tag{CF5.42}
\]
所以即使已经共同删除两轴与常数，短矩形上的偶 prime-factor 层仍有
一个与 \(V_1W_1\) 同量级的真实 centered 零模。CF5.42 否定的是
“每个复合模数单独由 centering 获得 power saving”；它不排除这个
偶 parity 见证与另一侧 level 符号、diagonal 或 principal/residue
ledger 在**取绝对值以前**抵消。该联合抵消现在是零模最窄的开放叶子。

### CF5I. unit 零模与 principal subtraction 的精确共同标量

CF5H 的偶 parity 见证并不允许把 CF5.12 的低秩三项丢掉。对
\((h\delta,s)=1\)，两条 axis 与常数逐点分别是
\(-\varphi(s)/s,-\varphi(s)/s,+\varphi(s)/s\)。所以 CF5.40 与
CF5.12 在 unit 行精确合回
\[
 \boxed{
 R_s(h,\delta)
 =\left(\mu(s)+{\varphi(s)\over s}\right)
   -{\varphi(s)\over s}-{\varphi(s)\over s}
   +{\varphi(s)\over s}
 =\mu(s).}                                               \tag{CF5.43}
\]
也就是说，低秩账本先且只先消掉 CF5H 中的
\(\varphi(s)/s\)；剩下的 parity 标量是 \(\mu(s)\)。

这正好是 principal reverse-Poisson completion 的零频标量。平方自由
\(s>1\) 满足纯有限恒等式
\[
 \boxed{
 {1\over\varphi(s)}\sum_{j\mid s}j\mu(j)=\mu(s).}       \tag{CF5.44}
\]
现在取任意有限 unit 标签集 \(D_s\)、复系数 \(a_\delta\)，以及两族
零频标量 \(z_\delta,z'_\delta\)。把已经由 CF5.43 合回的 unit 零模与
principal completion 的 subtraction 定义成
\[
 \begin{aligned}
 Z_s(z)&=\mu(s)\sum_{\delta\in D_s}a_\delta z_\delta,\\
 P_s(z')&=-{1\over\varphi(s)}\sum_{\delta\in D_s}a_\delta z'_\delta
                              \sum_{j\mid s}j\mu(j).
 \end{aligned}
\]
则 CF5.44 立即给出同一个共同恒等式
\[
 \boxed{
 Z_s(z)+P_s(z')
 =\mu(s)\sum_{\delta\in D_s}a_\delta(z_\delta-z'_\delta).} \tag{CF5.45}
\]
特别地，若两处使用同一个零频权，即 \(z_\delta=z'_\delta\)，unit
零模、两轴、常数和 principal subtraction 的总和逐 \(s,\delta\)
精确为零；无须对偶数与奇数 \(\omega(s)\) 分开估计，也没有
\(2^{\omega(s)}\) 成本。

CF5.45 没有自行证明实际物理权相同。原式的 quotient-zero
\(\widehat f(0)\) 来自第一条 Poisson/AFE 坐标，而 principal
subtraction 的 \(\widehat F_{r,s,\delta}(0)\) 来自 reverse Poisson。
更重要的是，(4.4)--(4.5) 的合法 reflection 顺序必须先在每个有限
dyadic box 内求完全部 Poisson \(h\)，再恢复整数格、使用共同 cutoff，
最后把乘积核拉回原 mollifier 坐标；不存在可直接调用的固定 \(h\) 或
固定 \((s,\delta)\) packetwise 等距 adapter。因此 CF5.45 只能在这个
全局过程确实供应了共同列 \(z,z'\) 后使用，不能反过来用它证明两列
相同。若所供应的两列只近似相等，CF5.45 右边是 **unit 零频子账本**
的全部 mismatch，却不是完整物理余项的唯一 mismatch：延拓补偿、
nonunit reduced-modulus 行、原 AFE diagonal、archimedean correction、
Eisenstein residues 及非零频率补集仍全须保留。因此这一步关闭的是
parity/低秩/principal 的有限系数重组，不是完整 physical ledger。

## CF6. 一个不重不漏的 master tag 集

在所有有限截断固定后，先按**已经逐项验证的** adapter 作一个互斥
分割：\(\mathscr P_{\rm exp}\) 是能合法使用 CF0/CF3/CF4 的指定平方自由
exact-shell 行，\(\mathscr P_{\rm nat}\) 是其余 native complement。
这个分割在原有限整数支撑上逐项决定；不以估计大小或事后 cancellation
决定。令 \(\Omega_{T,\sharp}\) 为下列互斥 tags：

\[
 \omega=(\mathfrak r,\tau,q_0,R,S,A,B,\epsilon_L,\epsilon_R,k,
         \mathfrak a,\mathfrak s,\boldsymbol J,e,f,d,\varpi).
 \tag{CF6.1}
\]

其中：

- \(\mathfrak r\in\{{\rm expanded},{\rm native}\}\) 记录上述互斥分支；
- \(\tau\) 记录原 height sign、AFE direction、smooth partition、
  actual \(b^\sharp\) coefficient pair、gcd/valuation 与 nonflat 标签；
- 在 expanded 分支，\((\epsilon_L,\epsilon_R)\in\{0,1\}^2\)
  记录 CF3.1 的四行，\(k=0\) 使用 CF5.1，\(k\ne0\) 使用 CF4.1；
- 在 native 分支，上述 quotient/spectral 子标签取一个哑元值，
  \(\mathcal K_\omega\) 就是未展开的原物理 kernel；这不是把它估计掉；
- \(\mathfrak a\) 是 nonaxis、left axis、right axis 或 origin correction；
- 对指定 trivial-character exact shell，\(\mathfrak s\) 是 Maaß-even、
  Maaß-odd、holomorphic 或 Eisenstein；其他 character rows 留在 native
  complement，不能借 CF4.3 宣称消失；
- \(\varpi\in\{PP,PQ,QP,QQ\}\) 只在 Eisenstein residue 行出现；
- 含 local Hecke remainder 的 tag 与 polynomial tag 互斥。

令 \(C_\omega\) 是从原有限和按上述**已验证**恒等式逐次展开得到的
系数；尚未验证 CF4 adapter 的行必须留在 native complement。这一
定义唯一地保留以下规则：实际 \(b^\sharp\) 对只出现一次；
CF3.2 的 quotient Möbius 符号只出现一次；CF4.4 的
\(C_{e,f}(t)\mu(d)\) 四行共用；(CF2.2) 在整个 atom 外只出现一次。

把对应核值记为 \(\mathcal K_\omega\)。有限线性立刻给
\[
 \boxed{\quad
 \mathcal C_{T,\sharp}^{\rm full}
    =\Re\sum_{\omega\in\Omega_{T,\sharp}}
       \frac{2T}{q_0(\omega)R(\omega)S(\omega)}
          C_\omega\mathcal K_\omega .
 \quad}                                                   \tag{CF6.2}
\]
这里 \(\mathcal C^{\rm full}\) 是该高度壳完整 centered 物理输出，
不是只含非零 Kloosterman 行。CF6.2 的 expanded 部分同时含 quotient
endpoint、\(k=0\)、axes、diagonal、nonzero geometric row、连续谱四
residue rows 与 local remainder；native complement 则原样保留尚无
合法 adapter 的 non-squarefree、其他 character、nonflat、unequal-gcd
或其他未展开行。这样完整性来自显式保留补集，不来自假想覆盖。

对已经进入 \(\mathscr P_{\rm exp}\) 的行，CF6.2 的证明是有限恒等式
的复合：先 CF3，再 quotient Poisson 与 corrected lift，再 CF4/CF5，
最后只在共同有限系数下求和。因此没有 Fubini 问题。本文尚未自含
证明 CF4 与公开原 atom 的逐项 adapter，所以在当前可复核结论中这些
候选行不得离开 native complement。取 \(\boldsymbol J\to\infty\) 时只使用每个固定
\(A,B\) 已证明的 local remainder limit；取 Eisenstein \(d\) cutoff
到无穷时必须把 CF4.5 四行一起取极限。本文不交换这些极限与全部
varying-level 外和。

## CF7. shell 的 \(A^{-1/2}\) 只计一次

在 shell prime \(p\) 的 ambient oldclass harmonic convention 中
\[
 P_1(0,0)=\frac1{(p+1)\rho_p}\asymp p^{-1}.              \tag{CF7.1}
\]
exact-shell ratio 是相对于 CF7.1 定义的。由下面 CF7.2--CF7.3 的
完整 \(C_2\) 向量，unshifted ratio 精确为
\[
 {D_p(0,0)\over P_1(0,0)}=1-{p\over p^2-1};
\]
它仍为 \(O(1)\) 且没有额外 saving。shifted \(b=0\) cell
给 \(O(p^{-1+\theta})\)；\(b=1\) AFE cell 的 ratio 是 \(O(1)\)，
但系数能量密度为 \(p^{-1}\)，故 Hilbert norm 为 \(p^{-1/2}\)。

所以 product shell 的 \(A^{-1/2}\) 是在 ambient harmonic measure
归一化后的 coefficient norm。CF6.2 中既不能再乘 CF7.1 的
\(p^{-1}\)，也不能另引入旧错误 cross-cusp 模型的第二个
\(p^{-1/2}\)。物理外权 CF2.2、Poisson 外因子 \(R\) 与该局部
Hilbert norm 是三个不同来源，各只计一次。

### CF7A. exact-shell 局部核与 half-root 的自含证明

为使后面的 level 分割可由 fresh checkout 复核，这里从定义重证所需
局部结论。令 \(p\) 是 trivial-central-character primitive datum 的
unramified prime，
\(\lambda_j=\lambda_\pi(p^j)\)，负指标取零，并使用
\(\lambda_{j+1}=\lambda_1\lambda_j-\lambda_{j-1}\)。置
\[
 t_p={\lambda_1\over p+1},\qquad
 \rho_p=1-pt_p^2,
\]
以及
\[
\begin{aligned}
 C_0(j)&=\lambda_j,\\
 C_1(j)&={\sqrt p\over\sqrt{\rho_p}}
                 (\lambda_{j-1}-t_p\lambda_j),\\
 C_2(j)&={p\lambda_{j-2}-\lambda_1\lambda_{j-1}+p^{-1}\lambda_j
          \over\sqrt{\rho_p(1-p^{-2})}}.
\end{aligned}                                             \tag{CF7.2}
\]
level exponents one、two 的 ambient kernels 及 valuation-one 差核是
\[
 P_1(a,b)={1\over p+1}\sum_{j=0}^1C_j(a)C_j(b),\qquad
 P_2(a,b)={1\over p(p+1)}\sum_{j=0}^2C_j(a)C_j(b),
 \qquad D_p=P_1-P_2.                                    \tag{CF7.3}
\]
直接代入 \(C_j(0)\) 得
\[
 P_1(0,0)={1\over(p+1)\rho_p},\qquad
 D_p(a,0)={\lambda_a-p\lambda_1\lambda_{a-1}/(p+1)
                  \over(p+1)\rho_p}\quad(a\ge1).       \tag{CF7.4}
\]
这里 \(a\ge1\) 是必要条件，也是 corrected lift 的实际范围：
第一 Fourier index 含 shell prime。精确地，CF7.2--CF7.3 还给出
\[
 P_2(a,0)=0\quad(a\ge1),\qquad
 {P_2(0,0)\over P_1(0,0)}={p\over p^2-1}.              \tag{CF7.4a}
\]
因此 CF7.4 不可对 \(a=0\) 使用；后者正是上面 unshifted
ratio 的来源。
corrected squarefree lift 的 local factor 是
\(\mu(p)/c_p(n)\)：除去 CF3.2 已保留的共同 Möbius 符号后，
\(b=v_p(n)=0\) 时为一，\(b\ge1\) 时为 \(-1/(p-1)\)。故 normalized
shell matrix 的**定义**是
\[
 E_p(a,b)=
 \begin{cases}
 D_p(a,0)/P_1(0,0),&b=0,\\
 -D_p(a,b)/((p-1)P_1(0,0)),&b\ge1.
 \end{cases}                                             \tag{CF7.5}
\]
特别地，由 CF7.4 与 Hecke recurrence，若 \(a=1+u\)，则
\[
 E_p(1,0)={\lambda_1\over p+1},\qquad
 E_p(1+u,0)={\lambda_1\lambda_u\over p+1}-\lambda_{u-1}\qquad(u\ge1).
                                                               \tag{CF7.6}
\]

现在只使用 Kim--Sarnak 的公开 unramified bound
\(|\lambda_1|\le p^\theta+p^{-\theta}\)、
\(|\lambda_j|\le(j+1)p^{\theta j}\)、\(\theta=7/64\)。它与
CF7.2 逐项给出
\[
\begin{aligned}
 |C_0(j)|&\ll(j+1)p^{\theta j},\\
 |C_1(j)|&\ll(j+1)p^{1/2+\theta(j-1)},\\
 |C_2(j)|&\ll(j+1)p^{1+\theta(j-2)},
\end{aligned}
\]
其中 \(j=0,1\) 直接读 CF7.2；\(\rho_p\) 一致离零，因为
\(pt_p^2\le p(p^\theta+p^{-\theta})^2/(p+1)^2<1\)。最后一个严格
不等式等价于
\((p-p^{2\theta})(p-p^{-2\theta})>0\)；该上界又趋零，故余下有限
多个 prime 的最小间隙为正。代回 CF7.3--CF7.5
得到
\[
 |E_p(1,0)|\ll p^{-1+\theta},\quad
 |E_p(1+u,0)|\ll(u+2)^Cp^{\theta(u-1)},\qquad
 |E_p(1+u,b)|\ll(u+b+2)^Cp^{\theta(u+b-1)} (b\ge1).
                                                               \tag{CF7.7}
\]
最后令 \(b=r+s\)，并对固定充分小的 \(\eta>0\) 定义
\[
 {\cal N}_p(u)^2=\sum_{r,s\ge0}p^{-r-s+\eta(r+s)}
                         |E_p(1+u,r+s)|^2.               \tag{CF7.8}
\]
每个 \(b\) 有 \(b+1\) 个有序分拆。因 \(2\theta<1\)，CF7.7 的
两个几何级数给
\[
 {\cal N}_p(0)\ll_\eta p^{-1/2+\eta},\qquad
 {\cal N}_p(u)\ll_\eta(u+2)^Cp^{\theta(u-1)+\eta u}\quad(u\ge1),
\]
令 \({\cal Y}_p\) 是坐标 \((r,s)\in\mathbb N_0^2\)、测度
\(p^{-r-s+\eta(r+s)}\) 的 Hilbert 空间，并令
\(K_{p,u}\in{\cal Y}_p\) 的坐标为 \(E_p(1+u,r+s)\)。于是
\(\|K_{p,u}\|_{{\cal Y}_p}={\cal N}_p(u)\)。定义的是如下明确的
valuation-averaged projective mass，而不是未定义的任意系数算子：
\[
 {\mathfrak h}_p:=\sum_{u\ge0}p^{-u}
                         \|K_{p,u}\|_{{\cal Y}_p}
 \ll_\eta p^{-1/2+2\eta}.                              \tag{CF7.9}
\]
矩阵对 \((r,s)\) 的 rank 一致有界，但负指标置零造成的边界
必须显式计入。对任意固定 \(j\ge0\)，令
\(H_j(r,s)=\lambda_{r+s-j}\)，其中负指标为零。当 \(s\ge j\) 时，
Hecke recurrence 给出（置 \(n=s-j\ge0\)）
\[
 \lambda_{r+n}
 =\lambda_n\lambda_r-\lambda_{n-1}\lambda_{r-1}
 =(\lambda_n-\lambda_1\lambda_{n-1})\lambda_r
       +\lambda_{n-1}\lambda_{r+1},
\]
其中 \(\lambda_{-1}=0\)。所以第 \(s\) 列属于第 \(j\) 与第
\(j+1\) 列的张成空间；前 \(j\) 列各至多再增加一维。因此
\[
                         \operatorname{rank}H_j\le j+2.       \tag{CF7.9a}
\]
这个结论也可先对任意有限左上截断证明，上界与截断无关。
CF7.2--CF7.5 中对 \(r+s\) 只出现 \(j=0,1,2\) 的这些 shifts，
而 \(b=0\) 的分段值只再增加一个 rank-one boundary。故整个
局部矩阵的 rank 有与 \(p,u\) 及截断无关的绝对上界；对每个有限
截断，nuclear norm 至多该固定 rank 平方根乘 CF7.8 的
Hilbert--Schmidt norm，然后取截断极限。所以 CF7.9 仍同时控制将
\(h,\delta\) 分开的 nuclear projective mass。

对 squarefree \(A\) 现在可以无歧义地定义
\[
 {\cal Y}_A=\widehat\bigotimes_{p\mid A}{\cal Y}_p,
 \quad K_{A,\boldsymbol u}=\widehat\bigotimes_{p\mid A}K_{p,u_p},
 \quad
 {\mathfrak h}(A)=\sum_{\boldsymbol u\in\mathbb N_0^{\omega(A)}}
       \left(\prod_{p\mid A}p^{-u_p}\right)
       \|K_{A,\boldsymbol u}\|_{{\cal Y}_A}.
\]
Hilbert tensor norm 的乘法性与非负 Tonelli（这里也可先作有限截断）给
\[
 {\mathfrak h}(A)=\prod_{p\mid A}{\mathfrak h}_p
 \ll_\varepsilon A^{-1/2+\varepsilon}.                 \tag{CF7.10}
\]
fixed local ranks 只给 \(C^{\omega(A)}=A^{o(1)}\)。若一个 dyadic
整数区间 \((Z,2Z]\) 含 \(d\) 的倍数，则 \(d\le2Z\) 且其个数至多
\(Z/d+1\le3Z/d\)。分别对 \(\prod p^u\)、\(\prod p^r\)、
\(\prod p^s\) 在 \(k,h,\delta\) 三个坐标各使用一次时，最多产生固定
常数而不是逐 prime 常数。这只是未来 physical adapter 可使用的初等
计数事实；本文没有据此定义或断言一个完整的 normalized global
average。

CF7.10 没有定义或证明一个对任意 \(k\)-系数成立的 global
\(\ell^1\to\ell^2\) operator bound。要用于实际 QCT，必须先把同一
区间内变化的 coefficient/Bessel/complete-shift 权写成与这些
valuation fibers 相容的共同有界列；这正属于 CF19.D/CF19.L。连续谱
也必须先在 ambient oldbasis 的内积恒等式中应用同一计算；CF7.10
不主张单个 ramified Eisenstein oldvector 有逐系数除数界。

## CF8. 共同投影与 CF6.2 的精确接口

CF1.5 的 \(F_\sharp\) 左上块所需的 physical adapter 记为同一个
\(\mathfrak M_\sharp\)。完整 height reassembly 必须在不改变
\(b^\sharp\) 的前提下证明
\[
 \mathfrak M_\sharp=\mathfrak R_\sharp(P)+\mathfrak A_\sharp(P),
 \qquad
 |\mathfrak A_\sharp(P)|
  \ll_\varepsilon B_PT_*^{1+\varepsilon}(1+\log P)^7.   \tag{CF8.1}
\]
其中
\[
 \mathfrak R_\sharp(P)=\mathfrak M_{\rm lo,\sharp}
 +\sum_{V_j\le Y}\omega_j\Re\{
       \mathcal C_{V_j,\sharp}^{\rm bad}
      +\mathcal C_{V_j,\overline\sharp}^{\rm bad}\}.    \tag{CF8.2}
\]
CF8.2 中的每个 \(\mathcal C^{\rm bad}\) 必须解释为 CF6.2 对同一
bad-tag 子集的限制，包括 native complement；它不能逐 box 另作投影。
正负高度只把系数换成
\(b^\sharp,\overline{b^\sharp}\)，核、低表与高度权保持共同。

若另外证明 CF0A.5 的增广残差满足相应小量界，CF1 的范数三角才给
\[
 \mathcal E_{\rho,P,\mathcal L}
 \le 2C_KH^2(\log N)^2\mathfrak R_\sharp(P)
       +O_\varepsilon(XHQ_PP^{a_*+\varepsilon}).         \tag{CF8.3}
\]
因此 CF8.1 与该残差界是从有限共同输出到完整高度的**显式接口
义务**，不是本稿引用本地 SHA 后自动获得的结论。接口一旦成立，
projection top block 便先以 CF1.5 的增广 Gram
精确出现，再通过唯一 \(b^\sharp\) 修正与显式残差进入 CF8.3。
它既未被删除，也未被错误送进一个只有短 shift support 的 QCT box。

## CF9. 当前唯一充分上界及其量词

固定一个假设零点 \(\rho=\beta+i\gamma\)、\(\beta>14/17\)，置
\[
 g=(17\beta-14)/3>0,\qquad \eta=g/4.
\]
先按 CF0A 的参数顺序选择固定 \(K,r_{\rm cut}\)，再固定由此得到的同一个
\(b^\sharp\)。所需且尚未证明的命题是：存在
\(C=C(\rho,\mathcal L,w,\alpha,K,h_0,\eta)\) 与
\(P_0=P_0(\rho,\mathcal L,w,\alpha,K,h_0,\eta)\)，使每个实数
\(P\ge P_0\) 都有
\[
 \boxed{\quad
 \mathfrak M_{\rm lo,\sharp}
 +\sum_{V_j\le Y}\omega_j\Re
   \sum_{\omega\in\Omega^{\rm bad}_{V_j,\sharp}
                    \sqcup\Omega^{\rm bad}_{V_j,\overline\sharp}}
       \frac{2V_j}{q_0RS}C_\omega\mathcal K_\omega
 \le C Q_PT_*P^\eta .
 \quad}                                                   \tag{CF9.1}
\]
这就是本文自含定义的最终 full-output upper gate。特别地：

- \(P\) 必须可在固定 \(\rho\) 后独立趋于无穷；不得只取
  \(P=|\gamma|^{6/17}\)；
- 低高度正积分与 bad signed rows 是同一个左端；只证明高高度
  Kloosterman row 不够；
- all gcd allocations、unit endpoints、mixed cells、noncore boxes、
  transform tails、连续谱 residues 以及未适配的 native complement
  均已是 \(\Omega^{\rm bad}\) 的明示坐标，不能从求和号中静默删除。

若 CF9.1 成立，则 CF8.3 与 XI 的同一输出下界
\[
 \mathcal E/(XHQ_P)\ge c_\rho P^g/\log P
\]
矛盾。固定零点后 \(C,P_0\) 依赖该零点是允许的；若要推出统一的
“充分大高度”定理，仍须证明 CF9.1 的适用阈值可由
\(|\gamma|\ge T_0\) 的统一条件给出，并说明 \(T_0\) 是否有效。

## CF10. 对 signed reciprocity/dispersion 的精确输入

CF3.1 表明可送入 two-sided level transform 的最小向量是
\[
 \mathbf U_{A,B}
  =(\mathcal B,-\gamma_A\mathcal E^L,
                  -\gamma_B\mathcal E^R,
       \gamma_A\gamma_B\mathcal E^{LR}),                \tag{CF10.1}
\]
并须再直和 CF5 的零模/轴坐标、CF4 的四谱型与 Eisenstein 四 residue
坐标、CF1 的有限投影残差坐标。reciprocity 必须在这个直和空间上
先作用，再作一次 TT* 或 Cauchy；否则会分别重建正对角。

在 balanced generic 行，双 prime character projector 只给合同
\(xt-yk-j\equiv0\pmod{pq}\)，留下
\(|\ell|\ll P^{5/6+\varepsilon}\) 个 aliases。故合法目标不是普通
varying-modulus large sieve，而是保留 \(\ell=0\) selector 的向量值
估计：在 CF10.1 的共同系数下，使两个 critical shell incidence
成为与短索引 \(pt\) 独立的正交输出，并在重组 quotient 前获得
\(P^{-1/12+\varepsilon}\) contraction。现有非振荡 two-point kernel
无法分辨 \(j_0=j+rkt\) 的 \(r\ne0\) aliases；若用 support width
强行分辨，会付 \(P^{O(1)}\) 而失去目标 saving。

因此下一步不再是“补一个 scalar Kuznetsov first moment”。它是：
对 CF6.2/CF10.1 的实际有限向量，构造能看见 \(\ell=0\) 的 oscillatory
two-sided level reciprocity，或者在算术侧直接证明同一 zero-alias
dispersion。任何证明都必须同时给出 low-height 行的 CF9.1 预算。

## CF11. zero-alias 有一个精确共享 Fourier 投影

上一节的 \(\ell=0\) selector 不必用长度 \(P^{5/6}\) 的正和表示。
固定不同素数 \(p,q\)，且所有 \(a,b,t,k,j\) 对 \(pq\) 为单位。
写 \(e(x)=e^{2\pi ix}\)。有限角色正交与
\(\int_0^1e(\alpha n)d\alpha={\bf1}_{n=0}\) 给出精确恒等式
\[
\boxed{\begin{aligned}
 {\bf1}_{pat-qbk=j}
 ={}&\frac1{(p-1)(q-1)}
 \sum_{\chi\ ({\rm mod}\ q)}\sum_{\psi\ ({\rm mod}\ p)}
   \chi(pat\bar j)\psi(-qbk\bar j)\\
 &\times\int_0^1
 e\!\left(\alpha\left{
        \frac{at}{q}-\frac{bk}{p}-\frac{j}{pq}\right}\right)d\alpha .
\end{aligned}}                                             \tag{CF11.1}
\]
证明如下。角色和先强制
\(pat\equiv j\pmod q\) 与 \(qbk\equiv-j\pmod p\)。因 \(p\ne q\)，
此时
\[
 \ell=\frac{pat-qbk-j}{pq}\in\mathbb Z.
\]
积分恰为 \({\bf1}_{\ell=0}\)，而括号中的相位就是 \(\ell\)。
若原等式成立，两个合同与积分条件反向全成立，所以没有只证明单向。
角色因子进一步准确分成
\[
 \chi(p)\chi(at)\overline{\chi(j)}\,
 \psi(-1)\psi(q)\psi(bk)\overline{\psi(j)}.             \tag{CF11.2}
\]
这保留 cross-prime kernel \(\chi(p)\psi(q)\)，没有把它取模。

共享 \(\alpha\) 还有一个任意长度的精确 isometry。对素数 \(q\)
及任意有限、支撑在 \((n,q)=1\) 上的复系数 \(u_n\)，
\[
 \boxed{\quad
 \frac1{q-1}\sum_{\chi\ ({\rm mod}\ q)}
  \int_0^1\left|\sum_nu_n\chi(n)e(\alpha n/q)\right|^2d\alpha
       =\sum_n|u_n|^2 .
 \quad}                                                   \tag{CF11.3}
\]
展开平方后角色平均强制 \(n-m=q\ell\)，共享 Fourier 积分再强制
\(\ell=0\)。所以 CF11.3 没有通常 varying-modulus large sieve 的
\(N/q\) alias 项，也不要求 \(N<q^2\)。向量值版本由在任意正交基
逐坐标应用同一有限等式得到。

CF11.1--CF11.3 给出一个合法的 joint Möbius dispersion 坐标：
CF10.1 的全部有限 tags 可以作为向量坐标，\(at\) 与 \(bk\) 分别使用
同一个 \(\alpha\)，并保留两侧角色与 outer-prime 坐标。它优于直接
丢掉 \(\ell\ne0\) 后为每个 alias 取绝对值。

## CF12. 分别 Cauchy 仍精确留下 \(P^{-1/12}\) 缺口

CF11.3 本身不是所需 contraction。若在 CF11.1 后立即对左右两个
角色--Fourier transforms 分别使用 Cauchy，CF11.3 把两边各自化为
原 product-coefficient energy。主对角并未在 CF10.1 的共同
principal/axis/endpoint matrix 中先扣除。因而在 §395 的 balanced
generic 尺度上，这一步返回
\[
                    P^{11/6+\varepsilon},                \tag{CF12.1}
\]
即原 diagonal exponent；目标 centered operator 只允许
\[
                    P^{7/4+\varepsilon}.                 \tag{CF12.2}
\]
二者的准确差仍为
\[
                    \frac{11}{6}-\frac74=\frac1{12}.    \tag{CF12.3}
\]
所以共享 Fourier 投影解决的是 \(P^{5/6}\) aliases 的**精确表示**，
不是 centered cancellation。合法的下一命题必须在一次 Cauchy 前
证明：CF10.1 的共同有限 matrix 在 CF11.1 的共享
\((\chi,\psi,\alpha)\) 空间中，扣除 physical diagonal 与全部
principal/axis/residue rows 后，算子范数至多
\(P^{-1/12+\varepsilon}\)。这比 `SHORT-SEQUENCE-ZERO-ALIAS-INTERTWINER`
更精确，因为 selector 与其无 alias 的单边 isometry 已由
CF11.1--CF11.3 实际证明；剩下的是共同 centered cross-operator，
而非普通 large-sieve capacity。

## CF13. 现有 Kloosterman 双线性定理与共同输出并不等价

Blomer--Pascadi 的 Theorem 1.1
([arXiv:2607.24311v1](https://arxiv.org/html/2607.24311v1)) 对固定模数
\(c\)、两个长度至多 \(N\le c\) 的区间及任意系数证明
\[
 \sum_{m,n}\alpha_m\beta_nS(am,n;c)
 \ll \|\alpha\|_2\|\beta\|_2c^{1+o(1)}
 \left({N^{1/8}\over c^{3/32}}
      +{N^{5/16}\over c^{3/16}}
      +{N^{2/3}\over c^{7/18}}\right),                 \tag{CF13.1}
\]
并在 \(N=c^{1/2}\) 时相对平凡界节省 \(c^{-1/32}\)。把
\(c=AB=P^{11/6}\) 代入只给 \(P^{-11/192}\)，小于所需
\(P^{-1/12}=P^{-16/192}\)，准确还差 \(P^{5/192}\)。更重要的是
CF13.1 是固定模数的正 \(\ell^2\) 范数界；它不含 CF10.1 的两种
shell orientation、共同 principal deletion 或 signed \((p,q)\) 重组。

Pascadi 的 Theorem 1.2
([arXiv:2511.08445v1](https://arxiv.org/html/2511.08445v1)) 对
\(c=dd'e\)、\(d'\mid d\)、\((d,e)=1\) 及
\(f^2\mid cd\) 的最大 \(f\) 给固定模数因子
\[
 \left({f\over\min(c,d^2)}\right)^{1/6}.               \tag{CF13.2}
\]
在理想 squarefree reduced cell
\[
 c=qb_0=P^{23/12},\quad d=f=q=P,\quad e=b_0=P^{11/12}
\]
时，CF13.2 是 \(b_0^{-1/6}=P^{-11/72}\)，数值上超过
\(P^{-1/12}\)。这说明缺口不是没有可用的固定模数 power saving。
但源定理的左端仍是一个固定 \(c\) 的正 Kloosterman 双线性型，且一般
区间带 \((m,n,c)=1\) 条件；它没有在一次范数之前同时保留
CF11.1 的共享 \(\alpha\)、cross-prime 核 \(\chi(p)\psi(q)\)、
两侧 valuation-one shell 和 CF10.1 的四行中心化矩阵。逐模数或逐
orientation 套用会回到 CF12 的两个正对角，不能引用 CF13.2 宣布闭合。

Milićević--Qin--Wu 的 Theorem 1.1
([arXiv:2511.07550v1](https://arxiv.org/html/2511.07550v1)) 对任意固定
模数 \(c\) 与任意两列系数给出的 saving 因子是
\[
 M^{-1/2}c^{1/6}
 +M^{-3/25}N^{-3/10}c^{1/5}
 +(MN)^{-3/16}c^{11/64}.                              \tag{CF13.3}
\]
在本线最有利的对称代入
\(M=N=c^{1/2}\)、\(c=AB=P^{11/6}\) 后，三项分别为
\[
 c^{-1/12},\qquad c^{-1/100},\qquad c^{-1/64}.
                                                               \tag{CF13.4}
\]
因此整体只能取最弱的
\[
 c^{-1/100}=P^{-11/600},                                \tag{CF13.5}
\]
而 CF12.3 要求 \(P^{-1/12}=P^{-50/600}\)。精确缺口为
\[
                       P^{39/600}=P^{13/200}.             \tag{CF13.6}
\]
源定理的三个适用条件在 \(M=N=c^{1/2}\) 时都成立，所以这不是
超出适用域造成的失败；失败来自定理三项之和中后两项太弱。它的对象
仍是单个固定 \(c\) 的正 \(\ell^2\) 双线性型，也没有 CF10.1 的
signed varying-level/common-projection 坐标。其 twisted-\(L\) 应用的
平均误差并不会改变本处原双线性定理的最弱项。

同一论文的 factorable-modulus Theorem 2.1 则给出一个可严格划出的
正面子域。它允许任取除数 \(s\mid c\)；在
\(M=N=c^{1/2}\) 时，其三项 saving 化为
\[
 c^{-1/4}s^{1/2},\qquad c^{-1/4}s^{1/4},\qquad s^{-1/4}.
                                                               \tag{CF13.7}
\]
写 \(s=c^\theta\)。因为
\[
 P^{-1/12}=c^{-1/22}\qquad(c=P^{11/6}),                 \tag{CF13.8}
\]
CF13.7 的每一项都不大于目标，当且仅当
\[
             {2\over11}\le\theta\le {9\over22}.          \tag{CF13.9}
\]
若要吸收源定理的 \(c^\varepsilon\)，须在两个端点内留下固定正
margin。特别地，若 \(c\) 有 \(s\asymp c^{1/3}\)，三项依次为
\[
 c^{-1/12},\qquad c^{-1/6},\qquad c^{-1/12},
\]
故相对于 \(P\) 得到 \(P^{-11/72}\)，比所需 \(P^{-1/12}\) 多出
\(P^{-5/72}\) 的余量。这个结论只支付**已经具有 CF13.9 除数的固定
shell 模数**。一般 \(c=AB\) 可以由两个 rough squarefree levels
组成而没有该尺度的除数；源定理也仍是固定模数正范数，不能据此
恢复 CF10.1 的带符号 varying-level/common-projection 输出。

这个 factorable/rough 分割还有一个完全初等的反向描述。固定
\(0<\delta<5/44\)。若整数 \(c>1\) 没有除数落在
\[
 [c^{\,2/11+\delta},c^{\,9/22-\delta}],                 \tag{CF13.10}
\]
则必有素数 \(r\mid c\) 满足
\[
 r>c^{\,5/22-2\delta}
   =P^{\,5/12-(11/3)\delta}\qquad(c=P^{11/6}).           \tag{CF13.11}
\]
证明只需把 \(c\) 的素因子按任意次序逐个相乘，并取第一个达到
\(c^{2/11+\delta}\) 的部分积。若每个素因子都不超过
\(c^{5/22-2\delta}\)，这个首次越界的部分积至多
\[
 c^{2/11+\delta}c^{5/22-2\delta}
 =c^{9/22-\delta},
\]
与 CF13.10 矛盾。于是 CF13.9 的补集可缩成一个带显式大素因子的
rough-shell 问题。CF13.11 本身不是新的 saving：该素因子的
valuation-one half-root 已在 CF7 的共同基线中计过一次，不能再乘。
它只给后续 rough-modulus joint estimate 一个不重不漏的输入分层。

Milićević--Qin--Wu 的 rough-modulus Theorem 2.2 不能支付这个新
补集。其分解写作 \(c=c^\star\rho\)，其中 \(c^\star\) 是一个素数
或两个素数之积。在 \(M=N=c^{1/2}\) 时，三个 saving 中最后一项为
\[
 (MN)^{-3/16}c^{11/64}\rho^{9/64}
   =c^{-1/64}\rho^{9/64}\ge c^{-1/64}.                  \tag{CF13.12}
\]
即使最理想的 \(\rho=1\)，这也只给
\[
 c^{-1/64}=P^{-11/384},
\]
而目标为 \(P^{-1/12}=P^{-32/384}\)，源定理显示的上界还差
\[
                            P^{21/384}=P^{7/128}.         \tag{CF13.13}
\]
因此 CF13.11 的大素因子不能经 Theorem 2.2 自动兑换成目标 saving；
CF13.12--CF13.13 否定的是该现有上界的充分性，不是构造了实际和的
下界或 rough-shell no-go。

所以这些原始定理分别给出“数值不足的全模数固定层”和“数值足够但
对象不匹配的特殊分解固定层”。它们都是 CF12 后续 joint operator 的
局部输入，不是该 operator 本身。

## CF14. 有限秩中心化不能收缩 zero-alias 匹配算子

CF11 还允许严格排除一种看似可能的免费节省。令 \(U,V\) 为有限集，
\(\phi:U\to V\) 为单射，并定义部分置换
\[
 (T_\phi f)(\phi(u))=f(u),\qquad
 (T_\phi f)(v)=0\quad(v\notin\phi(U)).                  \tag{CF14.1}
\]
则 \(\|T_\phi f\|_2=\|f\|_2\)。设 \(E\subset\ell^2(U)\)、
\(F\subset\ell^2(V)\) 分别是余维不超过 \(r,s\) 的中心化子空间。
若
\[
                         |U|>r+s,                         \tag{CF14.2}
\]
则
\[
             \boxed{\ \|P_FT_\phi P_E\|_{E\to F}=1\ }. \tag{CF14.3}
\]
这里 \(P_E,P_F\) 是正交投影。证明只用有限维线性代数：在 \(E\) 上
考虑
\[
 f\longmapsto P_{F^\perp}T_\phi f .                    \tag{CF14.4}
\]
其定义域维数至少 \(|U|-r\)，秩至多 \(s\)，由 CF14.2 有非零核向量
\(f\)。于是 \(f\in E\)、\(T_\phi f\in F\)，从而 CF14.3 的左端至少
为 1；CF14.1 又给出至多 1。

对固定 \((p,q,j)\)，取允许乘积区间内满足
\[
                         pu-qv=j                          \tag{CF14.5}
\]
的 \(u\) 为 \(U\)，并令 \(\phi(u)=(pu-j)/q\)。CF11.1 的
角色--共享 Fourier 投影正是 CF14.1 的一个酉坐标表示。balanced
尺度上 \(|U|\asymp A^2/P=P^{5/6}\)。因此删除固定个数，乃至
\(P^{o(1)}\) 个 projection/principal/axis 线性方向后，匹配块仍有
范数 1。这个结论也允许每个有限 tag 取值于一个固定维 Hilbert 空间；
逐坐标使用同一维数论证即可。

CF14.3 **不是**实际 QCT 系数的反例：实际向量由 Möbius divisor
convolution、valuation-one incidence、outer Riesz prime weights 和
同一 Bessel kernel 共同产生，未证明它能遍历 CF14 的任意向量。
它严格证明的是：CF11 的 exact alias removal、isometry 与任何有限秩
中心化本身都不能推出 \(P^{-1/12}\)。所需 contraction 必须使用这个
实际算术子空间的额外结构，并在一次 Cauchy 前与 CF10.1 的 signed
matrix 相互作用。换言之，下一命题不应再写成 coefficient-uniform 的
centered matching bound；它必须明确限制为 CF6.2 产生的实际共同列。

## CF15. 实际 Riesz 素数权的 varying-modulus 四阶矩支付一侧缺口

CF14 排除的是任意系数定理；实际反证系数有额外结构。固定
\(\rho,w\) 后，BK1--BK3 的 PNT 渐近给
\[
 S_Y:=\sum_{P<p\le2P}|Y_p|^2>0,
 \qquad
 M_Y:=\max_{P<p\le2P}|Y_p|^2
 \ll_{\rho,w}{\log P\over P}S_Y.                       \tag{CF15.1}
\]
这里常数允许依赖固定 \(\rho\)，与 XI/CF9 的量词一致。令
\[
 \mathcal P_q(\chi)=\sum_{P<p\le2P}Y_p\chi(p),\qquad
 \mathcal T_{q,a,\alpha}(\chi)
   =\sum_t W(t/A)\chi(t)e(\alpha at/q),                \tag{CF15.2}
\]
其中 \(q\) 也遍历该区间内的素数，\(A=P^{11/12}\)，
\(1\le a\le A\)，\(0\le\alpha\le1\)，而 \(W\) 是固定光滑紧支撑权。
Dirichlet 角色在 \(p=q\) 时自动给零，所以
\(\mathcal P_q\) 可用同一个、与 \(q\) 无关的系数列定义。

有如下实际权平均，而不是逐 \(q\) 的 coefficient-uniform 估计：
\[
 \boxed{\quad
 \sum_{P<q\le2P}|Y_q|^2{1\over q-1}
  \sum_{\substack{\chi\ ({\rm mod}\ q)\\\chi\ne\chi_0}}
   |\mathcal P_q(\chi)\mathcal T_{q,a,\alpha}(\chi)|^2
 \ll_{\rho,w,W,\varepsilon}
 A P^\varepsilon S_Y^2 .\quad}                         \tag{CF15.3}
\]

证明不使用素数角色和的逐点估计。先令
\[
 c_n=\sum_{p_1p_2=n}Y_{p_1}Y_{p_2}.                    \tag{CF15.4}
\]
素数唯一分解给
\[
 \sum_n|c_n|^2
 =\sum_p|Y_p|^4+4\sum_{p_1<p_2}|Y_{p_1}Y_{p_2}|^2
 =2S_Y^2-\sum_p|Y_p|^4\le2S_Y^2.                       \tag{CF15.5}
\]
对支撑于 \(n\le4P^2\) 的 CF15.4 使用 primitive Dirichlet 大筛。
因素数模数的非主角色全为 primitive，且
\((q-1)^{-1}=q^{-1}q/\varphi(q)\le P^{-1}q/\varphi(q)\)，得到
\[
 \sum_{P<q\le2P}{1\over q-1}
  \sum_{\chi\ne\chi_0}|\mathcal P_q(\chi)|^4
 =\sum_q{1\over q-1}\sum_{\chi\ne\chi_0}
       \left|\sum_nc_n\chi(n)\right|^2
 \ll P S_Y^2.                                          \tag{CF15.6}
\]
常数中的 \((2P)^2+4P^2\) 已除以外面的 \(P\)；没有把模数个数
再乘一次。

CF15.7 所需的均匀性不能在原 \(t\)-和上对
\(e(\alpha at/q)\) 作 Abel 求和：其总变差最坏为
\(aA/q\asymp A^2/P\)，会丢掉固定幂。正确的顺序是先作一次
exact Gauss--Poisson。置
\[
 \widehat W(\xi)=\int_{\mathbb R}W(x)e(-x\xi)\,dx,
 \qquad \beta=\alpha a,\qquad B_q={q\over A}.
\]
对素数 \(q\) 的每个非主角色 \(\chi\)，因其 primitive，有
\[
 \sum_{r\ ({\rm mod}\ q)}\chi(r)e(kr/q)
   =\tau(\chi)\overline\chi(k),
 \qquad |\tau(\chi)|=\sqrt q.
\]
在每个剩余类 \(r+q\mathbb Z\) 上作 Poisson，有绝对收敛的精确式
\[
 \boxed{\quad
 \mathcal T_{q,a,\alpha}(\chi)
 ={A\tau(\chi)\over q}
   \sum_{k\in\mathbb Z}\overline\chi(k)
     \widehat W\!\left({k-\beta\over B_q}\right).
 \quad}                                                   \tag{CF15.7a}
\]
因此 additive twist 只把长度 \(B_q=q/A\) 的对偶窗中心平移到
实数 \(\beta\)；它不进入对偶权的变差。
[Cochrane--Shi Theorem 1](https://www.math.ksu.edu/~cochrane/research/xyequvmodm.pdf)
对素数模数的特例正是，对任意整数起点 \(K\) 与
\(1\le L\le q\)，
\[
 {1\over q-1}\sum_{\chi\ne\chi_0}
   \left|\sum_{K<k\le K+L}\chi(k)\right|^4
 \ll L^2(\log q)^{12}.                                  \tag{CF15.7b}
\]
这里的 12 只是把原定理中对 prime \(q\) 的
\((\log q)^3(\log\log q)^7\) 粗略放大后的整数幂。将对偶和按
\[
 |k-\beta|\le B_q,\qquad
 2^{j-1}B_q<|k-\beta|\le2^jB_q
\]
分块。在 \(2^jB_q\le q/2\) 的块上，对 \(\chi\) 和用
CF15.7b，再只对已经对偶化的权
\(\xi\mapsto\widehat W((\xi-\beta)/B_q)\) 作分部求和，
该块的四阶均值范数至多
\[
 \ll_{W,J}(2^jB_q)^{1/2}(\log q)^3\,2^{-jJ}.
\]
对 \(\widehat W\) 的一致 Schwartz 界使这些范数可求和。而
\(|k-\beta|>q/2\) 的整个尾绝对值为
\[
 \ll_{W,J}B_q(q/B_q)^{-J+1}=B_qA^{-J+1};
\]
取固定 \(J>3\) 就远小于主界。Minkowski 因而给出
\[
 {1\over q-1}\sum_{\chi\ne\chi_0}
 \left|\sum_k\overline\chi(k)
     \widehat W\!\left({k-\beta\over B_q}\right)\right|^4
 \ll_{W,J}B_q^2(\log q)^{12},
\]
常数与实数平移 \(\beta\) 无关。代入 CF15.7a 并用
\(|\tau(\chi)|=\sqrt q\)，才得
\[
 {1\over q-1}\sum_{\chi\ne\chi_0}
       |\mathcal T_{q,a,\alpha}(\chi)|^4
 \ll_{W,J}{A^4\over q^2}B_q^2(\log q)^{12}
 =A^2(\log q)^{12},\qquad A<q.                         \tag{CF15.7}
\]
对每个 \(q\) 先在角色变量用 Cauchy，再在 \(q\) 上以
\(|Y_q|^2\) 为测度用 Cauchy；由 CF15.1、CF15.6、CF15.7，左端至多
\[
 A(\log P)^6S_Y^{1/2}
 \left(M_Y\sum_q{1\over q-1}
                    \sum_{\chi\ne\chi_0}|\mathcal P_q(\chi)|^4
 \right)^{1/2}
 \ll_{\rho,w,W}A(\log P)^{13/2}S_Y^2,                \tag{CF15.8}
\]
即 CF15.3。

同一证明有一个不隐藏标签数的正交直和版本。固定整数 \(J>3\)，对
支撑于 \([1,2]\) 的光滑函数置
\[
 {\mathfrak S}_J(W)=\sum_{r=0}^{J+2}\|W^{(r)}\|_{L^1}.  \tag{CF15.9}
\]
CF15.7a--CF15.7b 的对偶分块只使用
\(\widehat W,\widehat W'\) 的 \(J\) 阶衰减；在固定支撑上分部积分
逐项给该常数
\(\ll_J{\mathfrak S}_J(W)\)。因此，对任意有限标签集 \(\Lambda\)、
任意整数 \(1\le a_\lambda\le A\)、\(0\le\alpha_\lambda\le1\) 及
任意 \(W_\lambda\)，若
\[
 T_{q,\lambda}(\chi)=
 \sum_tW_\lambda(t/A)\chi(t)e(\alpha_\lambda a_\lambda t/q),
\]
则逐 \(\lambda\) 使用 CF15.3 后求和，严格得到
\[
 \boxed{\quad
 \sum_q|Y_q|^2{1\over q-1}\sum_{\chi\ne\chi_0}
 |\mathcal P_q(\chi)|^2
 \sum_{\lambda\in\Lambda}|T_{q,\lambda}(\chi)|^2
 \ll_{\rho,w,J}
 A(\log P)^{13/2}S_Y^2
 \sum_{\lambda\in\Lambda}{\mathfrak S}_J(W_\lambda)^2 .
 \quad}                                                   \tag{CF15.10}
\]
这只是 Hilbert 直和，不出现不同 \(\lambda\) 的交叉项，所以常数对
\(|\Lambda|\) 一致。若标签振幅为 \(c_\lambda\)，把它并入
\(W_\lambda\) 后右端只付 \(\sum_\lambda|c_\lambda|^2\)。

CF15.10 可以合法吸收一侧 leading \(C_1\) 的 divisor-output：
对固定 \(n=h\delta\) 的 finite divisor output，Cauchy 给
\[
 \left|\sum_{D\mid n}c_{D,n}\chi(D)\right|^2
 \le\tau(n)\sum_{D\mid n}|c_{D,n}|^2,                   \tag{CF15.11}
\]
而 QCT 支撑上 \(\tau(n)\ll P^\varepsilon\)。只要 quotient/Bessel
权在固定 \((D,n)\) 后属于 CF15.9 的共同光滑族，CF15.10 对这些
正交输出只多付 \(P^\varepsilon\)，不会多付 divisor 个数或一个
新的 \(A\)。这关闭的是**一侧正交 divisor tags**。它不把物理
cofactor \(a_0\) 的 scalar 求和变成正交输出，也不证明另一
orientation 的 \(B_{1,*}\mid h'\delta'\) 与同一 complete-shift
权同时满足 CF15.10；这两个问题仍属于下述 intertwiner。

CF15.3 关闭了旧 §405.10 的**实际 Riesz 权、对 \(q\) 平均后的 scalar
prime--interval leaf**：相对于 Pólya--Parseval 的 \(P S_Y\) 容量，
它把区间费用降到 \(A S_Y\)，即准确得到 \(A/P=P^{-1/12}\)。这不是
把两个独立 second moments 相乘；素数乘积的 fourth moment 在 CF15.6
中只使用了一次。

它还没有关闭 CF12。实际 CF6.2 在送到 CF15.3 前仍需一个 lossless
intertwiner，同时保留两侧 \(C_1\) valuation incidence、CF11.1 的
\(\ell=0\) selector、opposite quotient、CF10.1 四行、local
remainder 与 \(b^\sharp-b\) 的有限投影修正。若先把这些坐标吸收成
任意 \(q\)-依赖系数，CF15.4 的共同素数乘积列立即消失，便又落回
CF14 的范数 1 反例。因此 CF15.3 是新的真实 analytic input，但不是
all-box bound。

## CF16. cross-prime 角色核是精确 contraction

CF11.1 中的 \(\chi(p)\psi(q)\) 不是一个必须逐项估计的稠密矩阵。
令 \({\cal P}\) 是 \((P,2P]\) 中任意素数子集；其直径严格小于每个
\(p\in{\cal P}\)。在
\[
 {\cal H}=\bigoplus_{p\in{\cal P}}L^2(\widehat{U(p)}),\qquad
 \|f\|_{{\cal H}}^2=\sum_p{1\over p-1}\sum_{\psi\ ({\rm mod}\ p)}
                                      |f_{p,\psi}|^2
 \tag{CF16.1}
\]
上，对任意 \(|\vartheta_{p,q}|\le1\) 定义
\[
 ({\cal U}_{\vartheta}f)_{q,\chi}
 =\sum_{p\in{\cal P}}{1\over p-1}
   \sum_{\psi\ ({\rm mod}\ p)}
       \vartheta_{p,q}\chi(p)\psi(q)f_{p,\psi}.          \tag{CF16.2}
\]
角色在非单位处为零，所以 \(p=q\) 项自动为零。则
\[
                    \boxed{\ \|{\cal U}_{\vartheta}\|\le1\ }. \tag{CF16.3}
\]

这是精确有限证明。对固定 \(q\) 展开 CF16.2 的平方并平均 \(\chi\)。
若 \(p,p'\in(P,2P]\) 且 \(p\equiv p'\pmod q\)，则
\(|p-p'|<P<q\)，故 \(p=p'\)。因此
\[
 \|{\cal U}_{\vartheta}f\|_{{\cal H}}^2
 \le\sum_p\sum_{q\ne p}
 \left|{1\over p-1}\sum_\psi\psi(q)f_{p,\psi}\right|^2. \tag{CF16.4}
\]
对固定 \(p\)，不同 \(q\in(P,2P]\setminus\{p\}\) 在 \(U(p)\) 中
给出不同剩余类：否则 \(|q-q'|<P<p\) 又强制 \(q=q'\)。它们只是
完整剩余类 Fourier 变换的一组坐标。Parseval 遂给
\[
 \sum_{q\ne p}
 \left|{1\over p-1}\sum_\psi\psi(q)f_{p,\psi}\right|^2
 \le {1\over p-1}\sum_\psi|f_{p,\psi}|^2,              \tag{CF16.5}
\]
合计即 CF16.3。若 \(P_{\rm np}\) 是逐模数删去主角色的正交投影，
则
\[
          \|P_{\rm np}{\cal U}_{\vartheta}P_{\rm np}\|\le1             \tag{CF16.6}
\]
由投影收缩立即成立；没有把 full-character 正交式误写成非主角色
自身的精确正交式。

在 CF11.1 中取
\(\vartheta_{p,q}=e(-\alpha j/(pq))\)。因固定 \(q\) 的第一步已经
强制 \(p=p'\)，这个依赖两个素数的相位在 CF16.4 中与其共轭准确
抵消。在 CF11 的单位假设 \((j,pq)=1\) 下，
\(\overline\chi(j),\overline\psi(-j)\) 及固定 cofactor 的
\(\chi(a),\psi(b)\) 都是各角色坐标上的单位对角乘子，也不改变
CF16.6。故 CF11 的 shared Fourier integral、cross-prime kernel 与
两侧非主角色投影合在一起不产生 \(P^{5/6}\) alias 范数损失。

这个结论解释了剩余 intertwiner 的准确位置。若两侧 critical
\(C_1\) incidence 已被送到正交坐标 \(a\) 与 \(b\)，则每个固定
cofactor 的短和
\[
 T_{q,a}(\chi;\alpha)=\sum_tW_a(t/A)\chi(t)e(\alpha at/q) \tag{CF16.7}
\]
只需它自己的二阶 Parseval：当支撑区间长度小于 \(q\) 时，
\[
 {1\over q-1}\sum_\chi|T_{q,a}(\chi;\alpha)|^2
       =\sum_{q\nmid t}|W_a(t/A)|^2\ll A,                \tag{CF16.8}
\]
且非主角色子和只会更小。对正交 \(a\)-坐标求和仍只付其系数平方
能量。这里 \(q\nmid t\) 不能省略：Dirichlet 角色在非单位上为零；
长度小于 \(q\) 只保证单位剩余类互异，不保证支撑不含 \(q\) 的倍数。
CF16.6 再把两侧这种范数配对；这正保留 \(A/q=P^{-1/12}\)
而无需估计一个长度 \(PA^2\) 的任意公共列。

但现有 complete-shift 等式尚未证明两侧 mixed-Bruhat 的
\(A_{1,*}\mid h\delta\)、\(B_{1,*}\mid h'\delta'\) 同时成为 CF16.7
所需的正交 \(a,b\) 坐标。若先在 scalar output 中求 \(a\)，CF16.8
会变成长乘积列并恢复 CF12 的 \(P^{5/6}\) aliases。因此 CF16.3--CF16.8
关闭的是 shared-phase/cross-prime operator 本身；尚缺的叶子已缩成
**two-sided critical-incidence orthogonalization**，以及证明 CF10.1 的
共同 principal/equal-prime/axis 行恰好先投影到 CF16.6 的非主子空间。
它没有支付 native complement、其他 bad boxes 或 low-height 行。

## CF17. 乘上短和后逐模数分块；非主输入仍可承载任意边数组

CF16.3 不能在乘上 \(\mathcal T_{q,a,\alpha}\) 后直接当作所需
\(\sqrt A\)-级估计。这个边界可由第二个精确坐标变换看清。对每个
\(p\)，令
\[
 g_p(r)={1\over p-1}\sum_{\psi\ ({\rm mod}\ p)}
                  \psi(r)f_{p,\psi},\qquad r\in U(p).     \tag{CF17.1}
\]
角色 Parseval 把 CF16.1 变成
\(\sum_p\sum_{r\in U(p)}|g_p(r)|^2\)。再把输出角色作逆变换。
若
\[
 T_q(\chi)=\sum_t w_t\chi(t)e(\alpha at/q),
\]
则乘积 \(T_q(\chi)({\cal U}_\vartheta f)_{q,\chi}\) 在
\(x\in U(q)\) 坐标上的值，除去不影响范数的共轭约定，恰为
\[
 \sum_{\substack{p\in{\cal P},\,t\\pt\equiv x\ ({\rm mod}\ q)}}
   w_t e(\alpha at/q)\vartheta_{p,q}\,g_p(q),\qquad x\in U(q).
                                                               \tag{CF17.2}
\]
这个同余自动强制 \(q\nmid t\)，但下面的中心项也必须显式使用同一
单位支撑。
所以组合算子按 \(q\) **完全分块**。输出的非主投影在这些剩余类
坐标中只是扣除常数向量；相应的固定 \(q\) 矩阵是
\[
 C_q^0(x,p)=
 \sum_{\substack{t\\pt\equiv x\ ({\rm mod}\ q)}}
       w_t e(\alpha at/q)\vartheta_{p,q}
 -{1\over q-1}\sum_{q\nmid t}
       w_t e(\alpha at/q)\vartheta_{p,q}.                 \tag{CF17.3}
\]
例如 \(q=5\) 且唯一非零权为 \(w_5=1\) 时，真实角色短和恒为零；
若在 CF16.8 或 CF17.3 的中心项中错误保留 \(t=5\)，会分别得到假的
右端 \(1\) 或假的常数列 \(-1/4\)。这也是单位限制不可由短区间长度
替代的有限反例。

输入非主投影也不会强迫不同 \(q\) 的边值相关。固定 \(p\)，令
\({\cal Q}_p={\cal P}\setminus\{p\}\)，\(m_p=|{\cal Q}_p|\)。
CF16 的注入性说明 \({\cal Q}_p\) 给出 \(U(p)\) 中 \(m_p\) 个互异
坐标。给定任意 \(z_{p,q}\)，在这些坐标上置
\(g_p(q)=z_{p,q}\)，并在其余 \(p-1-m_p\) 个坐标上置共同值
\[
 -{\sum_{q\in{\cal Q}_p}z_{p,q}\over p-1-m_p}.           \tag{CF17.4}
\]
则 \(\sum_{r\in U(p)}g_p(r)=0\)，故对应角色向量没有主角色坐标，而且
\[
 \sum_{r\in U(p)}|g_p(r)|^2
 \le {p-1\over p-1-m_p}\sum_{q\in{\cal Q}_p}|z_{p,q}|^2.
                                                               \tag{CF17.5}
\]
这里 \({\cal P}\subset(P,2P]\) 且除至多一个素数 \(2\) 外全为奇数，
故对充分大 \(P\) 有 \(m_p\le(P+1)/2<p-1\)，CF17.5 的因子至多一个
绝对常数。因而 coefficient-uniform 的
\(P_{\rm np}M_T{\cal U}_\vartheta P_{\rm np}\) 范数，与最坏固定
\(q\) 的 centered incidence 矩阵 \(C_q^0\) 范数在绝对常数内等价；
对 \(q\) 的 varying-level 求和本身没有提供额外 power saving。

这不否定 CF15：CF15 的输入不是任意 \(z_{p,q}\)，而是同一个实际
Riesz 列 \(Y_p\)，其 \(q\)-平均还使用 CF15.1 的平坦性和一次
prime-product 大筛。CF17 精确说明不能先把 opposite quotient、
两侧 \(C_1\) incidence 或 Möbius 列吸收到任意
\(f_{p,\psi}\)，再指望 CF16 免费保留 CF15 的 \(A/q\)。
剩余命题必须在 CF17.2 之前证明实际两侧系数仍属于 CF15 的共同
prime-product 类，或直接证明该实际子空间上的 centered
\(C_q^0\) 加权均方；这正是 two-sided critical-incidence
orthogonalization 的解析内容。

## CF18. 固定 cofactor 的短逆边只有 \(A\) 条；平方能量与算子范数不可混用

CF17 的任意边数组反例没有使用实际 Riesz 平坦性。固定整数
\(b,j\)，并设对所有 \(p\in{\cal P}\) 都有 \((bj,p)=1\)。令
\(I_p\subset\mathbb Z\) 是落在一个长度严格小于 \(p\) 的整数区间内的
有限集，且 \(|I_p|\le A<P\)。对 \(p\ne q\) 定义短逆边
\[
 E_{p,q}^{b,j}(w)=
 \sum_{k\in I_p}w_{p,q}(k)
       {\bf1}_{qbk\equiv-j\ ({\rm mod}\ p)}.              \tag{CF18.1}
\]
同余式若可解，则 \(k\pmod p\) 唯一；因 \(I_p\) 的直径小于 \(p\)，
CF18.1 至多有一个非零求和项。反过来固定 \(p,k\) 时，两个素数
\(q,q'\in(P,2P]\) 若都满足同余式，则 \(q\equiv q'\pmod p\)。又
\(|q-q'|<P<p\)，所以 \(q=q'\)。因此每个固定 \(p\) 至多有
\(|I_p|\le A\) 个非零的 \(q\)-边。

若有任意有限的正交标签集 \(\Lambda\)，并且在每条允许边上
\[
 \sum_{\lambda\in\Lambda}|w_{p,q,\lambda}(k)|^2\le B,
                                                               \tag{CF18.2}
\]
则对任意素数权 \(Y_p\)，逐边使用上述注入性给出精确有限估计
\[
\begin{aligned}
 &\sum_{\substack{p,q\in{\cal P}\\p\ne q}}
   |Y_p|^2|Y_q|^2
   \sum_{\lambda\in\Lambda}
       |E_{p,q}^{b,j}(w_\lambda)|^2\\
 &\qquad\le
 B\sum_p|Y_p|^2
      \sum_{\substack{q:\ E_{p,q}^{b,j}\ne0}}|Y_q|^2
 \le BA M_Y S_Y.                                           \tag{CF18.3}
\end{aligned}
\]
这里 \(S_Y,M_Y\) 如 CF15.1；没有使用角色大筛、素数分布或渐近。
代入实际 Riesz 平坦性便得
\[
 \sum_{p\ne q}|Y_p|^2|Y_q|^2
   \sum_\lambda|E_{p,q}^{b,j}(w_\lambda)|^2
 \ll_{\rho,w} B{A\log P\over P}S_Y^2.                      \tag{CF18.4}
\]
所以在**平方条目能量**层面，短逆稀疏性确实给出所需的
\(A/P=P^{-1/12}\)，且 CF18.2 说明正交有限标签不会暗中再乘标签数。

同一结论适用于 generic unit exact determinant 的固定 \((a,b)\)
子块：另设 \((aj,q)=(bj,p)=1\)，且 \(t\) 限制在直径小于 \(q\)
的区间内，则
\[
                    pat-qbk=j                              \tag{CF18.5}
\]
同时强制
\(pat\equiv j\pmod q\) 与 \(qbk\equiv-j\pmod p\)。固定
\((p,q,a,b)\) 时两个短区间中至多各有一个允许的 \(t,k\)，而
CF18.5 的边集是 CF18.1 边集的子集；故 CF18.3--CF18.4 对加入左侧
短权及共享 zero-alias selector 后仍成立，只需把它们的逐边平方上界
并入 \(B\)。这一步没有把两个同余误当成原等式；只使用了
“原等式的支撑包含于短逆边”这一单向包含来作上界。

若在完整剩余类 Hilbert 空间中先删去主角色，正交投影当然不会增加
CF18.3 的平方能量；但是必须先证明 CF10.1 的 principal/equal-prime/
axis 行正是这个投影所删的共同方向。尚未建立该物理行到剩余类投影的
等式时，不能直接把 CF17.3 的稠密 centered 列替换为 CF18.1 的稀疏列。

CF18.4 仍不是 QCT 的 bilinear bound。令边矩阵的条目为
\(K_{p,q,\lambda}=Y_p\overline{Y_q}E_{p,q}^{b,j}(w_\lambda)\)，普通
Hilbert--Schmidt 不等式只给
\[
 {\|K\|_{\rm op}\over S_Y}
 \le {\|K\|_{\rm HS}\over S_Y}
 \ll B^{1/2}\left({A\log P\over P}\right)^{1/2}.            \tag{CF18.6}
\]
在 \(A=P^{11/12}\) 时，CF18.6 只有
\(P^{-1/24}(\log P)^{1/2}\)，而 CF12.3 需要
\(P^{-1/12+\varepsilon}\)。换言之，若在共同 QCT Gram 型被识别成
CF18.3 的平方能量之前先作一次 Cauchy/算子范数估计，就准确丢掉一半
幂次。要使用 CF18.4 关闭原式，仍须证明 CF6.2/CF10.1 的两侧
critical-incidence 与 principal/equal-prime/axis 四行先组成同一个
平方能量，而不是一个随后才平方的标量双线性型。现有
complete-shift/determinant 等式尚未给出这个 lossless Gram
intertwiner；CF18 因而是一个真实的实际权能量引理及一个精确的
\(P^{-1/24}\) 失败账，不是 CF9.1 的证明。

## CF19. 共享乘积 Fourier 空间的算子值引理

CF16 的标量核有一个严格的算子值扩张，它正好允许两种
mixed-Bruhat 输出不同。对每个 \(p\in{\cal P}\) 取有限维 Hilbert
空间 \({\cal V}_p\)，对每个 \(q\in{\cal P}\) 取 \({\cal W}_q\)，并令
\(\Theta_{p,q}(\alpha):{\cal V}_p\to{\cal W}_q\) 满足
\(\|\Theta_{p,q}(\alpha)\|\le1\)。定义
\[
 ({\cal U}_{\Theta(\alpha)}f)_{q,\chi}
 =\sum_{p\ne q}{1\over p-1}\sum_{\psi\ ({\rm mod}\ p)}
   \chi(p)\psi(q)\Theta_{p,q}(\alpha)f_{p,\psi}.          \tag{CF19.1}
\]
则从
\(\bigoplus_pL^2(\widehat{U(p)};{\cal V}_p)\) 到
\(\bigoplus_qL^2(\widehat{U(q)};{\cal W}_q)\) 有
\[
                  \|{\cal U}_{\Theta(\alpha)}\|\le1.     \tag{CF19.2}
\]
这里每个角色空间都用归一化测度
\((p-1)^{-1}\sum_\psi\) 或 \((q-1)^{-1}\sum_\chi\)。
证明与 CF16.4--CF16.5 完全有限。固定 \(q\) 后角色正交先杀掉
\(p\ne p'\)；逐项使用 \(\|\Theta_{p,q}\|\le1\)；再固定 \(p\)，
不同 \(q\) 在 \(U(p)\) 中给互异坐标，最后用 Hilbert 值 Parseval。
因此任何在抽出 CF11 的 enforcement-character 因子后、与
\(\chi,\psi\) 无关且已独立证明为 norm-one 的 mixed-Bruhat 自伴块都可以
作为 \(\Theta_{p,q}\) 使用；不需要把两种 orientation 错认成同一个
局部剩余类。证明实际块具有这种独立性属于后面的 CF19.L，不能由
抽象范数界反推。

令有限数组 \(u_{q,n}\in{\cal W}_q\)、
\(v_{p,m}\in{\cal V}_p\) 都只支撑在相应模数的单位上，并置
\[
\begin{aligned}
 G_{q,\chi}(\alpha)
   &=Y_q\sum_nu_{q,n}\chi(n)e(\alpha n/q),\\
 F_{p,\psi}(\alpha)
   &=Y_p\sum_mv_{p,m}\psi(m)e(-\alpha m/p).
                                                               \tag{CF19.3}
\end{aligned}
\]
允许 \(\Theta_{p,q}(\alpha)\) 含标量
\(e(-\alpha j/(pq))\)。CF11.2 中依赖 \(j\) 或符号的角色因子则在
两侧角色空间上组成单位对角算子；它们与 \({\cal U}_\Theta\) 复合不
改变范数，不能误写成 \(\Theta:{\cal V}_p\to{\cal W}_q\) 的一部分。
逐 \(\alpha\) 用 CF19.2，再对 \(\alpha\) 用 Cauchy，最后分别使用
向量值 CF11.3，
得到
\[
\boxed{\quad
 \left|\int_0^1
   \langle G(\alpha),{\cal U}_{\Theta(\alpha)}F(\alpha)\rangle
       d\alpha\right|
 \le
 \left(\sum_q|Y_q|^2\sum_n\|u_{q,n}\|^2\right)^{1/2}
 \left(\sum_p|Y_p|^2\sum_m\|v_{p,m}\|^2\right)^{1/2}.
 \quad}                                                     \tag{CF19.4}
\]
这里不要求整数 \(m,n\) 落在短于模数的区间。以左侧为例，角色
正交先给 \(n\equiv n'\pmod q\)，于是
\((n-n')/q\in\mathbb Z\)；同一个 \(\alpha\)-积分随后把这个整数
强制为零，故恰留下 \(n=n'\)。右侧完全相同。这是角色与共享连续
Fourier 坐标的联合 Parseval，不能删掉 \(\alpha\) 后单独引用。
这里两边的角色空间都含主角色；删除任一主角色子空间只会缩小范数。
CF19.4 不是把两个不相关 second moments 相乘：中间是同一个
cross-prime 算子 \({\cal U}_{\Theta}\)，共享的 \(\alpha\) 在两边只
积分一次。

这个引理也精确容纳 critical divisor 与物理 cofactor 的乘积。
例如令
\[
 u_{q,n}=\sum_{at=n}a^{-1/2}u_{q,a,t}.                    \tag{CF19.5}
\]
有限 Cauchy 在每个乘积 \(n\) 上给
\[
 \sum_n\|u_{q,n}\|^2
 \le \max_n\tau(|n|)
      \sum_{a,t}{\|u_{q,a,t}\|^2\over a}.                \tag{CF19.6}
\]
负的 \(t\) 用 \(|n|\)，\(t=0\) 留在 axis 行。若 \(a\) 在一个
dyadic interval、\(t\) 有长度 \(A_t\)，且归一化向量一致有界，则
右端为 \(A_tP^\varepsilon\)，因为
\(\sum_{a\asymp A_0}a^{-1}\ll1\)。右侧 \(b,k\) 完全相同。
更一般地，把 leading \(C_1\) 的 \(A_{1,*}\mid h\delta\) 作为 \({\cal W}_q\)
中的正交输出，只再付一份 \(\tau(h\delta)\)；另一 orientation 的
\(B_{1,*}\mid h'\delta'\) 可独立放在 \({\cal V}_p\) 中。CF19.1
允许 \({\cal V}_p\ne{\cal W}_q\)，所以不需要先证明两个输出指标相等。

把除短变量外、但已经包含一次 shell 密度的两侧 coefficient energies
记为 \(E_L,E_R\)。CF19.6 在短长度分别为 \(A_t,A_k\) 时把 CF19.4
化为
\[
 |{\cal B}_{\rm prod}|
 \ll P^\varepsilon\sqrt{A_tA_k}\sqrt{E_LE_R}.             \tag{CF19.6a}
\]
把一个另行出现的“完整模数容量”
\(P\sqrt{E_LE_R}\) 放在分母，会形式上得到
\[
 {\sqrt{A_tA_k}\over P};\qquad
 A_t\asymp A_k\asymp P^{11/12} \Longrightarrow P^{-1/12}.
                                                               \tag{CF19.6b}
\]
但这个比值**不是已证明的物理 saving**。CF19.4 正是 CF11.3 后对
左右两侧分别 Cauchy 的算子值版本；CF12.1 已经逐归一化算出同一步
返回原 diagonal exponent \(P^{11/6+\varepsilon}\)，而不是目标
\(P^{7/4+\varepsilon}\)。所以“完整模数容量”与 CF19.6a 的
coefficient energy 尚未被证明是同一个物理基线。把 CF19.6b 记作
收益，会把 exact zero-alias isometry 当成 centered cancellation，
正好重复 CF12 已排除的错误。CF7 的 shell half-root 仍只可各用一次。

若还带 \((a,b)=1\)，使用精确恒等式
\[
                 {\bf1}_{(a,b)=1}=\sum_{d\mid a,\ d\mid b}\mu(d).
                                                               \tag{CF19.7}
\]
固定 \(d\) 后写 \(a=da',b=db'\)。两侧 shell half-root 各产生
\(d^{-1/2}\)，故 CF19.4 的两范数乘积产生 \(d^{-1}\)；求和只付
\(\sum_{d\ll P}d^{-1}\ll\log P\)。所以 genuine-gcd 的单位 mask
不会重新引入一个 cofactor 长度。这个计算使用两侧 half-root 各一次，
没有把 CF7 的局部密度再平方。

CF19.4 展开后确实可以返回原 determinant。采用本文“内积在第二变量
线性”的约定时，在左侧取
\(G_{q,\chi}=Y_q\chi(j)\sum_n\overline{u_{q,n}}\,
\overline\chi(n)e(-\alpha n/q)\)，在右侧取
\(F_{p,\psi}=Y_p\overline\psi(j)\sum_mv_{p,m}\psi(-m)
e(-\alpha m/p)\)。这些只是 CF19.3 的共轭、反射与单位对角变换，
两边范数不变。此时角色平均强制
\(pat\equiv j\pmod q\)、\(qbk\equiv-j\pmod p\)；在这两个同余已成立
之后，共享积分中的频率是整数
\((pat-qbk-j)/(pq)\)，故只保留
\(pat-qbk=j\)。注意若先把 prime polynomial 与 \(at\) 多项式相乘再
平方，角色只给 \(p_1a_1t_1\equiv p_2a_2t_2\pmod q\)，此时
\(a_1t_1-a_2t_2\) 未必被 \(q\) 整除，CF11.3 不能直接使用。
CF19.1 的 cross-prime 次序正是避免这个错误的必要部分。

要把 CF19.4 无损接入一个实际物理 row，至少需要如下可逐字节核对的
分解条件：
其完整系数必须在有限截断上写成
\[
 C_\omega{\cal K}_\omega
 =\sum_{\nu}c_\nu\int_0^1
   \langle G_\nu(\alpha),
      {\cal U}_{\Theta_\nu(\alpha)}F_\nu(\alpha)\rangle d\alpha,
 \qquad
 \sum_\nu|c_\nu|\sqrt{E^L_\nu E^R_\nu}
 \ll P^\varepsilon E_{\rm shell},                         \tag{CF19.8}
\]
其中 \(E^L_\nu,E^R_\nu\) 是 CF19.4 右端的**同一** coefficient
energies，\(E_{\rm shell}\) 已含 CF7 的两侧 shell 密度各一次。
所需 physical adapter 必须给 determinant 与全部 finite tags 的精确
输运；CF7A 给局部 shell 的有限 projective atoms。原始 archimedean
核到同一 normalized 坐标的有限阶一致导数仍属于 CF19.D。对固定紧支撑
光滑部分，CF19.8 的连续变量分离可由
如下有限 Fourier 论证完成：在包住支撑的固定 torus 上展开 Fourier
级数，取 \(s>d/2\)，由 Cauchy--Schwarz、Parseval 与分部积分有
\[
 \sum_{r\in\mathbb Z^d}|\widehat\Phi(r)|
 \le\left(\sum_r(1+|r|^2)^{-s}\right)^{1/2}
    \left(\sum_r(1+|r|^2)^s|\widehat\Phi(r)|^2\right)^{1/2}
 \ll_{d,s}\sum_{|\alpha|\le s}\|\partial^\alpha\Phi\|_{L^2}.
                                                               \tag{CF19.9}
\]
每个 Fourier monomial 在左右归一化坐标中分离。若实际核的相应
Sobolev 半范数已经证明，Schwartz 尾由同一分部积分求和；CF19.9 本身
不证明该实际半范数，也不产生 centered power saving。

下面说明 CF19.8 在最接近实际对象的子族上还差什么。考虑 CF6.2 中
固定 \(q_0,R,S\)、固定 genuine-gcd 输出 \(h\)、balanced generic、
\(p\ne q\)、\(jtk\ne0\) 的 expanded exact-shell 行。固定一个原
dyadic box 与有限截断后，已有的严格步骤只有如下四项。

1. 所需 determinant adapter 必须不改变任何系数地把完整
   physical-shift 核写成
   \(pa_0t-qb_0k=j\)。这里 shell 的第一频率仍是 \(a_0j\) 或
   \(b_0j\)，没有把 \(t,k\) 冒充 shell frequency。
2. 在 balanced generic 支撑上
   \(|j|,|t|,|k|,a_0,b_0<P<p,q\)；因此 CF11 所需单位条件全部成立。
   \((a_0,b_0)=1\) 由 CF19.7 分离，费用 \(P^\varepsilon\)。
3. CF7A 把每侧 exact shell 写成有限 projective atoms，
   总质量分别为 \(a_0^{-1/2+\varepsilon}\)、
   \(b_0^{-1/2+\varepsilon}\)。leading \(C_1\) 因 \(b=1\) 成为
   divisor-output，并由 CF19.6 支付；其他三个 atoms 有更强局部幂次，
   其总和已经包含在同一 projective mass 中。
4. 仍须从原 trace 证明两种 mixed-Bruhat orientation 组成 norm-one
   块。这个局部目标若成立，才允许一个**已经构造出的**跨 level 分块映射作为
   CF19.1 的 \(\Theta_{p,q}\)，但它自身没有构造该映射。本步必须停留
   在 CF4.1 左侧的共同 geometric trace 上；不能把 Maaß parity、
   holomorphic、Eisenstein、diagonal 与 local remainder 擅自宣称为
   正交直和。

原先把这四步直接接到 CF19.10 是不合法的。首先发生了变量同名造成的
误接：原核
\(\Psi(r/R,s/S,\delta/L_h,h/H_M)\) 的归一化导数与 determinant 中
\(G_{x,y,j}(v)=W(v/V)I_{x,y,j}(v)\) 的 \(v\) 是**第二次 Poisson 前的
physical shift** 是不同坐标。代数 determinant 恒等式本身没有证明后一个 \(v\) 的
导数范数。因而还须独立证明
\[
 \sup_{\boldsymbol z}\sum_{0\le \ell+|\eta|\le m}
 \bigl\|(V\partial_v)^\ell\partial_{\boldsymbol z}^{\eta}
   \{W(v/V)I_{x,y,j}(v)\}\bigr\|_{L^2(dv/V)}
 \ll_{m,\varepsilon}P^\varepsilon {\cal S}_m(w),       \tag{CF19.D}
\]
这里 \(\boldsymbol z\) 是实际左右归一化坐标，且常数须一致于
\(p,q,a_0,b_0,j\) 和全部有限 detector/Bessel/AFE tags。CF19.D 才能
通过对 physical \(v\) 分部积分和 CF19.9 给出
\(\widehat G(-t/Q_0)\) 的一致 Schwartz 尾；任何只控制原核坐标的
旧估计都不能代替 CF19.D。

其次，CF7A 只给逐 level 的有限 projective atoms；mixed-Bruhat
norm-one 与 determinant 输运都仍是 adapter obligations。
三者尚未证明所有变化的 \(a_0,b_0\) 纤维可在取正范数前组成同一个
CF19.1 算子，并满足无额外 multiplicity 的能量账。所需的精确命题是
\[
 \sum_{a_0,b_0}\mu(a_0)\mu(b_0){\cal A}_{a_0,b_0}
 =\sum_\nu c_\nu\int_0^1
   \langle G_\nu,{\cal U}_{\Theta_\nu}F_\nu\rangle d\alpha,
 \quad
 \sum_\nu|c_\nu|\sqrt{E^L_\nu E^R_\nu}
 \ll P^\varepsilon{\cal B}_{\rm shell},                 \tag{CF19.L}
\]
其中左边是原带符号 determinant 行，右边的
\(E^L_\nu,E^R_\nu\) 必须逐字等于 CF377.3 已支付一次 shell half-root
后的 energies。特别不能把 \(a_0,b_0\) 的求和藏进
\(\Theta_{p,q}\) 的“有限维”二字。CF19.L 正是尚缺的 two-sided
critical-incidence orthogonalization，而不是逐块 norm-one 的推论。

即使 CF19.D 与 CF19.L 都成立，CF19.4 仍只给 CF12.1 的 diagonal
级别。还须在实际 Riesz/四行中心化子空间上证明真正的压缩。令
\({\cal P}_{\rm full}\) 表示 CF10.1 连同 diagonal、principal、axes、
residue rows 的同一个有符号增广投影；所需的新输入是
\[
 \left|\sum_\nu c_\nu\int_0^1
  \langle G_\nu,
   {\cal P}_{\rm full}{\cal U}_{\Theta_\nu}
   {\cal P}_{\rm full}F_\nu\rangle d\alpha\right|
 \ll P^{-1/12+\varepsilon}
       \sum_\nu|c_\nu|\sqrt{E^L_\nu E^R_\nu}.          \tag{CF19.C}
\]
CF14 证明 CF19.C 对任意 coefficient space 为假；因此其量词必须
限于 CF6.2 的实际 Riesz/Möbius/Bessel 列。CF15 的 actual-Riesz
四阶矩与 CF18 的 weighted edge energy 是可能输入，但二者目前都没有
证明 CF19.L 后的完整四行投影满足 CF19.C。

只有 CF19.D、CF19.L 与 CF19.C 三者都成立，求有限 local atoms、
\(|j|\ll P^\varepsilon\) 与 bounded-overlap smooth pieces 后，才得到
\[
 \boxed{\quad
 |{\cal C}^{\rm exp}_{\rm bal,gen,nonaxis}|
 \ll P^{-1/12+\varepsilon}{\cal B}_{\rm shell},
 \quad}                                                     \tag{CF19.10}
\]
其中
\({\cal B}_{\rm shell}\) 是 CF7/CF377.3 已经使用两侧 half-root
恰各一次后的共同基线。CF19.10 的 saving 全部来自尚未证明的
CF19.C，不能归给 norm-one cross-prime contraction 或 CF19.6b，
也不能再与 CF15 的 fourth moment 相乘。唯一物理外权
\(2T/(q_0RS)\) 在这个条件性推导中始终留在外面。

因此 CF19.10 目前是 **CF19.D+CF19.L+CF19.C 的条件性结论**，并未关闭固定
genuine-gcd cell 的 balanced generic expanded nonaxis
two-sided critical-incidence/zero-alias leaf。即使补齐这三个命题，
它仍不覆盖跨
\(h,q_0,R,S\) 的物理重组、equal-prime、
quotient \(k=0\)、physical \(t=0\) 或 \(k=0\) axes、top ramified、
unit endpoints、未展开的 other-character/non-squarefree/nonflat/
unequal-gcd native rows，也不覆盖 low-height expanding band。

CF19.D 中纯 affine-lattice 的 physical-shift 部分可以单独闭合。不过
短移位必须作为一个显式归一化坐标保留，不能
藏进一个据称有 product-scale 导数界的二变量函数。设
\(\Phi(d,c,\alpha)\) 在前两个坐标支撑于长度分别为 \(D,C\) 的固定
倍长区间，并在 \(\alpha\) 的固定紧集支撑。定义
\[
 \mathfrak N_m^{\rm sh}(\Phi)=
 \max_{i+j+k\le m}D^iC^j
   \|\partial_d^i\partial_c^j\partial_\alpha^k\Phi\|_\infty.
\]
令 \(P_0,Q_0\) 互素，固定整数 \(j\)，并置
\[
 I_j(v)={1\over Q_0}\int_{\mathbb R}
 \Phi\!\left(x,{P_0x-v\over Q_0},{v\over V}\right)
 e(-jx/Q_0)\,dx,
 \qquad G_j(v)=W(v/V)I_j(v).                         \tag{CF19.11}
\]
若 \(V\le Q_0C\)，则对每个 \(0\le\ell\le m\)
\[
 \|(V\partial_v)^\ell G_j\|_\infty
 +\|(V\partial_v)^\ell G_j\|_{L^2(dv/V)}
 \ll_{m,W}{D\over Q_0}\mathfrak N_m^{\rm sh}(\Phi), \tag{CF19.12}
\]
并对每个 \(N\le m\)
\[
 |\widehat G_j(\xi)|
 \ll_{N,W}V{D\over Q_0}\mathfrak N_N^{\rm sh}(\Phi)
                   (1+V|\xi|)^{-N}.                    \tag{CF19.13}
\]
证明是直接的。在被积函数上
\[
 V\partial_v=-{V\over Q_0}\partial_c+\partial_\alpha.
\]
第一项相对于 \(C\partial_c\) 的归一化费用为
\(V/(Q_0C)\le1\)，第二项本来就是归一化短移位导数；落在
\(W(v/V)\) 时费用也是常数。\(x\)-积分长度 \(O(D)\)，而 \(W\)
使 \(v/V\) 支撑固定，给 CF19.12。对
CF19.11 在 \(v\) 上分部积分 \(N\) 次并与零次界取小者，给
CF19.13，全部边界项因 \(W\) 消失。这是解析证明，不是有限检查。

三变量写法是必要的。若原权含
\(\Omega((P_0d-Q_0c)/V)\)，把它硬塞进二变量 \(F(d,c)\) 会给
\(C\partial_cF\) 一个 \(Q_0C/V\) 因子；此时二变量半范数并非
power-free。CF19.11 把该因子放回 \(\alpha\) 坐标，沿仿射格
\(P_0d-Q_0c=v\) 后恰由 \(V\partial_v\) 支付。\(\Phi\) 与
\(\alpha\) 无关时，旧的二变量陈述只是本引理的特例。

在 balanced generic 物理尺度
\[
 D\asymp {R\over ha_0},\quad C\asymp {R\over hb_0},\quad
 Q_0=qb_0,\quad V\asymp {H\over h},
\]
有
\[
 {V\over Q_0C}\asymp {H\over qR}\ll1,
 \qquad {Q_0\over V}\asymp {qb_0h\over H}\asymp b_0.
                                                               \tag{CF19.14}
\]
所以 CF19.13 在 \(\xi=-t/Q_0\) 恰给 \(|t|\ll b_0P^\varepsilon\)
及全部远 \(t\) 尾；它不会产生新的 \(P\) 损失。CF19.D 由此缩成
一个更窄而可核对的输入：必须从原 (4.4)--(5.13b) 逐项证明送入
CF372.4 的完整权可写为 CF19.11 的三变量 \(\Phi\)，并满足
\(\mathfrak N_m^{\rm sh}(\Phi)\ll
P^\varepsilon{\cal S}_m(w)\)，统一于 detector/Bessel/AFE tags。
现在仍须从公开原 atom 逐项写出其 normalized 坐标到
\((d/D,c/C,(P_0d-Q_0c)/V)\) 的链式映射，并核对全部 finite tags。
不能把短移位重新藏回 product 坐标，也不能仅凭符号 \(v\) 相同而
引用不可复核的旧估计。

CF15/RV 的 actual-Riesz 四阶矩有一个真正有用的共同 Hilbert 列扩张。
令 \({\cal H}\) 为有限维 Hilbert 空间，任取 \(z_p\in{\cal H}\)、
\(\|z_p\|\le1\)，以及对每个 \(q\) 的 contraction
\(R_q:{\cal H}\to{\cal H}_q\)。置
\[
 {\cal P}_{q,z}(\chi)
 =R_q\!\left(\sum_{P<p\le2P}Y_p\chi(p)z_p\right).       \tag{CF19.15}
\]
对 CF15.2 的同一个 \({\cal T}_{q,a,\alpha}\)，有
\[
 \boxed{\quad
 \sum_q|Y_q|^2{1\over q-1}\sum_{\chi\ne\chi_0}
 \|{\cal P}_{q,z}(\chi)\|^2
 |{\cal T}_{q,a,\alpha}(\chi)|^2
 \ll_{\rho,w,W,\varepsilon}AP^\varepsilon S_Y^2.
 \quad}                                                   \tag{CF19.16}
\]
常数与 \(\dim{\cal H}\)、\(z_p\) 和 \(R_q\) 无关。

证明沿 CF15，但须核对四阶矩而不能只说“向量值同理”。令
\({\cal P}_z(\chi)=\sum_pY_p\chi(p)z_p\)。在 Hilbert tensor product
中
\[
 \|{\cal P}_z(\chi)\|^4
 =\|{\cal P}_z(\chi)\otimes{\cal P}_z(\chi)\|^2.
\]
其 product coefficient 在 \(n=p^2\) 时为
\(Y_p^2z_p\otimes z_p\)，在 \(n=pr\)、\(p<r\) 时为
\(Y_pY_r(z_p\otimes z_r+z_r\otimes z_p)\)。因此三角不等式和
\(\|z_p\|\le1\) 给
\[
 \sum_n\|c_{n,z}\|^2
 \le\sum_p|Y_p|^4+4\sum_{p<r}|Y_pY_r|^2
 \le2S_Y^2.                                             \tag{CF19.17}
\]
把 scalar primitive large sieve 在 \({\cal H}\otimes{\cal H}\) 的
正交基逐坐标求和，CF15.6 原样成为
\[
 \sum_q{1\over q-1}\sum_{\chi\ne\chi_0}
       \|{\cal P}_z(\chi)\|^4\ll PS_Y^2.              \tag{CF19.18}
\]
\(R_q\) 只缩小范数。再逐 \(q\) 对角色用 Cauchy、以 \(|Y_q|^2\)
为测度对 \(q\) 用 Cauchy，并代入 CF15.1、CF15.7 与 CF19.18，恰得
CF19.16。这个证明只使用一次 actual-Riesz flatness 和一次大筛。

CF19.16 可以改写成一个不依赖所选分解的 edge-kernel 判据。对有限
标量数组 \(z=(z_{p,q})\) 定义
\[
 \gamma_2(z)=\inf_{\substack{{\cal H},\,u_p\in{\cal H},\\
                    R_q:{\cal H}\to\mathbb C,\ z_{p,q}=R_q(u_p)}}
       \left(\sup_p\|u_p\|\right)
       \left(\sup_q\|R_q\|\right).                       \tag{CF19.19}
\]
这里下确界遍历有限维 Hilbert 分解。令
\[
 {\cal P}_{q,z}(\chi)=\sum_pY_p\chi(p)z_{p,q}.
\]
若 \(z=0\)，下式平凡。否则任一容许分解的两个 sup norm 都非零；把
\(u_p,R_q\) 分别除以这两个 norm，先对该分解应用 CF19.16，再对全部
分解取下确界（不要求下确界取到），得到
\[
 \boxed{\quad
 \sum_q|Y_q|^2{1\over q-1}\sum_{\chi\ne\chi_0}
 |{\cal P}_{q,z}(\chi)|^2|{\cal T}_{q,a,\alpha}(\chi)|^2
 \ll_{\rho,w,W,\varepsilon}
 A P^\varepsilon S_Y^2\,\gamma_2(z)^2.
 \quad}                                                   \tag{CF19.20}
\]
这不是 coefficient-uniform bound：任意 edge array 的
\(\gamma_2\) 不必有绝对常数界。确实，对阶数 \(n=2^k\) 的
Sylvester--Hadamard 矩阵 \(H_n\)，有
\(H_nH_n^*=nI\)，故 \(\|H_n\|_*=n^{3/2}\)。任一分解
\(H_n=UV\) 若行向量范数至多 \(A\)、列泛函范数至多 \(B\)，则
\(\|H_n\|_*\le\|U\|_{\rm F}\|V\|_{\rm F}\le nAB\)；所以
\(\gamma_2(H_n)\ge\sqrt n\)。这里 CF19.19--CF19.22 只陈述标量
edge；算子值实际 shell 还须给出相应的 Hilbert factorization，不能
由标量式自动获得。

CF19.19 也把 projective-atom 账翻译成一个可逐项验证的充分条件。
若
\[
 z_{p,q}=\sum_\nu c_\nu\,\ell_{p,\nu}r_{q,\nu},          \tag{CF19.21}
\]
则在 \({\cal H}=\ell^2(\nu)\) 中取
\[
 u_p(\nu)=|c_\nu|^{1/2}\ell_{p,\nu},\qquad
 R_q(x)=\sum_\nu |c_\nu|^{1/2}
       {c_\nu\over|c_\nu|}r_{q,\nu}x_\nu
\]
（\(c_\nu=0\) 的项删掉）。Cauchy 给出
\[
 \gamma_2(z)\le
 \left(\sup_p\sum_\nu|c_\nu||\ell_{p,\nu}|^2\right)^{1/2}
 \left(\sup_q\sum_\nu|c_\nu||r_{q,\nu}|^2\right)^{1/2}.
                                                               \tag{CF19.22}
\]
所以 CF7A 的局部 projective atoms 与 CF19.9 的 smooth Fourier
atoms 若在**变化的全部** \(a_0,b_0\) 上满足 CF19.22 的共同平方
质量 \(P^\varepsilon\)，便足以把 CF19.20 接入 actual-Riesz saving。
只知道 atom 数为 \(P^{o(1)}\)、逐 atom 范数为一或逐 level
projective mass 为 \(a_0^{-1/2+\varepsilon}\) 并不自动证明这两个
supremum；这正是 CF19.L 仍须逐字节核对的全局能量账。

但 critical \(C_1\) atom 的变化 level 确实可以无幂支付；这里必须
使用它的真实 divisor-output，而不是逐 level 的 projective
\(\ell^1\) 质量。令 \(M,N\ge1\)，\({\cal V}\) 为有限维 Hilbert
空间，\(v_D\in{\cal V}\) 支撑于 \(1\le D\le M\)，并置
\(V(n)=\sum_{D\mid n}v_D\)。有限展开严格给
\[
 \sum_{n\le N}{\|V(n)\|^2\over n}
 =\sum_{D,E\le M}\langle v_D,v_E\rangle
   {H_{\lfloor N/[D,E]\rfloor}\over[D,E]}.             \tag{CF19.23}
\]
其中约定 \(H_0=0\)。
这就是带符号、Hilbert 值的 lcm--harmonic Gram；没有先对
\(D,E\) 取绝对值。若 \(B=\sup_D\|v_D\|\)，则对任意
\(\eta\ge0\)，还有完全初等的
\[
 \boxed{\quad
 \sum_{n\le N}n^{-1+\eta}\|V(n)\|^2
 \le B^2N^\eta H_N^4.
 \quad}                                                   \tag{CF19.24}
\]
确实 \(\|V(n)\|\le B\tau(n)\)。若 \(d_4(n)\) 是有序四因子
分解数，则逐素数指数 \(e\) 有
\[
 (e+1)^2\le { (e+1)(e+2)(e+3)\over6},
 \]
故 \(\tau(n)^2\le d_4(n)\)；最后
\[
 \sum_{n\le N}{d_4(n)\over n}
 =\sum_{abcd\le N}{1\over abcd}\le H_N^4.
\]
这也证明 CF19.24 对复系数、任意删减后的 divisor 子集及正交有限
tags 同时成立。

CF19.23 不能先被替换成
\(H_N\sum_{D,E}\langle v_D,v_E\rangle/[D,E]\)。最小反例已在标量
情形出现：\(M=N=2\)、\(v_1=1,v_2=-1\) 时 CF19.23 左端为 \(1\)，
而 reciprocal-lcm form 为 \(1/2\)，乘 \(H_2=3/2\) 只有 \(3/4\)。
所以主线已有的 reciprocal-LCM 正定性不能用逐核上界直接接入；
CF19.24 才是 sign-safe 的有限输出估计。

在 CF7A 的 leading \(C_1\) cell 中，真实条件是
\(A_{1,*}\mid h\delta\)，而 CF7.8 的平方权是
\((h\delta)^{-1+\eta}\)。因此只要其余已归一化系数向量逐
\(A_{1,*}\) 一致有界，CF19.24 把**全部变化的**
\(A_{1,*}\) 在取范数前合并，只付 \(P^\varepsilon\)；另一 orientation
的 \(B_{1,*}\mid h'\delta'\) 可在 CF19.1 的另一 Hilbert 输出中独立
使用同一证明。这里 \((h\delta)^{-1/2}\) 正是 CF7 的 shell
half-root，不能在 CF19.24 之后再乘一次。由此 CF19.L 中
critical-\(C_1\) 的 **level multiplicity** 已支付；两侧 divisor
outputs 与同一个 complete-shift/principal/equal-prime packet 的无损
输运仍未证明。其余 local atoms 的 level multiplicity 由下一分割继续
处理；native rows 保持开放。

逐 local valuation 再看一次，divisor-output 实际覆盖得更多。以下
只处理 \(kh\delta\ne0\) 的 unramified generic shell；任一坐标为零的
axis 继续留在 CF6 的 native/open 行。对每个 \(p\mid A\) 记
\[
 u_p=v_p(k),\qquad b_p=v_p(h)+v_p(\delta),
\]
并作互斥分解
\[
 A_{00}=\prod_{\substack{p\mid A\\u_p=b_p=0}}p,\qquad
 A_{\rm div}=A/A_{00}.                                  \tag{CF19.25}
\]
于是精确有：
\[
 (A_{00},|kh\delta|)=1,\qquad
 A_{\rm div}\mid\operatorname{rad}(|kh\delta|).
\]
令 \(e_{00,p}\) 是只保留 \((u,b)=(0,0)\) 坐标的秩一矩阵，并在
已经带有 CF7.8 的 \(k,h,\delta\) 权的局部空间中写
\[
 E_p=E_p(1,0)e_{00,p}+\widetilde E_p.                   \tag{CF19.26}
\]
这是精确矩阵等式；\(\widetilde E_p\) 的每个非零坐标都满足
\(u_p+b_p\ge1\)。令 \(\widetilde K_{p,u}\in{\cal Y}_p\) 是其第
\(u\) 个输出列，并定义
\[
 \widetilde{\mathfrak h}_p
 :=\sum_{u\ge0}p^{-u}\|\widetilde K_{p,u}\|_{{\cal Y}_p}.
\]
零--零秩一块的同一 projective mass 恰为 \(|E_p(1,0)|\)。故由
三角不等式、CF7.6 与 CF7.9，
\[
 \widetilde{\mathfrak h}_p
 \le {\mathfrak h}_p+|E_p(1,0)|
 \ll_\varepsilon p^{-1/2+\varepsilon}.
\]
因此张量展开 \(\widehat\otimes_{p\mid A}E_p\) 时，取零--零块的
prime product 恰为 \(A_{00}\)，其余块的 product 恰为
\(A_{\rm div}\)。对补块定义
\(\widetilde{\mathfrak h}(D)=\prod_{p\mid D}
\widetilde{\mathfrak h}_p\)，则
\[
 \widetilde{\mathfrak h}(A_{\rm div})
 \ll_\varepsilon A_{\rm div}^{-1/2+\varepsilon}.       \tag{CF19.27}
\]
这里 shell half-root 只使用了这一次；没有再从调和权或
progression mass 中复制它。

在逐 \(D\) 具有共同输入预算的纯 shell 层，这个补块的
varying-level multiplicity 也没有幂次损失。确切地说，
在固定输出 \((k,h,\delta)\) 上只有
\(D\mid\operatorname{rad}(|kh\delta|)\) 的补块 \(D=A_{\rm div}\)
非零，故对任意同一 Hilbert 输出中的有限向量 \(F_D(k,h,\delta)\)，
\[
 \left\|\sum_DF_D(k,h,\delta)\right\|^2
 \le \tau(|kh\delta|)
      \sum_D\|F_D(k,h,\delta)\|^2.                     \tag{CF19.28}
\]
若实际 nonlocal column 已经被写成纯 valuation tensor 与一个向量
\(x_D\) 的张量，随后只经过 norm-one contractions，并记
\(B_D=\|x_D\|\)，CF19.27 才给
\(\|F_D\|\le\widetilde{\mathfrak h}(D)B_D\)。先应用 CF19.28，再求
全部输出，得到（把任意固定幂次支撑写成 \(D\le P^C\)）
\[
 \left\|\sum_DF_D\right\|^2
 \ll_\varepsilon P^\varepsilon
       \sum_{D\le P^C}D^{-1+\varepsilon}B_D^2.
                                                               \tag{CF19.29}
\]
所以当剩余输入列逐 \(D\) 具有同一预算 \(B_D\le B\) 时，右端只付
\(P^\varepsilon\)。CF19.28 允许 \(F_D\) 依赖完整输出，因而没有把
\(C_j(b_p)\) 错当成固定的 \(v_D\)；这正是不能直接把一般 atoms
塞进 CF19.24 的原因。CF19.24 仍精确支付 leading \(C_1\) 的固定
divisor-column，而 CF19.26--CF19.29 支付整个补块的局部 level
multiplicity。尚未证明的仍是实际非局部权确实具有这里显示的
valuation-tensor/norm-one factorization，并给出共同 \(B_D\) 预算。

真正没有 divisor incidence 的只剩 \(A_{00}\)。此时每个 prime 只取
CF7.5 的零--零块，且 CF7.6 给出**精确值**
\[
 E_p(1,0)=\lambda_\pi(p)-{p\lambda_\pi(p)\over p+1}
          ={\lambda_\pi(p)\over p+1}.
\]
故张量后该零--零 level 的 signed 系数恰为
\[
 \boxed{\quad
   {\mu(A_{00})\lambda_\pi(A_{00})
      \over\prod_{p\mid A_{00}}(p+1)},\qquad
   (A_{00},|kh\delta|)=1.
 \quad}                                                   \tag{CF19.30}
\]
这里使用 squarefree unramified Hecke multiplicativity；continuous
oldspace 先采用 CF7A 的同一 ambient basis，不能把它换成逐个 ramified
Eisenstein Fourier coefficient。

CF19.30 是**相对于** ambient harmonic zero kernel 的 multiplier；若要
重新送入 primitive trace，必须先恢复 CF7.4，不能把 ambient
\(P_1(0,0)\) 当作第二份 saving。对一个零--零 prime 精确有
\[
 P_1(0,0)E_p(1,0)
 ={\lambda_\pi(p)\over(p+1)^2\rho_p},\qquad
 \rho_p=1-{p\lambda_\pi(p)^2\over(p+1)^2}.              \tag{CF19.31}
\]
CF7A 已证明
\(r_p:=p\lambda_\pi(p)^2/(p+1)^2<1\)，所以在每个 unramified
datum 上
\[
 {\lambda_\pi(p)\over(p+1)^2\rho_p}
 ={1\over(p+1)^2}\sum_{\ell\ge0}
       \left({p\over(p+1)^2}\right)^\ell
       \lambda_\pi(p)^{2\ell+1}.                       \tag{CF19.32}
\]
该级数以原几何比 \(r_p\) 绝对收敛，且 \(r_p\) 对全部 unramified
datum 与 prime 一致小于一。

这个几何级数可以进一步无损改写为真正的 odd-Hecke 列。
由 Hecke recurrence，在收敛圆内有生成函数
\[
 \sum_{n\ge0}\lambda_nz^n={1\over1-\lambda_1z+z^2}.
\]
取奇数部并置 \(y=z^2\)，得
\[
 \sum_{a\ge0}\lambda_{2a+1}y^a
 ={\lambda_1\over(1+y)^2-\lambda_1^2y}.
\]
在 \(y=1/p\) 处，CF7A 的 Kim--Sarnak 上界使左边由
\((2a+2)p^{-a-2+\theta(2a+1)}\) 控制，因
\(p^{-1+2\theta}<1\) 而绝对收敛。因此
\[
 \boxed{\quad
 {\lambda_\pi(p)\over(p+1)^2\rho_p}
   =\sum_{a\ge0}{\lambda_\pi(p^{2a+1})\over p^{a+2}}.
 \quad}                                                   \tag{CF19.32a}
\]
特别地，除去 \(a=0\) 项后的局部绝对尾满足
\[
 \sum_{a\ge1}{|\lambda_\pi(p^{2a+1})|\over p^{a+2}}
 \ll p^{-3+3\theta}.                                  \tag{CF19.32b}
\]
这是可求和的局部修正，但它不授权交换全部谱和与 level 和。

对 squarefree \(A_{00}\) 张量 CF19.32a，并用 unramified
Hecke multiplicativity，得到另一个精确形式
\[
 \prod_{p\mid A_{00}}P_1(0,0)E_p(1,0)
 =\sum_{\substack{t\ge1\\\operatorname{rad}(t)\mid A_{00}}}
     {\lambda_\pi(A_{00}t^2)\over A_{00}^2t}.          \tag{CF19.32c}
\]
右边系数的普通平方质量是有限的：
\[
 \sum_{\substack{t\ge1\\\operatorname{rad}(t)\mid A_{00}}}
 {1\over A_{00}^4t^2}
 ={1\over A_{00}^4}\prod_{p\mid A_{00}}(1-p^{-2})^{-1}
 \le {\zeta(2)\over A_{00}^4}.                         \tag{CF19.32d}
\]
但不能因此把无限右边当成一个有限长普通 spectral
large-sieve polynomial。事实上，其 index-length 加权质量精确为
\[
 \sum_{\substack{t\ge1\\\operatorname{rad}(t)\mid A_{00}}}
 (A_{00}t^2)\left|{1\over A_{00}^2t}\right|^2
 ={1\over A_{00}^3}
   \sum_{\substack{t\ge1\\\operatorname{rad}(t)\mid A_{00}}}1=+\infty
 \qquad(A_{00}>1).                                     \tag{CF19.32e}
\]
所以含 \(N/q\) 长度项的粗略大筛在逐项取 CF19.32c 极限时
必然失败。合法路线必须或者对有限 odd-Hecke 截断与原有理
multiplier 尾作一致控制，或者直接证明该有理 multiplier 的谱算子界。
CF19.32d 不能单独闭合 CF19.L。

Hecke recurrence
\(\lambda_\pi(p)\lambda_\pi(p^j)
=\lambda_\pi(p^{j+1})+\lambda_\pi(p^{j-1})\) 还给一个精确 parity
事实：每个奇次幂 \(\lambda_\pi(p)^{2\ell+1}\) 都是
\(\lambda_\pi(p^{2a+1})\) 的有限线性组合，不含偶 valuation。
因此 CF19.32 的任一有限截断乘 \(\lambda_\pi(k)\) 后，在
\((p,k)=1\) 时只含第一 Hecke index 的正奇 \(p\)-valuation。若另一
index \(n\) 满足 \((p,n)=1\)，primitive Petersson/Kuznetsov 的
Kronecker diagonal 对这个截断逐项为零。张量全部
\(p\mid A_{00}\) 后，只要 \(A_{00}>1\)，同一结论仍成立，因为
\((A_{00},kn)=1\)：
\[
 \boxed{\quad\text{zero--zero block 的每个有限 odd-Hecke 截断
 在 primitive trace 上没有 diagonal。}\quad}          \tag{CF19.33}
\]
这不是逐 level 绝对值，也没有复用 harmonic \(1/p\)：CF19.31 正是把
它恢复后再作 Hecke parity 展开。要把 CF19.33 升为完整全谱结论，仍须
在共同 Bessel test 下证明 CF19.32 的极限可与 Maaß、holomorphic、
Eisenstein 三谱及全部 level 外和交换；而 off-diagonal、principal 与
axis 并未由 diagonal 消失而得到估计。因此 CF19.33 是新的局部
diagonal guard，不是 CF19.C 或 CF9.1。

同一个零列还有一个精确 Euler-product 解释。令 \(M\) 含 primitive
conductor、\(kh\delta\) 与全部另行冻结的小 primes，并在
\(\Re s>\theta\) 先绝对收敛地定义
\[
 {\cal Z}_{\pi,M}(s)
 =\sum_{\substack{A\ {\rm squarefree}\\(A,M)=1}}
   {\mu(A)\lambda_\pi(A)\over\prod_{p\mid A}(p+1)}A^{-s}
 =\prod_{p\nmid M}\left(1-{\lambda_\pi(p)p^{-s}\over p+1}\right).
                                                               \tag{CF19.34}
\]
逐 Euler factor 有
\[
 {\cal Z}_{\pi,M}(s)=L^{(M)}(1+s,\pi)^{-1}{\cal H}_{\pi,M}(s),
\quad
 {\cal H}_{\pi,M}(s)=\prod_{p\nmid M}
 {1-\lambda_\pi(p)p^{-s}/(p+1)
  \over1-\lambda_\pi(p)p^{-1-s}+p^{-2-2s}}.             \tag{CF19.35}
\]
确实分子与分母之差恰为
\[
 {\lambda_\pi(p)p^{-s}\over p(p+1)}-p^{-2-2s}.
\]
Kim--Sarnak 因而使 \({\cal H}_{\pi,M}\) 的 Euler product 在
\(\Re s>-1/2\) 的每个闭子带绝对收敛；第一项只要求
\(\Re s>\theta-1\)，第二项给真正边界 \(-1/2\)。

CF19.35 也排除一个看似便宜的闭合：对 dyadic \(A_{00}\) 做 Mellin
反演后，逐 \(\pi\) 把线向左移动固定距离，必须穿过
\(L(1+s,\pi)^{-1}\) 的 poles，也就是 \(L(1+s,\pi)\) 的 zeros。
现有逐 form zero-free region 不能一致提供所需固定幂。故 CF19.35
只能把剩余对象识别为一个**谱平均中的 reciprocal standard-
\(L\) mollifier**；不能把点态 contour shift 当成 varying-level saving。

不过，若 opposite orientation 已经真正给出与 \(A_{00}\) 无关的共同
Hecke 列，则不需要使用 CF19.32c 的无限展开。下面的有限卷积引理同时
适用于 Maaß、holomorphic 与 Eisenstein datum，因为只用 unramified
Hecke 关系。固定整数 \(M\ge1\)、实数 \(X,N\ge1\) 与 Hilbert 空间
\({\cal H}\)，令
\[
 \alpha_A={\mu(A)\over\prod_{p\mid A}(p+1)},\qquad
 d_m=\sum_{\substack{X<A\le2X,\ A\ {\mathrm{squarefree}}\\
                     (A,M)=1,\ An=m,\ (A,n)=1}}
             \alpha_Ac_n,                              \tag{CF19.36}
\]
其中 \(c_n\in{\cal H}\) 支撑于 \(1\le n\le N\)。对任一 conductor
整除 \(M\) 的 trivial-central-character Hecke datum \(\pi\)，
逐有限项使用 \((A,n)=1\) 时的乘法性，精确得到
\[
 \sum_{\substack{X<A\le2X,\ A\ {\mathrm{squarefree}}\\(A,M)=1}}
   \alpha_A\lambda_\pi(A)
   \sum_{\substack{n\le N\\(n,A)=1}}c_n\lambda_\pi(n)
 =\sum_{m\le2XN}d_m\lambda_\pi(m).                   \tag{CF19.37}
\]
这一步没有恢复 CF19.31 的 harmonic \(1/p\)，所以没有把它重复算成
saving；它直接重组原 CF19.30 的有限 Möbius 列。

记 \(\Delta(U)=\max_{1\le m\le U}\tau(m)\)。固定 \(m\) 的分解
\(m=An\) 至多有 \(\tau(m)\) 个，Hilbert 空间中的 Cauchy--Schwarz
因而给
\[
 \begin{aligned}
 \sum_m\|d_m\|^2
 &\le \Delta(2XN)
   \sum_{X<A\le2X}|\alpha_A|^2\sum_{n\le N}\|c_n\|^2\\
 &\le {2\Delta(2XN)\over X}\sum_{n\le N}\|c_n\|^2
 \ll_\varepsilon X^{-1}(XN)^\varepsilon
                    \sum_{n\le N}\|c_n\|^2.          \tag{CF19.38}
 \end{aligned}
\]
第二行只用了 \(\prod_{p\mid A}(p+1)\ge A\) 及区间内整数个数不超过
\(2X\)。最后的初等 divisor bound 也不作为黑箱：给定
\(\varepsilon>0\)，对充分大的 prime 有
\(e+1\le p^{\varepsilon e/2}\)；余下有限 primes 的
\((e+1)p^{-\varepsilon e/2}\) supremum 有限。逐素数相乘即得
\(\tau(m)\ll_\varepsilon m^\varepsilon\)（把 \(\varepsilon/2\)
重命名为 \(\varepsilon\)）。

因此设一个包含三类离散谱与连续谱的非负共同调和测度 \(d\nu(\pi)\)
已经在同一 Bessel majorant 下满足标量 spectral large sieve
\[
 \int\left|\sum_{m\le U}a_m\lambda_\pi(m)\right|^2d\nu(\pi)
 \le {\mathscr L}(U)\sum_{m\le U}|a_m|^2.
\]
在有限维子空间 \(\operatorname{span}\{c_n:n\le N\}\) 的正交基逐坐标
求和（连续谱用非负 Tonelli），再代
CF19.37--CF19.38，严格推出
\[
 \boxed{\quad
 \int\left\|\sum_A\alpha_A\lambda_\pi(A)
       \sum_{(n,A)=1}c_n\lambda_\pi(n)\right\|^2d\nu(\pi)
 \ll_\varepsilon {\mathscr L}(2XN)\over X}(XN)^\varepsilon
                 \sum_{n\le N}\|c_n\|^2.
 \quad}                                                   \tag{CF19.39}
\]
CF19.39 是一个已证明的蕴含；其唯一解析前提就是紧邻显示的 scalar
large sieve。它准确说明下一条谱估计应作用于哪个长度与平方质量；
这个 scalar large sieve 本身仍须按原共同 Bessel test 重证。若 \(c_n\) 还依赖 \(A\)、谱权不是
同一个非负 majorant，或 ramified prime 未先放入 \(M\)，CF19.37--
CF19.39 均不能直接使用。这三项正是 CF19.L 尚需从 physical atom
验证的共同列条件。

这里可以把“全谱 scalar large sieve”与 shell 的归一化再缩窄一步。
采用 [Hu--Petrow--Young 的 generalized PBK
公式](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/88D50BBABA259F680EEF50F145BC5E0F/S2050509426101765a.pdf/generalized_mathrmpgl2_peterssonbruggemankuznetsov_formula_for_analytic_applications.pdf)
的记号，令 \(f\) 是满足其
TF、NmL、FTB、CvF 四条件的有限处纯张量，并令 \(h_\infty\) 是该文
(1.40) 或 (1.41) 的非负 archimedean majorant。对支撑于
\(m\le U\)、且 \((m,N_f)=1\) 的有限系数 \(a_m\)，把 Theorem 4.8
的 Fourier-coefficient 形式在开平方以后写成
\[
 \begin{aligned}
 {\mathcal Q}_f(a)={}&
 \sum_{\pi\in F_0(f)}h_\infty(t_\pi)
   \sum_{\varphi\in B_f(\pi)}
       \left|\sum_{m\le U}a_m a_{u_\varphi}(m)\right|^2\\
 &+{1\over4\pi}\sum_{\chi\in F_E(f)}\int_{\mathbb R}
 h_\infty(t)\sum_{\varphi\in B_f(\chi,\chi^{-1})}
       \left|\sum_{m\le U}a_m a_{u_E(\varphi_{it})}(m)\right|^2dt.
                                                               \tag{CF19.40}
 \end{aligned}
\]
这是逐项非负的 Maaß--Eisenstein 二次型；正性是在 orthonormal
Fourier basis 中开平方得到的，不能从一个可能带相位的压缩权反推。
在 \((m,N_f)=1\) 时用该文 (1.9)、(4.21) 才可把 CF19.40 改写成
共同 Hecke polynomial 的 cusp 与 continuous harmonic measures。

该文 Theorem 1.23 的证明在丢掉目标 cusp 子族**以前**先把正的
CF19.40 通过 Theorem 1.8 精确写成 diagonal \(D\) 与 generalized
Kloosterman 项 \(S\)，随后其 (5.17)--(5.26) 分别估计 \(D\) 与
\(S\)。所以同一证明实际给出比定理陈述更直接的全正谱推论
\[
 \boxed{\quad
 {\mathcal Q}_f(a)
 \ll_\varepsilon (|F|+U)(UqT)^\varepsilon
                    \sum_{m\le U}|a_m|^2.
 \quad}                                                   \tag{CF19.41}
\]
这里 \(F\) 是 NmL 中用于比较 \(F_0(f)\) 的同导子有限 cusp family；
\(|F|\) 支付 diagonal，\(U\) 支付 off-diagonal。CF19.41 不是把
Theorem 1.23 的 cusp 左边形式上加一个 continuous 项，而是引用其
证明中在这一步尚未删项的 PBK 等式。holomorphic/discrete-series
变体由该文 Remark 1.24 的独立 Petersson 版本给出；若实际对象同时
含 Maaß、holomorphic、Eisenstein 三部分，必须对同一个 coefficient
polynomial 分别应用这两个正公式再相加。它仍不允许三类谱各自选择
不同的 physical 投影或 Bessel majorant。

经典 exponent-one local projector 与 CF7 的 ambient kernel 也能
逐式对齐。HPY (7.1)--(7.4) 在 \(c=1\) 时给
\[
 f_{\le1,p}=(p+1){\bf1}_{ZK_0(p)},\qquad
 f_{\le1,p}(1)=p+1,
\]
且 \(\pi(f_{\le1,p})\) 是投到 \(V_\pi^{K_0(p)}\) 的正交投影。
对 unramified trivial-central-character datum，HPY (1.11) 的
oldclass factor 满足
\[
 r_\pi(p)^{-1}
 =(1+p^{-1})\sum_{a\ge0}{\lambda_\pi(p^{2a})\over p^a}
 ={1\over1-p\lambda_\pi(p)^2/(p+1)^2}
 ={1\over\rho_p}.                                      \tag{CF19.42}
\]
第二个等号不是额外局部假设：从
\(\sum_{j\ge0}\lambda_jz^j=(1-\lambda_1z+z^2)^{-1}\)
取偶部，得
\(\sum_{a\ge0}\lambda_{2a}y^a=(1+y)/((1+y)^2-\lambda_1^2y)\)，
再置 \(y=p^{-1}\)。因此将 HPY 的 primitive harmonic trace 除以
局部 Plancherel mass \(f_{\le1,p}(1)\) 后，局部权精确成为
\[
 {r_\pi(p)^{-1}\over p+1}
 ={1\over(p+1)\rho_p}=P_1(0,0).                       \tag{CF19.43}
\]
squarefree 多素数情形由纯张量相乘。故 CF7 的 ambient \(p^{-1}\)
来自 normalized classical projector，而 CF7.10 的 shell half-root
来自其上的 coefficient norm；两者来源不同，但相对于已经含 CF19.43
的 physical baseline 时绝不能再把前者称为第二份 saving。

最后，把 CF19.41 代入 CF19.39 时尺度不能简写成“整体除以 \(X\)”。
在未除以 \(f(1)\) 的 HPY harmonic trace 中，\(U=2XN\) 给
\[
 {\mathscr L(2XN)\over X}
 \ll_\varepsilon
 \left({|F|\over X}+2N\right)(XNqT)^\varepsilon.       \tag{CF19.44}
\]
若 physical convention 已按 CF19.43 将整个 trace 除以 \(f(1)\)，
则 CF19.44 的右边也整体除以 \(f(1)\)。因此 reciprocal
Hecke--Möbius 列只在 family-mass 项产生显式 \(X^{-1}\)；length
项仍是 \(2N\)（或 normalized convention 下的 \(2N/f(1)\)）。
要把它称为 CF19.L 所需的 \(P\)-saving，仍须从原 atom 证明：

1. 所有变化的 shell labels 已嵌入**一个** classical positive
   projector，而不是一族不能相加的 normalized traces；
2. CF19.36 的 opposite column 真正与 \(A\) 无关，并且其全部 indices
   与 projector level 互素，ramified primes 已进入 \(M\)；
3. 原 Bessel/AFE weight 被同一个 (1.40)/(1.41) majorant 控制，且
   CF19.44 的 \(|F|/X\) 与 \(N\) 逐项落在 physical baseline 内。

第一条不能靠把全部 level 放进一个未经计费的巨大 classical level
来形式解决。确切地说，若 shell 集合包含每个
\(X<p\le2X\) 的 prime level，而一个 classical pure-tensor
\(K_0(L)\) projector 要同时保留这些 level-one oldspaces，则逐 prime
必有 \(p\mid L\)，从而
\[
 L\ge\prod_{X<p\le2X}p,\qquad
 f_{\le L}(1)=\nu(L)\ge\prod_{X<p\le2X}(p+1).          \tag{CF19.45}
\]
这是 level 与 Plancherel mass 的真实新增费用，原 polynomial
physical baseline 中没有这一项。CF19.45 只排除这种 naive common-LCM
overprojector；它不排除一个真正的 signed level reciprocity 或直接
rational-multiplier trace，而后两者正是仍应继续证明的路线。

### CF19B. 真实 level reciprocity 的有限平方自由完成，以及它不提供的 half-root

先把一个符号边界钉死。Hu--Petrow--Young 的 Theorem 1.8 是
\(m_1m_2>0\) 的 generalized PBK。该文在 Theorem 1.8 后明确说明
\(m_1m_2<0\) 的相对迹公式“expected”，但当时没有 relative-trace
proof；其 (1.22)--(1.23) 版本在后文只是被 posited and assumed。
因此 CF19.40--CF19.44 的 generalized local projector 目前只能直接
用于同号行。经典 \(K_0(N)\) Kuznetsov 的异号版本当然存在，但不能
据此把 HPY 的任意有限处 \(f\) 与 actual exact-shell projector 也
自动升级成异号公式。这个差别正落在 QCT 的 opposite-sign/mixed 行，
不是一个可由绝对值忽略的 Bessel 符号。

另一方面，Andersen--Kıral 的
[level reciprocity](https://arxiv.org/abs/1801.06089) 确实给出一个
**已证明的经典全谱模板**，而且其 prime 假设中的有限局部完成可以
扩到平方自由数。为避免把模板误称为 CF19.L，下面从其原公式重做这
一步。

固定 level-one holomorphic newform \(g\)（归一化 Hecke 系数记为
\(\lambda_g\)，weight 为 \(\kappa\)）。以下始终假设
\(\phi^{(j)}(0)=0\)（\(0\le j\le12\)），且某个 \(B>12\) 使
\(\phi^{(j)}(x)\ll(1+x)^{-B}\)（\(0\le j\le12\)）；这正是该文
Theorem 5.1 的 test class。对平方自由 \(N\)、\((r,N)=1\)，令
\({\cal N}_g^+(r,N;s;\phi)\) 为 Andersen--Kıral (2.10)--(2.13)
的三谱和，只把 prime twist 换成 \(\lambda_f(r)\)：

* Maaß 项以 Fricke 特征值 \(\omega_f\)、\(\phi_+(t_f)\)、
  \(\widetilde L(s,g\times f)^2\lambda_f(r)\) 加权；
* holomorphic 项以 \(i^\ell\phi_h(\ell)\)、同一个 Fricke 权和同一个
  raw \(\widetilde L^2\) 加权；
* Eisenstein 项在所有 cusps 上积分，两个 raw Eisenstein
  \(\widetilde L\) 因子分别取 \(it\) 与 \(-it\)，twist 是
  \(\tau_{it}(r)\)。

这里 raw \(\widetilde L\) 使用 Fourier coefficient \(\nu_f(n)\)，而
不是只对 newform 写 \(\nu_f(1)L(s,g\times f)\)；这正是 oldforms 已
包括在同一迹公式中的归一化。这个 moment 是带 Fricke 符号的
\(\widetilde L^2\)，不是非负的 \(|L|^2\)，也不是任意 Hilbert 系数列。

若 \(p\nmid rN\)，在这些 moment 的有限线性空间上定义

\[
 \begin{aligned}
 ({\mathscr C}^{(s)}_p{\cal N})(r,N)
 :={}&(1-p^{-4s}){\cal N}(pr,N)\\
 &-2\lambda_g(p)p^{-s}(1-p^{-2s}){\cal N}(r,N)
   +p^{-1/2}{\cal N}(r,pN).
 \end{aligned}                                           \tag{CF19.46}
\]

不同 prime 的 \(\mathscr C_p^{(s)}\) 交换，因为三种操作只在该 prime
上分别选择 twist、neutral 或 level 状态。于是对
\(A\) squarefree、\((A,N)=1\)，可无歧义地置

\[
 {\cal M}_g^+(A,N;s;\phi)
 :=\left(\prod_{p\mid A}{\mathscr C}^{(s)}_p\right)
       {\cal N}_g^+(1,N;s;\phi).                         \tag{CF19.47}
\]

这不是形式猜测。在 \(\Re s>5/4\) 的绝对收敛域，先用 \(0\infty\)
Kuznetsov 打开两个 raw Dirichlet series。\(A=1\) 时得到

\[
 {\cal N}_g^+(1,N;s;\phi)=\zeta_N(2s)^2
                 {\cal S}_g^+(1,N;s;\phi),
\]

其中

\[
 {\cal S}_g^+(A,N;s;\phi)
 =\sum_{m,n\ge1}{\lambda_g(m)\lambda_g(n)\over(mn)^s}
  \sum_{(c,AN)=1}{S(m\overline N,nA;c)\over c\sqrt N}
  \phi\!\left({4\pi\sqrt{mnA}\over c\sqrt N}\right). \tag{CF19.48}
\]

设已处理互素的 \(D\mid A\)，再取 \(p\mid A/D\)。这里不能把裸的
\(\lambda_f(D)\) 在应用 trace formula 时冒充一个无关 scalar；正确的
归纳对象是已经完成的 \(\prod_{\ell\mid D}\mathscr C_\ell^{(s)}\)。
先把这个有限乘积与 \(\mathscr C_p^{(s)}\) 全部展开，再打开两个 raw
Dirichlet series。不同 prime 的 Hecke relations 交换。对新 prime
\(p\)，此前所有 \(D\)-状态的 indices 与 levels 都是 \(p\)-units，
所以 Andersen--Kıral Lemma 4.1 与 Proposition 4.2 的
\(p\)-adic 分割逐项不变；其 (4.11)--(4.13) 分别处理
\(p\Vert c\)、\(p^2\mid c\) 与同时除去两端的情形。把三个分支与已经
完成的 \(D\)-组合重新合起，恰产生 CF19.46，并把 geometric modulus
条件从 \((c,DN)=1\) 改成 \((c,DpN)=1\)、第二 Kloosterman index 从
\(nD\) 改成 \(nDp\)，同时把 \(\zeta_{DN}\) 的 local factor 改成
\(\zeta_{DpN}\)。所以对 \(\omega(A)\) 归纳得到

\[
 \boxed{\quad
 {\cal M}_g^+(A,N;s;\phi)
   =\zeta_{AN}(2s)^2{\cal S}_g^+(A,N;s;\phi)
 \quad}                                                   \tag{CF19.49}
\]

于 \(\Re s>5/4\)。归纳每一步只重排绝对收敛级数，且不同 prime 的
valuation 操作交换，故没有隐藏 Fubini 或 prime-order 选择。

同一 geometric 对象也有真正的 two-sided reciprocity。Andersen--
Kıral Theorem 5.1 的证明把内和写成
\(D_g(\overline N,A,c;s+u/2)\)，只使用
\((A,N)=(AN,c)=1\) 以取得逆元；其 additive-twist functional
equation 并不使用 \(A,N\) 为 prime。因此同一 Mellin contour 计算给

\[
 \sqrt N\,{\cal S}_g^+(A,N;s;\phi)
 =\left({A\over N}\right)^{2s-1}
   \sqrt A\,{\cal S}_g^+(N,A;s;\Phi_{\kappa,s}),       \tag{CF19.50}
\]

其中 \(\Phi_{\kappa,s}\) **正是**该文 (5.2) 的 gamma-ratio Mellin
transform；它不是可逐 box 重新选择的任意 majorant。先在绝对收敛域
证明 CF19.49--CF19.50。对每个固定 \(A,N\)，CF19.52 只含有限个
固定 levels \(Nw\)；该文对 raw Rankin--Selberg \(L\)-functions、
rapid Bessel transforms 与全部 cusps 的 continuation 可逐个应用，
再由恒等定理把 CF19.49--CF19.50 延到 \(s=1/2\)。这里没有声称这些
continuation bounds 对变化的 \(A,N\) 一致；所得只是每个有限
\((A,N)\) 的精确恒等式。于是对互素 squarefree \(A,N\)

\[
 \boxed{\quad
 \sqrt N\,{\cal M}_g^+(A,N;\phi)
   =\sqrt A\,{\cal M}_g^+(N,A;\Phi).
 \quad}                                                   \tag{CF19.51}
\]

所以 prime--prime reciprocity 的**局部完成**并不会因平方自由
tensorization 自动产生指数损失。确切地，把 \(A=uvw\) 分成两两互素
的 twist、neutral、level 三种 prime 状态，CF19.47 展开为

\[
 \begin{aligned}
 {\cal M}_g^+(A,N;s;\phi)
 =\sum_{uvw=A}\;&
  \prod_{p\mid u}(1-p^{-4s})
  \prod_{p\mid v}\{-2\lambda_g(p)p^{-s}(1-p^{-2s})\}
  w^{-1/2}
  {\cal N}_g^+(u,Nw;s;\phi).
 \end{aligned}                                           \tag{CF19.52}
\]

在 \(s=1/2\) 时，Deligne 的 \(|\lambda_g(p)|\le2\) 使一个 prime 的
绝对系数质量至多

\[
 (1-p^{-2})+4p^{-1/2}(1-p^{-1})+p^{-1/2}
 \le1+5p^{-1/2}.
\]

若所有未冻结 prime 都满足 \(p\ge Z>1\)，则

\[
 \sum_{uvw=A}|c(u,v,w)|
 \le\exp\!\left(5\sum_{p\mid A}p^{-1/2}\right)
 \le A^{5/(\sqrt Z\log Z)}.                              \tag{CF19.53}
\]

给定 \(\varepsilon>0\)，先冻结只依赖 \(\varepsilon\) 的有限个小
primes，使 \(5/(\sqrt Z\log Z)\le\varepsilon\)，便只付
\(A^\varepsilon\)。这给出了 composite local completion 的真实有限
系数账，而不是把 \(3^{\omega(A)}\) 粗估成固定幂。

但 CF19.51 **没有**提供 shell half-root。CF19.52 中所有 prime 都取
twist 状态的项，其系数为

\[
 \prod_{p\mid A}(1-p^{-2})\ge\prod_p(1-p^{-2})
 ={1\over\zeta(2)}>0.                                   \tag{CF19.54}
\]

只有所有 prime 都取 level 状态的单独一项带 \(A^{-1/2}\)；它不能代表
整个完成式。在 \(A\asymp N\) 时 CF19.51 的外比例
\(\sqrt{A/N}\) 也是常数量级。因此任何用于 actual QCT 的
\(A^{-1/2}\) 仍只能来自 CF7.9--CF7.10 已支付一次的 shell coefficient
norm，不能再从 level reciprocity、Fricke harmonic weight 或
CF19.52 的某个子项复制。这也严格否定了把 §420 候选中的
“互反外因子”直接记成全谱 \(A^{-1/2}\) saving。

CF19.46--CF19.54 同时把可复用范围划得很窄：它们完整包含经典
Maaß、holomorphic、Eisenstein、oldforms 与 level-raised correction，
却仍不闭合 CF19.L/CF19.C，原因逐项如下。

1. \(+\) moment 的两个 Dirichlet columns 都是同一 fixed \(g\) 的
   \(\lambda_g(n)n^{-s}\)，且谱侧是 raw \(\widetilde L^2\)。actual
   \(b^\sharp\)、complete-shift tags 与任意 Hilbert columns 并不满足
   这个特殊结构。
2. CF19.50 把一个共同 \(\phi\) 变成一个共同 \(\Phi\)。尚未证明原
   AFE/Bessel/physical-shift 权恰为这对变换，也未证明 CF19.D 的
   seminorm 能控制变换后所有 boxes；而 \(\phi_+,\Phi_+\) 本身并非
   CF19.40 的非负 majorants，若无另一个共同 domination 证明，不能
   在 reciprocity 后直接丢绝对值再调用 CF19.41。
3. 异号经典 Kuznetsov 改用 \(K\)-Bessel transform，Maaß Fourier
   coefficient 还带 parity，holomorphic 项消失；HPY 的 generalized
   opposite-sign local-projector 版本又正是尚未证明的假设。因此不能
   把 CF19.51 的三谱 \(+\) moment 原样贴到负号 QCT row。
4. CF19.52 的 level-raised 项虽以 raw Fourier coefficients 正确包含
   classical oldforms，却没有证明其局部三项就是 CF7.5 的
   valuation-one \(E_p(a,b)\)，更没有包含 CF10.1 的共同
   principal/axis/residue/finite-projection 四行。

故这里得到的是一个新的**无条件平方自由 level-reciprocity 子定理**和
一个严格的 no-double-counting 结论。要把它接入 CF9.1，下一条必须是
实际 coefficient identity：在同一个 finite tag 与同一个 Bessel
test 下，把 CF6.2 的指定同号行逐字写成 CF19.52，并对异号行另给已证
的 generalized trace；或者直接为 actual Hilbert columns 重证
CF19.49 的 local sieving induction。未完成这一步时，CF19.51 不能
被称为 varying-level QCT bound。

### CF19C. reciprocity 只删除反对称 test；固定 parity 壳没有 Möbius saving

CF19.51 对 signed level family 的代数作用可以精确求出。记
\[
 \mathscr T_\phi(A,N):=\sqrt N\,{\cal M}_g^+(A,N;\phi).
\]
则对互素平方自由 \(A,N\)，CF19.51 就是
\[
 \boxed{\mathscr T_\phi(A,N)=\mathscr T_\Phi(N,A).}     \tag{CF19.55}
\]
令 \(\Omega\) 是任意有限、在 \((A,N)\leftrightarrow(N,A)\) 下不变的
互素平方自由 pair 集，且 \(w(A,N)=w(N,A)\)。定义
\[
 \mathscr S_\phi
 =\sum_{(A,N)\in\Omega}\mu(A)\mu(N)w(A,N)
                              \mathscr T_\phi(A,N).
\]
由 CF19.55 和换名立刻得到
\[
 \boxed{
 \mathscr S_\phi=\mathscr S_\Phi,
 \qquad \mathscr S_{\phi-\Phi}=0,
 \qquad \mathscr S_\phi={1\over2}\mathscr S_{\phi+\Phi}.} \tag{CF19.56}
\]
所以真正的 two-sided reciprocity 会**精确删除 test 的反对称部分**；
它没有估计剩下的对称部分。

这一点在物理 product shell 上不能再借 Möbius 符号补强。若
\(\omega(A)=r\)、\(\omega(N)=t\) 在 \(\Omega\) 上固定，则
\[
 \boxed{\mu(A)\mu(N)=(-1)^{r+t}\quad((A,N)\in\Omega).}  \tag{CF19.57}
\]
CF5F 已给出光滑 dyadic product cutoff 精确冻结固定 cardinality 的
构造；在两侧分别使用该构造即可得到非空、交换不变的 fixed-parity
壳。于是取任意非负对称 \(w\)，并在纯有限 countermodel 中置
\(\mathscr T_\phi=\mathscr T_\Phi=1\)，CF19.55 完全成立，而
\(|\mathscr S_\phi|=\sum_\Omega w\)，没有任何 cancellation。

这个 countermodel 只说明 **CF19.55 这条恒等式本身**不蕴含 family
saving；它不声称常数 trace 来自真实自守谱。只有先证明 actual QCT
的共同 Bessel/physical-shift adapter 确实把同一有限求和域识别成
CF19.55 的交换不变对象，并证明其权关于交换对称，CF19.56 才能无损
删除该 QCT 输出的全局反对称 Bessel-test 分量。即使这个 adapter
成立，所需幂次仍必须在剩余的对称分量上来自真实
Kloosterman/shift/Type 系数的联合振荡。特别是
“两侧都有 \(\mu\)”并不足够：在 fixed-\(\omega\) 壳上两侧符号都已
冻结。可验收的 CF19.L 因而必须直接控制这个 symmetric physical
family，或证明共同 reflection 把它和邻接 cardinality 壳重新耦合；
只引用 reciprocity 与 Möbius 符号不能闭合。

这三条是比“另证 continuous spectrum”更准确的剩余 adapter。HPY
全谱正性已经支付 Maaß--Eisenstein 的抽象 scalar inequality，经典
投影也精确恢复 CF7.1；但本文尚未证明实际 QCT 同时满足上述三条，
所以 CF19.41--CF19.44 仍不能宣布 CF19.L 闭合。

### CF19Z. odd--Hecke 零列的 exact-shell 几何界

CF19.32c 的普通系数平方质量有限，而带 Hecke-index 长度权的质量在
CF19.32e 发散；所以把它直接塞进普通谱大筛不是合法的极限过程。
不过，在几何侧可以先把同一个 odd--Hecke 列完整求和，而且得到比
逐谱绝对值强得多的**无条件壳界**。下面先把对象和所用假设冻结。

令 \(A,B,k,n\) 为正整数，\(A\) squarefree，
\[
 A>1,\qquad (A,B)=(A,kn)=1.
\]
令 \(\phi:(0,\infty)\to\mathbb C\) 满足：存在
\(J>1/2\)、\(K>0\) 与 \(C_\phi\)，使对所有 \(x>0\)
\[
 |\phi(x)|\le C_\phi\min(x^J,x^{-K}).                 \tag{CF19.58}
\]
对任一符号 \(\pm\)，定义
\[
 \begin{aligned}
 \mathfrak G_{A,B}^{\pm}(k,n;\phi)
 :=\sum_{\substack{t\ge1\\\operatorname{rad}(t)\mid A}}
 {1\over A^2t}
 \sum_{\substack{r\ge1\\(r,A)=1}}
 {S(At^2k,\pm n;ABr)\over ABr}\,
 \phi\!\left({4\pi t\sqrt{Akn}\over ABr}\right).
                                                               \tag{CF19.59}
 \end{aligned}
\]
因 \((A,B)=(A,r)=1\)，每个 \(p\mid A\) 在模数 \(ABr\) 中恰有
valuation one；所以 CF19.59 真的是 exact valuation-one shell，而
不是放宽后的全模数和。其数值系数 \(A^{-2}t^{-1}\) 与 CF19.32c
的 odd--Hecke 系数相同；但 CF19.59 又在 modulus 上额外施加了一次
exact-shell 条件。CF19Z7 将证明：若把二者串联，单素数局部谱和精确
为零。因此 CF19.59 只是一个辅助几何对象，不能据系数外形把它认作
CF19.32c 的物理实现，更不能再从中宣称一份 \(p^{-1}\) 或 shell
half-root saving。

对任意 \(0<\eta<J-1/2\) 和 \(Y>0\)，分 \(r\le Y\) 与 \(r>Y\)
（若 \(Y<1\)，前者为空），两个幂级数分别给
\[
 \sum_{r\ge1}r^{-1/2+\eta}
       \min\{(Y/r)^J,(Y/r)^{-K}\}
 \ll_{J,K,\eta}Y^{1/2+\eta}.                          \tag{CF19.60}
\]
这里在 \(r\le Y\) 用 \((Y/r)^{-K}\)，所得和为
\(Y^{-K}\sum_{r\le Y}r^{K-1/2+\eta}\ll Y^{1/2+\eta}\)；
在 \(r>Y\) 用 \((Y/r)^J\)，而
\(J>1/2+\eta\) 使尾和收敛并同样为 \(O(Y^{1/2+\eta})\)。这也覆盖
\(Y<1\)，因为此时 \(Y^J\le Y^{1/2+\eta}\)。

现在用 Weil 界的准确 gcd 形式
\[
 |S(a,b;c)|\le\tau(c)(a,b,c)^{1/2}c^{1/2}.
\]
由于 \(t\) 的每个素因子都整除 \(A\)，而 \((A,kn)=1\)，有
\[
 (At^2k,n,ABr)=(k,n,ABr)\le(k,n).
\]
再用 \(\tau(m)\ll_\eta m^\eta\)，并在 CF19.60 中置
\[
 Y={4\pi t\sqrt{Akn}\over AB},
\]
便得到固定 \(t\) 的内和绝对值至多
\[
 \begin{aligned}
 &\ll_{J,K,\eta,C_\phi}
 (k,n)^{1/2}(AB)^{-1/2+\eta}Y^{1/2+\eta},
 \end{aligned}
\]
从而乘上 \(A^{-2}t^{-1}\) 后为
\[
 \ll (k,n)^{1/2}B^{-1}
 A^{-11/4+\eta/2}(kn)^{1/4+\eta/2}t^{-1/2+\eta}.
\]
最后
\[
 \sum_{\operatorname{rad}(t)\mid A}t^{-1/2+\eta}
 =\prod_{p\mid A}(1-p^{-1/2+\eta})^{-1}
 \ll_{\varepsilon,\eta}A^\varepsilon
\]
（先吸收有限个小素数；对其余素数用
\(-\log(1-p^{-1/2+\eta})\le\varepsilon\log p\)）。选取
\[
 0<\eta<\min\{1/4,(J-1/2)/2,\varepsilon/4\},
\]
并把上一个 Euler 乘积中的幂取为至多 \(A^{\varepsilon/2}\)，便证明
双重级数绝对收敛且
\[
 \boxed{
 |\mathfrak G_{A,B}^{\pm}(k,n;\phi)|
 \ll_{J,K,\varepsilon,C_\phi}
 { (k,n)^{1/2}(kn)^{1/4+\varepsilon}
   \over B A^{11/4-\varepsilon}}.}                    \tag{CF19.61}
\]

CF19.58 把 test 的自然尺度归一为一；物理使用时不能把变化尺度藏入
\(C_\phi\)。更一般地，若存在 \(X_\phi>0\) 使
\[
 |\phi(x)|\le C_\phi
 \min\{(x/X_\phi)^J,(x/X_\phi)^{-K}\},
\]
就在 CF19.60 中改置
\(Y=4\pi t\sqrt{Akn}/(ABX_\phi)\)。同一证明逐字给
\[
 |\mathfrak G_{A,B}^{\pm}(k,n;\phi)|
 \ll { C_\phi(k,n)^{1/2}\over B}\,
 X_\phi^{-1/2-\eta}
 A^{-11/4+\eta/2}(kn)^{1/4+\eta/2}
 \prod_{p\mid A}(1-p^{-1/2+\eta})^{-1}.               \tag{CF19.61a}
\]
因此对每个 \(\varepsilon>0\)，CF19.61a 可简写为
\[
 |\mathfrak G_{A,B}^{\pm}(k,n;\phi)|
 \ll {C_\phi\over B\sqrt{X_\phi}}\,
 \max(1,X_\phi^{-\varepsilon})
 A^{-11/4+\varepsilon}(kn)^{1/4+\varepsilon}(k,n)^{1/2}.
                                                               \tag{CF19.61b}
\]
只有已经证明 \(X_\phi\) 位于物理参数的多项式范围时，才可把
\(\max(1,X_\phi^{-\varepsilon})\) 放入统一的 \(T^\varepsilon\)；
CF19.61 的 unit-scale 写法本身不授权这一步。

CF19.61 同时说明任一有限 odd--Hecke 截断的辅助几何边在截断参数上一致
可和；而 \(A>1\)、\((A,n)=1\) 还使第一 index \(At^2k\) 与第二
index \(n\) 永不相等，所以对应 primitive trace 的 Kronecker
diagonal 逐项为零。这是 CF19.33 的几何强化，并且 Maaß、holomorphic、
Eisenstein 的区分在这条纯 Kloosterman 估计中没有出现。

CF19.61 **不是** actual QCT 的全谱界。CF19Z2 只把 CF19.59 这个
辅助 exact-shell 几何级数识别成相应的完整 classical
Kuznetsov/Petersson regulated trace；CF19Z7 的单素数计算则证明，
该 trace 不能与 CF19.31--CF19.32c 的 local multiplier 再串联。
actual zero--zero 行的候选应是 CF19.85 的 lower-level trace。
把 CF19.85 接回原 complete-shift，并使 principal/axis/residue 行在
恢复整数格后进入同一个共同账本，仍属于未证 CF4/CF19.D/CF19.C。

### CF19Z2. 完整谱 exact-shell 由 level Möbius 容斥一次实现

CF19.59 的 exact-shell 几何边不需要逐谱猜测一个“valuation-one
Kuznetsov”。它可由普通 \(\infty\infty\) trace 在**取绝对值前**作
有限 level 容斥精确产生。从本节起，除 CF19.58 的点态界外，另假设
\(\phi\) 在 \([0,\infty)\) 上光滑、\(\phi(0)=0\)，并且存在
\(\delta_0>0\) 使
\[
 \phi^{(j)}(x)\ll(1+x)^{-2-\delta_0}\qquad(j=0,1,2).
                                                               \tag{CF19.61c}
\]
也就是说，CF19Z 的纯几何结论仍只需 CF19.58，而 CF19Z2 的每一条
谱恒等式都明确限于同时满足 CF19.61c 的 Kuznetsov-admissible tests。
为固定归一化，记
\(\operatorname{Spec}^{\pm}_N(m,n;\phi)\) 为 level \(N\)、trivial
character、cusp pair \(\infty\infty\) 的完整 Kuznetsov 谱边，约定
其几何边为
\[
 \begin{aligned}
 \operatorname{Spec}^{+}_N(m,n;\phi)
   &=\Delta_\phi{\bf1}_{m=n}
     +\sum_{\substack{c\ge1\\N\mid c}}
       {S(m,n;c)\over c}\phi\!\left({4\pi\sqrt{mn}\over c}\right),\\
 \operatorname{Spec}^{-}_N(m,n;\phi)
   &=\sum_{\substack{c\ge1\\N\mid c}}
       {S(m,-n;c)\over c}\phi\!\left({4\pi\sqrt{mn}\over c}\right).
                                                               \tag{CF19.62}
 \end{aligned}
\]
这里 \(+\) 边包含 Maaß、holomorphic 与全部 cusps 的 Eisenstein
谱，\(-\) 边包含带 parity 的 Maaß 与全部 Eisenstein 谱而
holomorphic 边为空；两个式子都使用 level \(N\) 的完整正交空间，
所以 oldforms 已包括，不能再另加 newform correction。
\(\Delta_\phi\) 是与 \(N\) 无关的同号 diagonal transform。
CF19.62 是经典 Bruggeman--Kuznetsov 的精确归一化；例如
[Andersen--Kıral §3, (3.3)--(3.14)](https://arxiv.org/html/1801.06089)
先对一般 cusp pair 定义谱边，并在 \(\infty\infty\) 时给
\(N\mid c\) 的经典 Kloosterman sum。该文 (3.10) 的条件
\(\phi(0)=0\) 与
\(\phi^{(j)}(x)\ll(1+x)^{-2-\delta}\), \(j=0,1,2\)，由中值定理在
\(x\le1\) 给 \(\phi(x)\ll x\)，在 \(x\ge1\) 给
\(\phi(x)\ll x^{-2-\delta}\)，故满足 CF19.58 的 \(J=1\)、
\(K=2+\delta\)。这里只使用“CF19.61c 蕴含 CF19.58”；点态条件
CF19.58 绝不反向蕴含 smoothness 或 trace admissibility。

对任意 \(c\)，有限 Möbius 反演给
\[
 \sum_{d\mid A}\mu(d){\bf1}_{ABd\mid c}
={\bf1}_{AB\mid c}\sum_{d\mid(A,c/(AB))}\mu(d)
 ={\bf1}_{AB\mid c}\,{\bf1}_{(c/(AB),A)=1}.            \tag{CF19.63}
\]
由于 \(A>1\)，同号 diagonal 的系数也精确为
\[
 \sum_{d\mid A}\mu(d)=0.                               \tag{CF19.64}
\]
把 CF19.62--CF19.64 合起，对每个固定
\(\operatorname{rad}(t)\mid A\) 得到完整谱恒等式
\[
 \boxed{
 \sum_{d\mid A}\mu(d)\,
 \operatorname{Spec}^{\pm}_{ABd}(At^2k,n;\phi)
 =
 \sum_{\substack{r\ge1\\(r,A)=1}}
 {S(At^2k,\pm n;ABr)\over ABr}
 \phi\!\left({4\pi t\sqrt{Akn}\over ABr}\right).}       \tag{CF19.65}
\]
这一步对 \(+\) 与 \(-\) 都成立；没有把 holomorphic 谱错误贴到
异号行，也没有遗漏 non-squarefree levels \(ABd\) 上的 oldforms
或 Eisenstein cusps。它还是一个**有限** level 恒等式，所以没有
Fubini 或 varying-level 收敛假设。

令 \(\mathcal T\) 递增遍历所有只含 \(A\)-素因子的有限 \(t\) 集。
将 CF19.65 乘 \(A^{-2}t^{-1}\) 后对 \(t\in\mathcal T\) 求和，得到
\[
 \begin{aligned}
 \sum_{t\in\mathcal T}{1\over A^2t}
   \sum_{d\mid A}\mu(d)
     \operatorname{Spec}^{\pm}_{ABd}(At^2k,n;\phi)
 =\mathfrak G^{\pm}_{A,B;\mathcal T}(k,n;\phi).         \tag{CF19.66}
 \end{aligned}
\]
CF19.61 证明右边在 \(\mathcal T\uparrow
\{t:\operatorname{rad}(t)\mid A\}\) 时绝对收敛，故左边作为一个**整体
regulated full-spectrum trace** 有唯一极限，而且该极限就是
\(\mathfrak G^{\pm}_{A,B}\)，并满足 CF19.61。这里没有把 \(t\)-极限
分别移入 Maaß、holomorphic 或 Eisenstein 和；CF19.32e 已说明那种
逐谱交换不能由普通大筛支配。

这也精确标出 Andersen--Kıral reciprocity 不能直接补上的缝。该文
(3.12)--(3.14) 用于 reciprocity 的 \(0\infty\) 几何核是
\[
 \sum_{(c,N)=1}{S(\overline N m,n;c)\over c\sqrt N}
       \phi\!\left({4\pi\sqrt{mn}\over c\sqrt N}\right),
                                                               \tag{CF19.67}
\]
而 CF19.62--CF19.65 的 \(\infty\infty\) exact shell 要求
\(AB\mid c\)，归一化是 \(1/c\)，且没有 inverse-\(N\) index。
所以 CF19.51 的 \(0\infty\) level reciprocity 不能逐项识别为
CF19.65，也不能据此赠送 \(A^{-1/2}\)。现在已经闭合的是
“完整谱有限 level 容斥 \(\leftrightarrow\) exact-shell 几何边”
以及它的 regulated odd--Hecke 极限；仍开放的是原 QCT 反射是否以
**同一个 regulator 和同一个 \(\infty\infty\) test** 产生 CF19.66，
以及 principal/axis/residue 四行是否在恢复整数格后进入这份共同账本。

### CF19Z3. 两条 dyadic Hecke 列的一次 Schur 装配

CF19.61b 还允许先在几何侧装配全部 \(k,n\)，而不用把 test 强行改成
逐 pair 相同。令 \(\mathcal K\subset[K_0,2K_0]\cap\mathbb N\)、
\(\mathcal N\subset[N_0,2N_0]\cap\mathbb N\)，并令每个
\(\phi_{k,n}\) 都满足 CF19.61b 的同一 \(J,K,C_\phi,X_\phi\) 界。
若只调用下面的几何 Schur bound，不需要 CF19.61c；若还要把每项解释为
CF19.65 的 full-spectrum trace，则每个 \(\phi_{k,n}\) 还必须分别
满足 CF19.61c。
对矩阵
\[
 H_{k,n}=(k,n)^{1/2}
\]
有
\[
 \begin{aligned}
 \sup_{k\in\mathcal K}\sum_{n\in\mathcal N}H_{k,n}
 &\le\sup_k\sum_{d\mid k}d^{1/2}(2N_0/d+1)
 \ll_\varepsilon(N_0+K_0^{1/2})(K_0N_0)^\varepsilon,\\
 \sup_{n\in\mathcal N}\sum_{k\in\mathcal K}H_{k,n}
 &\ll_\varepsilon(K_0+N_0^{1/2})(K_0N_0)^\varepsilon.
                                                               \tag{CF19.68}
 \end{aligned}
\]
第一行只用
\((k,n)^{1/2}\le\sum_{d\mid(k,n)}d^{1/2}\)、
\(\sigma_{-1/2}(k),\tau(k)\ll_\varepsilon k^\varepsilon\)；
第二行对称。Schur test 因而给
\[
 \|H\|_{\ell^2(\mathcal N)\to\ell^2(\mathcal K)}
 \ll_\varepsilon
 \{(N_0+K_0^{1/2})(K_0+N_0^{1/2})\}^{1/2}
 (K_0N_0)^\varepsilon.                                \tag{CF19.69}
\]
对任意有限标量列 \(x_k,y_n\)，CF19.61b、逐项 domination 与
CF19.69 遂给
\[
 \begin{aligned}
 \left|\sum_{k\in\mathcal K}\sum_{n\in\mathcal N}
 x_k y_n\mathfrak G_{A,B}^{\pm}(k,n;\phi_{k,n})\right|
 \ll_\varepsilon{}&
 {C_\phi A^{-11/4+\varepsilon}\over B\sqrt{X_\phi}}\,
 \max(1,X_\phi^{-\varepsilon})(K_0N_0)^{1/4+\varepsilon}\\
 &\times
 \{(N_0+K_0^{1/2})(K_0+N_0^{1/2})\}^{1/2}
 \|x\|_2\|y\|_2.                                     \tag{CF19.70}
 \end{aligned}
\]
特别地，若 \(K_0^{1/2}\le N_0\) 且 \(N_0^{1/2}\le K_0\)，长度费用
简化为 \((K_0N_0)^{3/4+\varepsilon}\)。

CF19.70 的优点是允许 \(\phi_{k,n}\) 随 pair 变化；代价是已经对
\(k,n\) 取 pointwise majorant，不能再把这个 bound 与另一份谱大筛
saving 相乘。它只装配 CF19.59 这个辅助 exact-shell 对象；CF19Z7
证明，把 actual CF19.32c 再接到 CF19.59 会重复 shell 并精确杀掉
局部零块。actual QCT 应改接 CF19.85；即使如此，也必须证明同一个
\(C_\phi,X_\phi\) 一致控制全部 AFE、detector、reflection 与 endpoint
tags，并核对 lower-level harmonic measure。这个任务仍属 CF19.D/CF4；
没有该 seminorm/尺度和谱归一化证明，CF19.70 只是辅助 supplier。

### CF19Z4. 固定 dyadic 模数权消掉 Hecke-index 长度

CF19.61a 中的尺度在真实 dyadic modulus weight 上还会与
\((kn)^{1/4}\) 精确抵消。这个事实可完全留在几何侧证明。令
\(C_0>0\)，并对每个 \(\operatorname{rad}(t)\mid A\) 给一个有界
函数 \(W_t:(0,\infty)\to\mathbb C\)，满足
\[
 \operatorname{supp}W_t\subset[1/2,2],
 \qquad \sup_t\|W_t\|_\infty\le C_W.
\]
定义
\[
 \begin{aligned}
 \mathfrak H_{A,B;C_0}^{\pm}(k,n;\boldsymbol W)
 :=\sum_{\substack{t\ge1\\\operatorname{rad}(t)\mid A}}
 {1\over A^2t}
 \sum_{\substack{r\ge1\\(r,A)=1}}
 {S(At^2k,\pm n;ABr)\over ABr}\,
 W_t\!\left({ABr\over C_0}\right).                     \tag{CF19.71}
 \end{aligned}
\]
这里不要求不同 \(t\) 使用同一个函数，也暂不要求 \(W_t\) 光滑。
固定 \(0<\eta<1/2\)。Weil 界及 CF19Z 中同一个 gcd 恒等式先给
\[
 \begin{aligned}
 &\sum_{\substack{r\ge1\\(r,A)=1}}
 \left|{S(At^2k,\pm n;ABr)\over ABr}
 W_t\!\left({ABr\over C_0}\right)\right|\\
 &\qquad\ll_{\eta}C_W(k,n)^{1/2}(AB)^{-1/2+\eta}
 \sum_{r\asymp C_0/(AB)}r^{-1/2+\eta}
 \ll_\eta {C_W(k,n)^{1/2}C_0^{1/2+\eta}\over AB}.
                                                               \tag{CF19.72}
 \end{aligned}
\]
若 \(C_0/(AB)<1/2\)，内和为空；否则最后一步是一个长度
\(\asymp C_0/(AB)\) 的初等幂和。关键是
\((AB)^{-1/2+\eta}(C_0/(AB))^{1/2+\eta}
=C_0^{1/2+\eta}/(AB)\)：所有 \(\eta\)-幂在 \(AB\) 上也精确抵消。
于是
\[
 \boxed{
 |\mathfrak H_{A,B;C_0}^{\pm}(k,n;\boldsymbol W)|
 \ll_\eta
 {C_W(k,n)^{1/2}C_0^{1/2+\eta}\over A^3B}
 \prod_{p\mid A}(1-p^{-1})^{-1}
 \ll_{\varepsilon}
 {C_W(k,n)^{1/2}C_0^{1/2+\varepsilon}
  \over B A^{3-\varepsilon}}.}                         \tag{CF19.73}
\]
第一界中的 Euler 乘积是精确的 \(t\)-质量：
\[
 \sum_{\operatorname{rad}(t)\mid A}{1\over t}
 =\prod_{p\mid A}(1-p^{-1})^{-1};
\]
第二界仍由“有限个小素数吸入常数，其余局部对数至多
\(\varepsilon\log p\)”得到；非空情形还有 \(C_0\ge AB/2\ge1\)，
故可取 \(0<\eta\le\varepsilon\) 并把 \(C_0^{1/2+\eta}\) 放宽为
\(C_0^{1/2+\varepsilon}\)。这里不再出现
\(\sum_t1\) 或 Hecke-index length，所以没有使用 CF19.32e 中发散的
大筛权。

若 \(W_t\) 光滑，CF19.71 还可逐 \(t,k,n\) 精确放回 CF19.65。置
\[
 X_{t,k,n}={4\pi t\sqrt{Akn}\over C_0},\qquad
 \phi_{t,k,n}(x)=W_t(X_{t,k,n}/x).
 \]
则
\[
 \phi_{t,k,n}\!\left({4\pi t\sqrt{Akn}\over ABr}\right)
 =W_t(ABr/C_0).                                       \tag{CF19.74}
\]
因 \(W_t\) 支撑离开零与无穷，\(\phi_{t,k,n}\) 对每个固定
\((t,k,n)\) 都是 compactly supported Kuznetsov-admissible test；
其自然尺度正是
\(X_{t,k,n}=t\{4\pi\sqrt{Akn}/C_0\}\)。此处不能把已经对
全部 Hecke indices 求和的 CF19.61a 再逐 \(t\) 调用；应回到其
证明中紧邻 CF19.60 之后、对 \(t\) 求和之前的 fixed--\(t\) 界。
在该界中代入这个尺度，
\(t^{-1/2+\eta}X_{t,k,n}^{-1/2-\eta}\) 恰留下
\(t^{-1}\)，而
\((kn)^{1/4+\eta/2}X_{0,k,n}^{-1/2-\eta}\) 恰消去全部 \(kn\)
幂并再给 \(A^{-1/4-\eta/2}C_0^{1/2+\eta}\)；这与直接证明
CF19.72--CF19.73 完全一致。

最后对 CF19Z3 的 \(\mathcal K,\mathcal N,x_k,y_n\) 用同一个 gcd
矩阵 Schur test，直接得到
\[
 \begin{aligned}
 \left|\sum_{k\in\mathcal K}\sum_{n\in\mathcal N}
 x_ky_n\mathfrak H_{A,B;C_0}^{\pm}(k,n;\boldsymbol W)\right|
 \ll_\varepsilon{}&
 {C_WC_0^{1/2+\varepsilon}\over BA^{3-\varepsilon}}
 \{(N_0+K_0^{1/2})(K_0+N_0^{1/2})\}^{1/2}\\
 &\times(K_0N_0)^\varepsilon\|x\|_2\|y\|_2.           \tag{CF19.75}
 \end{aligned}
\]
在 CF19.70 的非极端失衡域，长度费用是
\((K_0N_0)^{1/2+\varepsilon}\)，不是
\((K_0N_0)^{3/4+\varepsilon}\)。

CF19.73--CF19.75 是固定模数壳、允许 test 随 \(t\) 变化的
exact-shell 辅助几何 supplier；它允许 \(W_t\) 带全部已经固定的
AFE/detector/reflection tags，只要求同一 \(\ell^\infty\) 预算。
但这还不是“actual common test 直接可用”：同一物理 Bessel test
在 Hecke index 从 \(Ak\) 改为 \(At^2k\) 时不会自动换成
\(\phi_{t,k,n}\)。它仍不证明原物理系数展开后恰有 CF19.71 的
\(A^{-2}t^{-1}\)、第一 index \(At^2k\) 与 modulus \(ABr\)，也不估计
剩余三个 local states、另一 shell、principal/axis/residue 或
native complement。因此下一项 adapter 已缩成这三个**系数等同性**
与余下行的共同分账，不能把 CF19.75 称为 CF19.L 或 CF9.1。

### CF19Z5. actual common test 使 dyadic 模数壳随 \(t\) 移动

上一节的 test--shell 对应必须在物理 common-test 约定下重做。
设 \(C_0\ge AB/2\)，\(W:(0,\infty)\to\mathbb C\) 有界、
支撑于 \([1/2,2]\)，且 \(\|W\|_\infty\le C_W\)，并置
\[
 X_{k,n}={4\pi\sqrt{Akn}\over C_0},\qquad
 \phi_{k,n}(x)=W(X_{k,n}/x).                            \tag{CF19.76}
\]
下面的几何界只需有界性；若还要以 CF19.65 把它解释成
full-spectrum trace，则另要求 \(W\) 光滑，使 \(\phi_{k,n}\)
满足 CF19.61c。
对 base index \(Ak\)，CF19.76 在 \(c=ABr\) 上恰给
\(W(c/C_0)\)。但 odd--Hecke 展开后仍使用**同一**
\(\phi_{k,n}\)；第一 index \(At^2k\) 的 Bessel argument 多一个
\(t\)，所以精确变成
\[
 \phi_{k,n}\!\left({4\pi t\sqrt{Akn}\over ABr}\right)
   =W\!\left({ABr\over tC_0}\right).                  \tag{CF19.77}
\]
因而 actual common test 对应的模数壳是
\(ABr\asymp tC_0\)，不是 CF19.71 的 \(ABr\asymp C_0\)。
要在后者中固定 \(C_0\)，必须把 common test 换成
\(\phi_{t,k,n}(x)=W(tX_{k,n}/x)\)；这一换不是迹公式的
自动结论。

好消息是，移动壳可以直接求和，不必伪造一族
\(t\)-dependent tests。在 CF19.59 中代入 CF19.76。对固定
\(t\)，CF19.72 的同一 Weil 计数只须把 \(C_0\) 换为
\(tC_0\)；再乘外系数 \(A^{-2}t^{-1}\)，得
\[
 {C_W(k,n)^{1/2}C_0^{1/2+\eta}\over A^3B}\,
 t^{-1/2+\eta}.
\]
故对 \(0<\eta<1/2\)，
\[
 \boxed{
 |\mathfrak G_{A,B}^{\pm}(k,n;\phi_{k,n})|
 \ll_\eta
 {C_W(k,n)^{1/2}C_0^{1/2+\eta}\over A^3B}
 \prod_{p\mid A}(1-p^{-1/2+\eta})^{-1}
 \ll_\varepsilon
 {C_W(k,n)^{1/2}C_0^{1/2+\varepsilon}
  \over BA^{3-\varepsilon}}.}                          \tag{CF19.78}
\]
第二界取 \(\eta<\min(1/2,\varepsilon)\)，并像 CF19.61 一样
把有限个小素数吸入常数。这里 \(t\)-质量不是
CF19.73 的 \(\prod(1-p^{-1})^{-1}\)，而是 CF19.78 显示的
\(\prod(1-p^{-1/2+\eta})^{-1}\)；两者都只付 \(A^\varepsilon\)，
但不能在局部账上互换。

对 dyadic \(k,n\) 与一致的 \(\|W_{k,n}\|_\infty\le C_W\)，
再用 CF19.69 得到与 CF19.75 相同的
\((K_0N_0)^{1/2+\varepsilon}\) 非极端长度费用。因此
“common test 导致移动壳”不会恢复 CF19.32e 的发散 length
费用；它只否定了把 CF19.71 本身逐物理 box 等同的错误。
仍需 CF19.D 证明原始 quotient-Poisson 核在同一尺度
\(X_{k,n}\) 上真正可写成 CF19.76，且全部 endpoint/
reflection tags 具有共同 \(C_W\) 预算。CF19.78 仍只是
common-test exact-shell 的辅助几何 supplier；CF19Z7 将证明它不能和
CF19.32c 串联。它也不估计其他 local states 或
principal/axis/residue/native 行。

### CF19Z6. 原 Type-I/Type-I bulk 的几何 test/scale 映射

现在只返回 MWKF-PHYS-v1 的字面原子，不借用 CF4 的未证
全谱等同。在一个 Type-I/Type-I expanded--expanded bulk 行中写
\[
 r=A\ell,\qquad s=Bm,\qquad (A,Bm)=1,\qquad n=h\delta,
                                                               \tag{CF19.79}
\]
其中 \(A,B\) 平方自由，\(\ell,m\) 是展开后的无权 quotient。
固定 \(s,h,\delta\) 及其他有限 tags，把原 CF2.1 中依赖
\(r=A\ell\) 的全部 archimedean/taper 因子（显式
\((A\ell,s)=1\) mask 除外）写成支撑于
\(u=A\ell/R\asymp1\) 的光滑函数 \(f_{s,n}(u)\)。
主笔记 §412 的精确 quotient Poisson
与 corrected lift 给
\[
 R\sum_{k\in\mathbb Z}
 \widehat f_{s,n}\!\left({kR\over As}\right)
 {S(Ak,-n;As)\over As\,c_A(n)}.                       \tag{CF19.80}
\]
这里 \(R\) 是 CF2.3 中唯一的 Poisson Jacobian；
\(1/(As)\) 已是 classical trace 的 \(1/c\)，不允许再加
\(\sqrt{As}\) 或第二份 \(R\)。CF3.2 中的 \(\mu(A)\) 与
CF19.80 的 \(c_A(n)^{-1}\) 合并且只合并一次，成为 CF7.5 的
\(\mu(A)/c_A(n)\)；\(\mu(B)\) 与原 mollifier/taper 标量仍留在外面。
CF19.80 只冻结
Kloosterman 行的 Jacobian、indices 与 modulus。

令 \(c=As=ABm\) 及 \(C_0=AS\)。因 \(B\mid s\) 且
\(s\le2S\)，有 \(C_0\ge AB/2\)，正满足 CF19Z5 的尺度前提。
由原 \(s\asymp S\) 的光滑
dyadic cutoff，zero--zero 子行中余下的完整几何权可定义为
\[
 W_{k,n}(z):=
   \bigl[\text{CF2.1 的余下 normalized weight 及
   quotient Fourier transform}\bigr]_{\,s=Sz,\;
          \xi=kR/(C_0z)}.                               \tag{CF19.81}
\]
这不是一个代理权：括号内是原有限 atom 逐字节在
\(s=Sz\) 的取值。它支撑于 \(z\in[1/2,2]\)。且由
\[
 |\widehat f_{s,n}(\xi)|\le\|f_{s,n}\|_1
\]
及 \(u\) 的固定紧支撑，对每个已经固定的 literal atom 有
\[
 \sup_{k,n}\|W_{k,n}\|_\infty
 \ll \mathcal A_0(\text{该 atom}).                     \tag{CF19.81a}
\]
这句话不把 \(\mathcal A_0\) 宣称为绝对常数：MWKF-PHYS-v1 §3 的
内部族有一致 \(O_{W,F}(1)\) 预算，更大的 core 必须保留原登记的
\(\mathcal A_J\) 费用。若把有限 AFE/detector/reflection tags 一起
取最大值，CF19.81a 仍只支付该最大值，没有新增 \(A,B,m\) 幂。
这里“没有新增”是指除 \(\mathcal A_J\) 已显式登记的参数依赖外，
不再复制一份隐藏费用。
原域若还保留 \((m,Bq_0)=1\) 或其他 quotient mask，它们不塞进
\(W_{k,n}\)：CF19.78 的纯几何绝对界对删项仍成立，但 CF19.65 的
完整谱恒等式不能据此忽略这些 mask；其精确 inclusion--exclusion
仍归 CF4。
若还要求统一的 spectral derivative seminorm，则必须对 CF19.81 的
\(z\)-导数逐项证明原核的 Sobolev pullback 并再用 CF19.9；这部分
仍属 CF19.D，不由上面的 \(L^\infty\) 界自动推出。

对 \(k,n\ne0\) 取绝对值并把符号放入 \(\pm\) Kloosterman 行。
在 zero--zero 局部状态中
\((A,|kn|)=1\)，因而置
\[
 X_{k,n}={4\pi\sqrt{A|kn|}\over C_0},\qquad
 \phi_{k,n}(x)=W_{k,n}(X_{k,n}/x)
\]
就有字面恒等式
\[
 W_{k,n}(c/C_0)
 =\phi_{k,n}\!\left({4\pi\sqrt{A|kn|}\over c}\right).
                                                               \tag{CF19.82}
\]
所以 Type-I/Type-I bulk 的**几何** common test、尺度
\(C_0=AS\)、base index \(Ak\) 与 modulus \(ABm\) 已逐项对上
CF19.76。

然而 CF19.80 本身没有 \(A^{-2}t^{-1}\)。该系数只在对 actual shell
的 zero--zero local state 应用 CF19.31--CF19.32c 后出现；而
CF19Z7 证明，不能再把所得 odd--Hecke 列送进 CF19Z2 的 exact-shell
trace。正确候选是：由 CF4 在完整 Maaß/holomorphic/Eisenstein
归一化中把该列降到 CF19.85 的 level-\(B\) trace，CF19.80 只负责
核对原 Poisson 的 base index、modulus scale 与唯一外因子 \(R\)。
在 CF4 闭合前，不能把这些条目拼成已证的 actual spectral bound。
而且 CF19.79--CF19.82 只处理
expanded--expanded Type-I/Type-I 的非零 bulk；四个 quotient endpoint、
Type-II、\(k=0\)、axes、principal/residue 与 native complement 均未因此获得
新覆盖。

### CF19Z7. 再套 exact shell 会精确杀掉零块；正确候选降到 level \(B\)

CF19Z--CF19Z5 的几何不等式本身正确，但它们不能作为 CF19.32c 的
zero--zero 物理实现。原因可在一个 prime 上精确看见。固定
\(p\nmid B\)，令
\[
 \Delta_p(y)=(1+y)^2-\lambda_1^2y.
\]
Hecke recurrence 的奇偶生成函数分别是
\[
 \sum_{a\ge0}\lambda_{2a+1}y^a={\lambda_1\over\Delta_p(y)},
 \qquad
 \sum_{a\ge0}\lambda_{2a}y^a={1+y\over\Delta_p(y)}.     \tag{CF19.83}
\]
CF19.32a 前的 Kim--Sarnak majorant 同时控制奇、偶两列，所以二者在
\(y=1/p\) 都绝对收敛。
CF7.4a 对所有 \(j\ge1\) 给 \(P_2(j,0)=0\)，故
\[
 D_p(j,0)=P_1(j,0)
 ={\,\lambda_j-\dfrac p{p+1}\lambda_1\lambda_{j-1}\,
   \over(p+1)\rho_p}.
\]
因此在 \(y=1/p\) 处绝对收敛地有
\[
 \begin{aligned}
 \sum_{a\ge0}{D_p(2a+1,0)\over p^{a+2}}
 &={p^{-2}\lambda_1\over(p+1)\rho_p\Delta_p(1/p)}
   \left\{1-{p\over p+1}\left(1+{1\over p}\right)\right\}\\
 &=0.                                                       \tag{CF19.84}
 \end{aligned}
\]
这不是少算一个 \(p^{-1}\) 的量级警告，而是精确的零；例如局部取
\(p=2,\lambda_1=1\) 时，左边仍为零，而
\(D_2(1,0)=1/7\ne0\)。CF19.32a 已把
原 shell zero--zero coefficient \(D_p(1,0)\) 展成
\(\sum_a p^{-a-2}\lambda_{2a+1}\)。若再把每个 odd-Hecke 项送入
CF19.65 的 exact-shell trace，则在这个 unramified oldclass 分量上
又乘 \(D_p(2a+1,0)\)，恰得到 CF19.84，而不是 \(D_p(1,0)\)。所以
\[
 \boxed{\text{CF19.32c 的 odd--Hecke 系数与 CF19Z2 的 level
 inclusion--exclusion 不可串联。}}
\]
这正是“harmonic \(1/p\) 或 local \(O(1/p)\) 不能重复计算”的一个
精确反例。

不重复 shell 的 classical candidate 是把 prime \(A\) 从 level 中
降掉。定义
\[
 \begin{aligned}
 \mathfrak L_{A,B}^{\pm}(k,n;\phi)
 :=\sum_{\substack{t\ge1\\\operatorname{rad}(t)\mid A}}
 {1\over A^2t}
 \sum_{r\ge1}
 {S(At^2k,\pm n;Br)\over Br}\,
 \phi\!\left({4\pi t\sqrt{Akn}\over Br}\right).
                                                               \tag{CF19.85}
 \end{aligned}
\]
这里仍假设 \(A>1\) 平方自由、\((A,Bkn)=1\)。令 \(\mathcal T\)
是只含 \(A\)-素因子的正整数所成的任意有限集。若 \(\phi\) 还满足
CF19.61c 的 classical Kuznetsov
admissibility，普通 level-\(B\) 全谱公式（采用 CF19.62 的同一
harmonic/Fourier 归一化）逐项给
\[
 \sum_{t\in\mathcal T}{1\over A^2t}
   \operatorname{Spec}^{\pm}_{B}(At^2k,n;\phi)
 =\mathfrak L_{A,B;\mathcal T}^{\pm}(k,n;\phi),          \tag{CF19.86}
\]
且同号 diagonal 因 \(At^2k\ne n\) 为零。按 CF19.62 的 \(\pm\)
约定，level \(B\) 的 Maaß、同号 holomorphic、oldforms 与全部
Eisenstein cusps 都保留（异号 holomorphic 行为空）；因
\((A,B)=1\)，它们在每个 \(p\mid A\) 都是 unramified datum，
所以 CF19.32c 的 Hecke 关系可在同一 full spectrum 上逐项使用。
当 \(\mathcal T\) 穷尽全部 \(A\)-smooth \(t\) 时，下面 CF19.87 的
绝对界使几何右边收敛，从而定义唯一的 aggregate regulated
full-spectrum limit；这里不交换 \(t\)-极限与任何单独谱和。
这说明 CF19.85--CF19.86 是 zero--zero local multiplier 的正确
classical trace **candidate**。把它等同于 actual CF19.80 的
zero--zero 行仍要求 CF4 证明 level lowering、Fourier/harmonic measure
与连续谱归一化完全一致；本文不从局部生成函数反推该全局等同。

CF19.85 的几何边不需谱解释即可估计。对满足 CF19.58 的 test，重复
CF19.60--CF19.61，但把 modulus \(ABr\) 换成 \(Br\)。这里即使
\(r\) 含 \(A\)-素因子也仍有
\((At^2k,n,Br)=(k,n,Br)\le(k,n)\)，因为 \((At,n)=1\)。于是得到
\[
 |\mathfrak L_{A,B}^{\pm}(k,n;\phi)|
 \ll_{\varepsilon}
 {C_\phi(k,n)^{1/2}(kn)^{1/4+\varepsilon}
  \over BA^{7/4-\varepsilon}}.                         \tag{CF19.87}
\]
若进一步使用 actual-common-test 形状 CF19.76，则
\[
 \phi_{k,n}\!\left({4\pi t\sqrt{Akn}\over Br}\right)
   =W_{k,n}\!\left({Br\over tC_0}\right),
\]
固定 \(t\) 的 Weil 和支撑于 \(Br\asymp tC_0\)。乘
\(A^{-2}t^{-1}\) 并求全部 \(A\)-smooth \(t\)，严格给
\[
 \boxed{
 |\mathfrak L_{A,B}^{\pm}(k,n;\phi_{k,n})|
 \ll_\varepsilon
 {C_W(k,n)^{1/2}C_0^{1/2+\varepsilon}
  \over BA^{2-\varepsilon}}.}                          \tag{CF19.88}
\]
其 \(t\)-Euler 乘积仍是 CF19.78 的
\(\prod_{p\mid A}(1-p^{-1/2+\eta})^{-1}\)。对两条非极端 dyadic
\(k,n\) 列再用 CF19.69，长度费用仍为
\((K_0N_0)^{1/2+\varepsilon}\)。

CF19.88 比 CF19.78 少一个 \(A^{-1}\)，正因为 level-\(B\) 几何边
不再人为要求 \(A\mid c\)。这不是损失，而是删除重复 shell density
后的正确账。下一条真正需要核验的命题因此不再是把 actual row 接到
CF19Z2，而是：CF4 的 completed Maaß/holomorphic/Eisenstein
normalization 是否把 CF19.80 的 zero--zero oldspace 差核无损降为
CF19.86，同时把其余 local states、principal、axes 与 residues 留在
同一个有限系数不等式中。下一节先关闭其中逐 datum、共同有限
regulator 的 unramified oldclass multiplier 部分。

### CF19Z8. unramified oldclass 的 lower-level multiplier 在有限 regulator 内精确相同

上一节的 candidate 至少在每个 unramified oldclass 上可以完全核对，
不需要猜测 trace 归一化。固定 level \(B\) 的一个 spectral datum
\(\pi\)；这里可分别取 Maaß、holomorphic 或任一 Eisenstein cusp
datum，并固定其 parity/cusp label。因 \((A,Bkn)=1\)，对每个
\(p\mid A\)，\(\pi_p\) unramified，且
\[
 \lambda_\pi(At^2k)=\lambda_\pi(At^2)\lambda_\pi(k)
 \qquad(\operatorname{rad}(t)\mid A).                  \tag{CF19.89}
\]
CF7.2--CF7.4 又直接说明：在由这个 \(\pi\) 生成的 level \(ABd\)
oldclass 中，有限 level difference
\(\sum_{d\mid A}\mu(d)\operatorname{Spec}_{ABd}\) 的 zero--zero
局部系数正是 \(\prod_{p\mid A}D_{p,\pi}(1,0)\)。另一方面，
CF19.32c 是逐 datum 的绝对收敛恒等式
\[
 \boxed{
 \prod_{p\mid A}D_{p,\pi}(1,0)
 =\sum_{\substack{t\ge1\\\operatorname{rad}(t)\mid A}}
   {\lambda_\pi(At^2)\over A^2t}.}                    \tag{CF19.90}
\]

令 \(\mathscr W_\pi(k,n;\phi)\) 表示 CF19.62 的 level-\(B\)
谱边中这个 datum 的 base harmonic/Fourier/Bessel 权；同一个 test
意味着它的 Bessel transform 不随 Fourier indices 改变。把
CF19.89--CF19.90 相乘，在任意有限 discrete spectral regulator 内，
以及任意 compact Eisenstein regulator 内（其权可积且上面的局部级数
对 Maaß 用 Kim--Sarnak、对 holomorphic 用 Deligne、对实轴
Eisenstein 用 \(|\lambda_{it}(p^j)|\le j+1\) 一致控制），有
\[
 \begin{aligned}
 &\sum_\pi \mathscr W_\pi(k,n;\phi)
       \prod_{p\mid A}D_{p,\pi}(1,0)\\
 &\qquad=
 \lim_{\mathcal T}
 \sum_{t\in\mathcal T}{1\over A^2t}
 \sum_\pi \mathscr W_\pi(At^2k,n;\phi).              \tag{CF19.91}
 \end{aligned}
\]
这里 \(\mathcal T\) 穷尽全部 \(A\)-smooth 正整数；两边始终使用
**同一个** regulator，故 CF19.91 没有交换无限 full spectrum 与
\(t\)-极限。它证明 CF19.85 不是仅凭幂次猜出的替代物：它逐 datum
精确再现 exact-shell level difference 的 unramified zero--zero
oldclass 分量，而且 harmonic \(P_1(0,0)\) 已包含在 \(D_p\) 中一次。

CF19.91 仍没有处理 conductor 含某个 \(p\mid A\) 的 ramified
newspace/oldspace 数据，也没有证明解除共同 regulator 后，actual
complete-shift 的全部局部状态恰等于 CF19.86 加这些 ramified
remainder。连续谱的所有 cusp labels 在 CF19.91 中被逐 datum 保留，
但把它们与 principal/axis/residue 行共同压缩仍属 CF4/CF19.C。
因此这里关闭的是 **finite-regulator unramified oldclass multiplier**，
不是 full-spectrum physical adapter。

### CF19Z9. Steinberg 行是 rank one；全部导子模式只给一份 shell half-root

CF19Z8 留下的 ramified 局部类型可在当前 zero--zero 方向上继续精确
分类。先取 primitive conductor exponent one。平凡中心特征强制其为
\(\pi_p=\chi\mathrm{St}\)，其中
\[
 \lambda_j:=\lambda_\pi(p^j)=\epsilon^jp^{-j/2},qquad
 \epsilon\in\{1,-1\}.
\]
置
\[
 q=p+1,qquad r_p={p(p+2)\over q^2}.
\]
采用 [Blomer--Milićević, Lemma 2](https://arxiv.org/abs/1404.7845)
的 exact oldclass convention。取 degeneracy map \(f|_p\) 的 \(L^2\) 归一化，使其 normalized
Fourier coefficient 为 \(\sqrt p\,\lambda_{j-1}\)。局部 Hecke
double-coset 内积直接给
\[
 \|f\|=\|f|_p\|=1,
 \qquad \langle f|_p,f\rangle={\epsilon\over p+1}.
\]
因此 Gram--Schmidt 说明 level \(p^2\) 的完整两维 oldclass 正交基
是原 newvector \(f\) 与
\[
 f^{(p)}=r_p^{-1/2}\left(f|_p-{\epsilon\over q}f\right).
                                                               \tag{CF19.92}
\]
在 normalized Fourier coefficients 中，第二个向量在 valuation
\(j\) 的系数为
\[
 U(j)=r_p^{-1/2}
 \left(\sqrt p\,\lambda_{j-1}-{\epsilon\over q}\lambda_j\right),
 \qquad \lambda_{-1}=0.                                \tag{CF19.93}
\]
直接代入 \(\lambda_j=\epsilon^jp^{-j/2}\)，对 \(j\ge1\) 得
\[
 {U(0)U(j)\over\lambda_j}=-{pq-1\over q^2r_p}.          \tag{CF19.94}
\]

因为 \([\Gamma_0(p):\Gamma_0(p^2)]=p\)，level \(p\) newvector
trace 与 level \(p^2\) oldclass trace 的 ambient harmonic
normalization 比是 \(1:p^{-1}\)。故其 exact level
difference 在 valuations \((0,j)\) 上为
\[
 \mathcal K_p^{(1)}(0,j)
 =\lambda_j-{1\over p}\{\lambda_j+U(0)U(j)\}.
\]
当前 corrected lift 的 denominator 是 unit-side 的
\(c_p(1)=-1\)。由 CF19.94 清分母得到
\[
 \boxed{
 {\mathcal K_p^{(1)}(0,j)\over c_p(1)}
 =-C_{p,0}\lambda_j,qquad
 C_{p,0}=1-{p+1\over p^2(p+2)},qquad j\ge1.}           \tag{CF19.95}
\]
CF19.95 是尚未乘回 CF3.2 外层 \(\mu(p)=-1\) 的 normalized
corrected-lift 行。裸 level-
\(p\) minus level-\(p^2\) kernel 本身则是
\(\mathcal K_p^{(1)}(0,j)=+C_{p,0}\lambda_j\)；在 actual unit-side
zero--zero 行中，\(\mu(p)/c_p(1)=1\)，所以最终物理乘子同样取
\(+C_{p,0}\lambda_j\)，不能把 CF19.95 的中间负号再保留一次。
Kloosterman/spectral kernel 对两个 Fourier indices 对称，故这是
CF19.80 中首 index valuation \(j\ge1\)、第二 index valuation zero
的 Steinberg rank-one Hecke 列，而不是待付的任意二维矩阵；并且
\[
 0<C_{p,0}<1,qquad
 |C_{p,0}\lambda_1|^2={C_{p,0}^2\over p}\le {1\over p}.
                                                               \tag{CF19.96}
\]

primitive conductor exponent 至少二时，local standard Euler factor
在 \(p\) 处 degree zero，所以 \(\lambda_\pi(p^j)=0\ (j\ge1)\)；
当前 lifted first index 含 \(p\)，故该行逐 Fourier coefficient 为零。
对 trivial-nebentypus Eisenstein newdata，primitive character pair
的两个 local conductor exponents 相同，所以没有 exponent-one
Eisenstein 类型；正 exponent 类型至少二，也由同一正 index 消失。

最后可把全部 primitive-conductor patterns 在取绝对值前正交合计。
在每个 \(p\mid A\)，非零选择只有 unramified 与 Steinberg 两个互相
正交的 primitive subspaces，其 zero--zero 局部平方质量为
\[
 |D_p(1,0)|^2+{C_{p,0}^2\over p}.
\]
由 CF19.31、Kim--Sarnak \(|\lambda_1|\le p^\theta+p^{-\theta}\)
及 \(\inf_p\rho_p>0\)，
\[
 p|D_p(1,0)|^2\ll p^{-3+2\theta},
\]
而 CF19.96 给
\[
 |D_p(1,0)|^2+{C_{p,0}^2\over p}
 \le {1\over p}\{1+O(p^{-3+2\theta})\}.               \tag{CF19.97}
\]
因为 \(\theta=7/64<1/2\)，右边的 Euler correction 绝对可积。
所以对任意 squarefree \(A\)，同一个有限谱 regulator 内导子模式的
Hilbert 平方和（各 primitive subspace 使用自身的 native harmonic
measure）满足
\[
 \boxed{
 \sum_{\mathfrak c\mid A}
   |\text{zero--zero local coefficient at conductor }\mathfrak c|^2
 \ll {1\over A},
 \qquad
 \|\text{all conductor patterns}\|\ll A^{-1/2}.}      \tag{CF19.98}
\]
这里 \(\mathfrak c\) 只记录 \(A\)-部分的 primitive conductor；
exponent-two 行已为零。CF19.98 先用 primitive subspace 正交性求平方
和，绝不对 \(2^{\omega(A)}\) 个模式作三角不等式。

CF19.98 是所需 shell half-root 的唯一导子模式来源，不能与 CF19.88
的辅助 modulus density 相乘，也不能再乘 CF7.1。它仍只是 local
coefficient Hilbert norm：要进入 actual QCT，须证明所有导子模式的
shifted Fourier lists 在同一个 full-level harmonic large sieve 中
保持共同 Bessel/complete-shift 权。这里不能对模式先取绝对值再三角
求和；但在正交谱空间中保留平方和也不会制造
\(2^{\omega(A)}\)。下一节把这点精确写成一个有限 regulator 引理。
这个 common-ambient physical adapter 与连续谱 principal/axis/residue
的共同 regulator 仍属 CF19.L/CF19.C。

### CF19Z10. 导子模式先组成一个对角乘子；一次标量大筛已经足够

先把“导子模式需要新的向量值大筛”这个表述彻底消掉。固定一个有限
离散谱 regulator，并把 Eisenstein 参数限制在同一个紧集；所得正交
谱空间记为
\[
 {\cal H}_{\cal R}=\widehat\bigoplus_{\sigma\in\Sigma_A}
                    {\cal H}_{\sigma,\cal R}.         \tag{CF19.99}
\]
这里 \(\sigma\) 记录每个 \(p\mid A\) 的 primitive conductor 类型；
Maaß、holomorphic、Eisenstein cusp label 与 parity 都保留在各自的
正交直和或直积分中。令 \(P_\sigma\) 是相应正交投影。对每个谱 datum
\(\pi\in{\cal H}_{\sigma,\cal R}\)，令
\[
 m_A(\pi)=\prod_{p\mid A}m_{p,\sigma_p}(\pi),
 \quad
 m_{p,0}=D_{p,\pi}(1,0),\qquad
 m_{p,1}=+C_{p,0}\lambda_\pi(p),\qquad
 m_{p,\ge2}=0.                                        \tag{CF19.100}
\]
CF19.90 说明第一项正是 unramified oldclass 的 exact level-difference
multiplier；CF19.95 及其后乘回的 \(\mu(p)/c_p(1)=1\) 说明第二项
正是 actual Steinberg 行，而不是另一个 shell 权。定义
\({\cal H}_{\cal R}\) 上的对角算子
\[
 (M_A F)(\pi)=m_A(\pi)F(\pi).                         \tag{CF19.101}
\]

由于 primitive conductor 子空间彼此正交，CF19.97 的逐素数平方和
张量后严格给
\[
 \begin{aligned}
 \|M_A\|_{\rm op}^2
 &=\operatorname*{ess\,sup}_{\sigma,\pi}
        |m_A(\pi)|^2\\
 &\le \prod_{p\mid A}
     \operatorname*{ess\,sup}_{\pi}
       \left(|D_{p,\pi}(1,0)|^2+{C_{p,0}^2\over p}\right)
 \ll {1\over A}.
                                                               \tag{CF19.102}
 \end{aligned}
\]
小素数只进入绝对常数；大素数的 Euler correction 是
\(1+O(p^{-3+2\theta})\)，故乘积一致有界。注意第一行只需
\(\max_\sigma x_\sigma\le\sum_\sigma x_\sigma\)；没有把不同模式
的振幅作 \(\ell^1\) 求和。

现在令 \(T_1,T_2\) 是**同一个非负 Bessel regulator/同一个 ambient
full-level measure** 下的两条 Fourier evaluation map，并假定标量
大筛给
\[
 \|T_i a\|_{{\cal H}_{\cal R}}^2
 \le L_i\|a\|_2^2\qquad(i=1,2).                      \tag{CF19.103}
\]
则普通 Hilbert 空间 Cauchy--Schwarz 与 CF19.102 立即给
\[
 \boxed{
 |\langle M_AT_1a,T_2b\rangle|
 \ll A^{-1/2}(L_1L_2)^{1/2}\|a\|_2\|b\|_2.}         \tag{CF19.104}
\]
这就是所需的一份 conductor half-root；它来自 \(M_A\) 的算子范数，
不再从调和权、oldspace density 或 CF19.88 复制。证明对紧支撑
Eisenstein 直积分完全相同，因为 CF19.101 是可测有界乘子且谱测度
非负；没有交换解除 regulator 的极限。

若有限 local transfer 产生若干 downward-shifted 输入列，也不能仅把
它们**形式上**放入输入直和便宣称输出正交。若
\(S_{\sigma,j}\) 是相应 index-shift contraction，
\(r_{\sigma,j}\) 是固定系数，须先按实际进入同一 conductor subspace
的方式定义相干 synthesis
\[
 ({\cal S}a)_\sigma:=\sum_jr_{\sigma,j}S_{\sigma,j}a.
\]
所需 finite local 条件是这个真实 synthesis/Gram 算子的范数界
\[
 \boxed{
 \|{\cal S}a\|_{\widehat\oplus_\sigma}^2
 =\sum_\sigma\sum_{j,j'}r_{\sigma,j}\overline{r_{\sigma,j'}}
   \langle S_{\sigma,j}a,S_{\sigma,j'}a\rangle
 \ll A^{-1}\|a\|_2^2.                               \tag{CF19.105}
 }
\]
只有已经证明不同 \(j\) 的**输出**正交时，CF19.105 才退化成
\(\sum_{\sigma,j}|r_{\sigma,j}|^2\|S_{\sigma,j}a\|^2\)；输入直和本身
不够。精确反例是同一 \(\sigma\) 中取 \(J\) 个
\(S_{\sigma,j}=I\)、\(r_{\sigma,j}=1/J\)：逐列平方和为
\(J^{-1}\|a\|^2\)，而 \(({\cal S}a)_\sigma=a\)。CF19.105 若由
exact local tensor 的完整 Gram 矩阵给出，CF19.104 才可原样用于
合成列。反之，逐 shifted list 估计后作 \(\ell^1\) 三角会产生错误的
\(2^{\omega(A)}\)，只记对角能量又会漏掉相干交叉项。

因此 **finite-regulator conductor-pattern aggregation** 已经闭合：
它只需要一次共同的 scalar ambient large sieve，而不需要另猜一个
vector-valued spectral theorem。尚未闭合、且不能由 CF19.104 偷换的
物理命题是：从 actual CF19.80 的全部 level traces 出发，证明其
zero--zero 行在同一 ambient normalization 中恰成为 CF19.101（或
其 shifted-list synthesis 满足 CF19.105 的完整 Gram 界），同时
\(T_1,T_2\) 的
Bessel/AFE/complete-shift 权确实共同满足 CF19.103。principal、两条
axes、residues、nonflat 与其余 boxes 也必须在解除同一 regulator
以前放入共同不等式。CF19.104 没有证明这些 adapter，也没有证明
CF19.L、CF19.C 或 \(14/17\)。

### CF19Z11. 裸 valuation-one 物理壳的共同 test 与 full-spectrum 乘子恒等式

这里精确关闭 CF19Z10 所留 adapter 的一个、也只有一个部分。设
\(A>1\) 平方自由、\((A,Bkn)=1\)，并令 \(\phi\) 满足 CF19.61c 的
classical Kuznetsov admissibility。对任意符号 \(\pm\) 定义
\[
 {\cal G}_{A,B}^{\pm}(k,n;\phi)
 :=\sum_{\substack{m\ge1\\(m,A)=1}}
 {S(Ak,\pm n;ABm)\over ABm}\,
 \phi\!\left({4\pi\sqrt{A|kn|}\over ABm}\right).
                                                               \tag{CF19.106}
\]
这是 CF19.80 的 zero--zero 行在固定其余 tags 后的**裸
\(A\)-valuation-one 壳**：outer \(\mu(A)\) 与
\(c_A(n)^{-1}\) 因 \((A,n)=1\) 精确相消。若原 atom 还含
\((m,Bq_0)=1\)、character、nonflat 或其他依赖 \(m\) 的 mask，
CF19.106 只表示把这些另列为固定系数以前的壳；它们不能因本节而
删除或自动进入谱边。

令 \({\cal K}_N^{\pm}(x,y;\phi)\) 是 ordinary
\(\infty\)-cusp geometric Kuznetsov 行
\[
 {\cal K}_N^{\pm}(x,y;\phi)
 =\sum_{N\mid c}{S(x,\pm y;c)\over c}
   \phi\!\left({4\pi\sqrt{|xy|}\over c}\right).
\]
对每个 \(c=ABm\)，有限 Möbius 系数恰为
\(\sum_{d\mid(A,m)}\mu(d)=\mathbf1_{(m,A)=1}\)。因此不取绝对值便有
\[
 \boxed{
 {\cal G}_{A,B}^{\pm}(k,n;\phi)
 =\sum_{d\mid A}\mu(d)
   {\cal K}_{ABd}^{\pm}(Ak,n;\phi).}                  \tag{CF19.107}
\]
CF19.107 的每个 level 使用**同一个** \(\phi\)：\(d\) 只出现在
整除条件 \(ABd\mid c\)，没有进入 Bessel argument 或 test。
这正是 CF19.79--CF19.82 的 common-test 几何事实，不使用被禁止的
direct cusp identity。若同号公式含 diagonal，它也逐 level 为零，
因为 \(Ak=n\) 会迫使 \(A\mid n\)，与 \((A,n)=1\)、\(A>1\) 矛盾；
异号公式本来没有 diagonal。原 AFE diagonal 是 CF6 中另一个 tag，
不由此删除。

对 CF19.107 的每个 ordinary level 使用同一 normalization 的
classical Kuznetsov 公式，记全 Maaß/holomorphic/Eisenstein 谱边为
\(\operatorname{Spec}_{N}^{\pm}\)。则作为 admissible trace
distribution 有
\[
 {\cal G}_{A,B}^{\pm}(k,n;\phi)
 =\sum_{d\mid A}\mu(d)
   \operatorname{Spec}_{ABd}^{\pm}(Ak,n;\phi).         \tag{CF19.108}
\]
同号保留 holomorphic 行，异号 holomorphic 行为空；Maaß parity、
all oldforms 与 Eisenstein 的全部 cusp labels 均保留。这里 full-level
Eisenstein 二次型的 basis independence、primitive newdata 的正交
分解及 oldclass 正交化可分别使用
[Young, Proposition 8.2 and Sections 8.1, 8.5](https://arxiv.org/abs/1710.03624)；
离散 oldclass 使用
[Blomer--Milićević 的正交 oldform construction](https://arxiv.org/abs/1404.7845)。
这些只是在每个 full spectrum 内换正交基，并没有把不同 level 的
谱 datum 逐项强行配对。

现在在 CF19.108 的各谱边采用该 newform/oldform 分解，并先放入同一个
finite discrete / compact Eisenstein regulator；这里 regulator 必须由
同一 primitive-newdatum 集、parity 与谱参数 cutoff 在每个 level
诱导，不能任意截取各 level 的 full-level basis。因为 level 集
\(\{ABd:d\mid A\}\) 有限，可以先对 level 求和再按 primitive
conductor pattern 重组。逐个 \(p\mid A\) 的 local difference 只有：

- unramified newdatum 给 CF19.90 的 \(D_{p,\pi}(1,0)\)；
- conductor-one Steinberg newdatum 给 CF19.95 后乘回
  \(\mu(p)/c_p(1)\) 的 \(+C_{p,0}\lambda_\pi(p)\)；
- conductor exponent 至少二的 positive lifted index 为零；
- trivial-nebentypus Eisenstein 没有 exponent-one pattern，正导子
  pattern 至少二，故同样为零。

不同 primes 的 degeneracy Gram 矩阵张量化，故整个有限 level 和
恰成为 CF19.100 的对角乘子。若 \(X_{\pi,k}\)、\(Y_{\pi,n}\) 记
primitive datum 在 base-
\(B\) 方向的全部 Fourier/harmonic 因子（含 \(B\)-part native
measure），而 \(h_\phi^\pm(t_\pi)\) 是共同 Bessel transform，则
\[
 \boxed{
 \sum_{d\mid A}\mu(d)
   \operatorname{Spec}_{ABd,\cal R}^{\pm}(Ak,n;\phi)
 =\sum_{\sigma\in\Sigma_A}\int_{{\cal H}_{\sigma,\cal R}}
 h_\phi^\pm(t_\pi)m_A(\pi)
 X_{\pi,k}\overline{Y_{\pi,n}}\,d\nu_{B,\sigma}(\pi).}
                                                               \tag{CF19.109}
\]
这里 \(d\nu_{B,\sigma}\) 是正交 newdata 分解实际产生的 **native
primitive harmonic measure**，不是事后假定所有导子模式具有同一
数值密度。CF19.109 的共同性是：同一个 \(h_\phi^\pm\) 乘在所有
pattern 上；pattern 的体积比、oldclass Gram 与 ramified local row
全部已经进入 \(m_A\) 和 \(d\nu_{B,\sigma}\)。

若写 \(h_\phi^\pm=u_\phi|h_\phi^\pm|\)，\(|u_\phi|=1\) 于非零集，
则 CF19.109 还能精确写成 native 正测度 Hilbert pairing
\[
 \left\langle
 M_A\bigl(|h_\phi^\pm|^{1/2}X_k\bigr),
 \overline{u_\phi}\,|h_\phi^\pm|^{1/2}Y_n
 \right\rangle_{{\cal H}_{\cal R}}.                  \tag{CF19.110}
\]
因此 CF19Z10 的“一次 Cauchy、一次 half-root”确实适用于这个裸壳的
regulated spectral coefficient；不需要 cross-cusp identity，也不需
按导子模式作 \(\ell^1\) 三角。

CF19.107--CF19.110 **没有**证明 CF19.103 的 scalar large sieve：
还须证明 actual \(|h_\phi|\) majorant 在全部 AFE/detector/reflection
tags 上具有统一 normalized seminorm，并把 native measures 的
Fourier evaluation maps 同时控制。它们也没有处理 CF19.106 刻意
剥离的 quotient masks。若某个剩余 mask 能由有限 periodic
inclusion--exclusion 写成 common levels，必须逐项证明其新 levels、
test 与 local rows 仍满足同一 CF19.109；否则该行继续留在 CF4/native
complement。最后，从共同 regulator 到完整 trace 的极限、principal、
两 axes、residues、nonflat、unequal-gcd、endpoints、Type-II 与其余
boxes 全仍开放。因此本节关闭的是
\[
 \boxed{\text{mask-free zero--zero valuation-one shell 的 exact
 common-test full-spectrum/newdatum normalization},}       \tag{CF19.111}
\]
不是 CF19.D、CF19.L、CF19.C 或 \(14/17\)。

因此 generic expanded shell 的局部 varying-level 问题已缩成
CF19.30 这一条 reciprocal Hecke--Möbius 零列。若未来从 CF0A.3 的
实际 \(b^\sharp\) 证明平方自由 canonical 子域的共同 Mellin columns，
还必须证明这些 columns 与 CF19.27、另一 orientation、共享
complete-shift 权及 Maaß/holomorphic/Eisenstein 全谱在**同一次**
谱范数中相容；逐 \(A_{00}\) 使用 Kim--Sarnak 绝对值仍会损失幂次。
具体地，在 \(A_{00}\asymp A\) 上，
\[
 \sum_{A_{00}}\left|
 {\mu(A_{00})\lambda_\pi(A_{00})
  \over\prod_{p\mid A_{00}}(p+1)}\right|
 \ll_\varepsilon A^{\theta+\varepsilon},
 \qquad\theta={7\over64},
\]
而 CF19.L 只容许 \(P^\varepsilon\) 的 level 费用；所以不能在此处
逐 level 取绝对值。
这是比“重做全部四 atom”更窄的 signed spectral leaf。ramified、native
及端点行不由此分割自动支付。

CF19.16 精确说明 CF19.C 可以如何被证明：必须把 opposite-shell 的
全部 auxiliary outputs 在变化 \(q\) **之前**写成同一组
\(q\)-无关向量 \(z_p\)，允许随后用 \(R_q\) 收缩。有限正交标签可放入
\({\cal H}\) 的直和，只需逐 \(p\) 保持总平方范数有界。反之，若实际
输出是任意 edge array \(z_{p,q}\)，它一般不能写成 CF19.15；CF17.4
已经给出这种数组仍可存在于非主子空间的精确反例。故 CF19.16 是
新的无损 analytic supplier，但“实际 mixed-Bruhat/complete-shift
输出属于共同 Hilbert 列”仍是 CF19.L 中必须逐项证明的解析内容。
等价地，对每个归一化实际 edge kernel 证明
\(\gamma_2(z)\ll P^\varepsilon\)，再用 CF19.20；CF19.22 给出目前
最直接的可验收证书格式。

所以 CF19.8 对 **CF6.2 的整个 actual common coefficient list** 尚未
完成：还需要把 CF3 的四 endpoint 行、CF5 的 quotient-zero/axis 行、
CF4 的四谱型与 PP/PQ/QP/QQ、以及 native complement 分别标明是
CF19.1 的 contraction block、已经独立支付的行，还是仍无此分解的行。
在这份逐行字节映射完成前，CF19.4 只证明了 two-sided
product-Fourier/operator supplier，不证明 all-box bound。特别地，
CF19.6 若只恢复两侧 shell baseline，不能再把同一
\(a^{-1/2}b^{-1/2}\) 当成额外 \(P^{-1/12}\)；残余 saving 必须从
CF19.4 相对于**同一 coefficient energy**的 \(A_t/q\) 比较中出现。

## CF20. 反向审计表

本文在 fresh checkout 可自含复核的结论只有：

1. CF0A.1--CF0A.5 与 CF1.5：一次有限 Möbius 系数修正、唯一共同
   投影及精确增广 Gram 等式；修正误差的解析小量界仍未证明；
2. CF3.1--CF3.2：quotient 两端点的有限 inclusion--exclusion；把四个
   abstract rows 逐项识别为公开原 atom 的端点仍是 adapter obligation；
3. CF4.5：在四行确有同一系数的前提下，PP/PQ/QP/QQ 的有限尾逐项
   抵消。CF4.1--CF4.4 的全谱 normalization 与原 atom 的等同性未证；
4. CF5.3--CF5.8：从 prime-power Ramanujan 和作二维差分，自含证明
   CF5.2 的共同 divisor 展开、精确主质量 \(\varphi(s)/s\) 与绝对质量
   \(\tau(s)^2\)，并同时覆盖两条 axis 与 origin。CF5.9--CF5.12 再
   证明两个边缘只剩顶 divisor，并在完整剩余类空间把同一 Ramanujan
   核正交分成双中心、左轴、右轴与常数四项；CF5.13--CF5.16 通过
   residue periodization 把任意有限物理权精确放入同一个四项等式与
   Cauchy 上界。CF5.17--CF5.19 又把任意 unequal-gcd 双 Poisson
   三行精确中心化为两条零均值 sampling axes 与一个不可删除的常数，
   并给出跨全部有限模数的一次共同 Cauchy。CF5.20--CF5.24 在真正
   零模上把全部 nonunit kernels 精确降到 reduced modulus，证明
   residue/sampling/deleted-origin 三种描述的系数一致，并以模 3
   反例禁止把它外推到非零频率。CF5.25--CF5.28 求出 centered 核的
   精确质量：prime shell 有半根下降，但 \(s=pq\) 时 centered/raw
   比例趋于 \(1/\sqrt2\)，故复合壳不能只靠有限投影取得 power saving。
   CF5.29--CF5.32 再把 squarefree centered 核写成四状态正交张量，
   并证明完整带符号 cofactor cube 中每个未激活素数恰给 \(1/p\)；
   实际 dyadic shell 的缺顶点/变权迁移仍属 CF19.L。CF5.33--CF5.34
   构造平滑 product shell 精确冻结固定 \(\omega(s)\) 的反例，否定
   只用完整 cube 加 smooth Abel 迁移该收益的路线，但不否定壳内
   two-sided dispersion。CF5.35--CF5.39 对 CF5.1 的实际分离权证明
   centered 零模的精确倍数采样误差公式及 uniform variation bound；
   prime shell 在 \(H_1,H_2\le p\) 时降到 \(H_1H_2/p\)，复合 divisor
   cost 是否逐物理壳达标仍待核算。CF5.40--CF5.42 进一步证明：当
   平方自由模数的最小素因子大于两条 shift 支撑时，双中心零模在
   偶数素因子层仍精确保留与 \(V_1W_1\) 同量级的常数见证；奇数层
   才有 \(\sum_{p\mid s}p^{-1}\) 的逐模数小量。因此剩余问题不是再做
   一次单模数 centering，而是把偶 parity 行同另一侧 level 符号、
   diagonal 及 principal/residue ledger 在取绝对值前共同压缩。
   CF5.43--CF5.45 又证明：放回 CF5.12 的两轴与常数后，unit 行只剩
   \(\mu(s)\)，它和 principal reverse-Poisson subtraction 的标量完全
   相反；若两边零频权相同便逐 tag 精确抵消，一般情形的全部缺口恰是
   CF5.45 的共同权 mismatch。原 QCT 只能在先求完 Poisson 频率、恢复
   整数格、共同截断并作坐标拉回后供应这两个列；固定频率逐 tag 对接
   并不合法。该全局 physical adapter 及其余补集仍属 CF19.D/CF19.C，
   而不是这条有限恒等式的结论。
   CF5.1 在复合壳的 signed varying-level saving、零模低秩部分与
   diagonal/principal/residue 行的压缩仍未证明；
5. CF6 给出不允许静默丢项的 master-tag contract；只有 adapter 已验证
   的行才能进入 expanded 分支，其余必须留在 native complement。
   因此本稿不把 CF6.2 对全部原行的等同性列为已证；
6. CF7A：从 oldspace Gram 定义重证 exact-shell local kernel；CF7.9--
   CF7.10 只把 \(A^{-1/2}\) half-root 证明为显式 valuation-averaged
   projective mass，并核对它没有与 harmonic/progression 权重复。
   把这份纯 valuation mass 迁移为实际 coefficient/Bessel/complete-shift
   算子界仍是 CF19.D/CF19.L 的开放 adapter；
7. CF8.1--CF8.3：输出修正到全高度余量的显式接口义务，而非已证
   height reassembly；
8. CF11.1--CF11.3：保留两侧角色与共同 tags 的 exact zero-alias
   Fourier projector 及其无 alias 单边 isometry；
9. CF13.1--CF13.2：两篇 2025--2026 原始 Kloosterman 定理在真实尺度
   的数值与对象适配边界；
10. CF14.1--CF14.3：任意有限秩中心化后部分匹配算子仍有范数 1 的
    严格 no-free-contraction 引理；
11. CF15.1--CF15.11：对实际 Riesz 素数权的 varying-prime-modulus
    prime--interval 四阶矩及正交有限标签扩张，准确支付 scalar
    \(P^{-1/12}\) leaf 与一侧 divisor-output；它不正交化物理
    cofactor 的 scalar 求和。
12. CF16.1--CF16.6：带任意双素数单位相位的 cross-prime mutual-character
    operator 是 contraction；双方非主投影后仍成立。CF16.7--CF16.8
    证明一旦 critical cofactor 已成为正交输出，共享 Fourier 相位不再
    产生 zero-alias 长度损失。
13. CF17.1--CF17.5：乘上短角色和后的算子按 \(q\) 逐块成为 centered
    multiplicative-incidence 矩阵；非主输入仍能以常数代价承载任意
    \(z_{p,q}\)。因此 CF16 本身没有 coefficient-uniform
    varying-level power saving。
14. CF18.1--CF18.5：固定 cofactor 的短逆边注入给实际 Riesz 加权
    平方条目能量 \(\ll BA M_YS_Y\)，包括正交有限标签与 exact
    determinant 子支撑；CF18.6 同时证明若先退化成一般算子范数，
    只能得到 \((A/P)^{1/2}\) 而非 \(A/P\)。
15. CF19.1--CF19.7：cross-prime contraction 的算子值版本、共享乘积
    Fourier isometry、两侧不同 critical divisor outputs 及 genuine-gcd
    mask 的无固定幂重组。CF19.9 证明归一化 smooth kernel 的核分解
    只付已显示的有限 Sobolev 半范数。CF19.6b 是未对齐基线的形式
    比值，不是 saving；CF19.4 仍返回 CF12.1 的 diagonal 级别。
    CF19.10 只是在新增 physical-shift 半范数 CF19.D、varying-level
    能量恒等式 CF19.L 与 actual-centered 压缩 CF19.C 下的条件性
    balanced generic 结论；旧的原核导数、逐块 norm-one、CF7A 与
    determinant 代数各自都不蕴含这三个输入。CF19.11--CF19.14 已独立支付第二次 Poisson
    的 affine physical-shift 导数与远频尾，把 CF19.D 缩成原完整
    \(F\) 的 normalized-seminorm pullback。CF19.15--CF19.18 把
    actual-Riesz 四阶矩严格扩张到任意共同 Hilbert 列及其逐模数
    contractions；它不接受 CF17 的任意 \(z_{p,q}\) edge array。
    CF19.19--CF19.22 把标量 edge 的共同列义务等价写成
    \(\gamma_2\) factorization norm，并给出 projective-square-mass
    充分条件；它没有证明实际 shell 满足 \(\gamma_2\ll P^\varepsilon\)，
    算子值 shell 也仍需另给对应分解。CF19.23--CF19.24 则把 leading
    \(C_1\) 的 divisor-output 精确写成 Hilbert 值 lcm--harmonic Gram，
    并以 \(H_N^4\) 支付其全部 level multiplicity；同时给出不能直接用
    \(H_N\) 乘 reciprocal-LCM form 的最小反例。这个结论没有完成两侧
    output 到 common shift 的输运。CF19.25--CF19.30 进一步把 generic
    unramified shell 的全部 level primes 分成 divisor-supported 部分
    与唯一 \(u=b=0\) 部分；前者在纯 shell 层由 CF19.27--CF19.29
    支付，后者精确成为 reciprocal Hecke--Möbius 零列。补块估计仍须
    证明实际 nonlocal columns 满足 CF19.29 的共同输入预算；零列的
    共同全谱估计也未证明。CF19.8 仍须对实际 CF6.2 tags 完成逐行
    映射或独立支付。CF19.31--CF19.33 恢复 ambient kernel 后把零列
    展成仅含正奇 local valuation 的 Hecke shifts。CF19.32a--CF19.32d
    给出精确 odd-Hecke 生成函数、可求和的局部尾与有限普通系数平方
    质量；CF19.32e 同时证明带 index-length 权的质量发散，所以不能把
    无限展开直接塞进含 \(N/q\) 项的普通 spectral large sieve。每个
    有限截断在 \((A_{00},kn)=1\) 时没有 primitive diagonal，但共同
    Bessel test 下的一致截断极限或有理 multiplier 算子界、off-diagonal、
    principal 与 axis 仍开放。CF19.34--CF19.35 又把同一零列精确识别为
    \(L^{(M)}(1+s,\pi)^{-1}\) 乘一个在 \(\Re s>-1/2\) 绝对收敛的
    Euler product；它同时说明逐 form 移线会重新遇到未知 zeros，不能
    代替所需 joint spectral estimate。CF19.36--CF19.39 则在 opposite side
    已成为真正共同 Hecke 列时，把原有限 Möbius 零列无损压成长度
    \(2XN\)、系数平方质量 \(X^{-1+o(1)}\) 的单一 Hilbert 值多项式；
    它没有证明该共同列条件或原 Bessel test 下的标量全谱大筛。
    CF19.40--CF19.45 从 HPY 同号公式抽出正的 Maaß--Eisenstein
    scalar large sieve 并对齐 classical exponent-one projector，
    同时证明 naive common-LCM projector 的 Plancherel 成本；HPY 的
    generalized opposite-sign 公式在原文中仍只是被假设。
    CF19.46--CF19.54 则从 Andersen--Kıral 的局部三项重新归纳出互素
    squarefree--squarefree 的经典同号全谱 reciprocity：有限完成的
    \(3^{\omega(A)}\) 项在冻结小 primes 后只付 \(A^\varepsilon\)，
    但 all-twist 项系数有绝对正常数下界，所以 reciprocity 本身绝不
    提供第二份 \(A^{-1/2}\)。这个子定理仍限于 fixed-\(g\) raw
    \(\widetilde L^2\)、共同 gamma-ratio Bessel transform；actual
    \(b^\sharp\)、generalized 异号 projector 与完整四行共同投影尚未
    映射。CF19.55--CF19.57 进一步证明 reciprocity 在交换不变的共同
    和中只删除 test 的反对称部分；fixed-\(\omega\) product shell 上
    \(\mu(A)\mu(N)\) 是常号，所以对称部分不能仅由“两侧 Möbius
    符号”获得 saving。CF19.58--CF19.61 随后直接在几何侧估计一个
    与 CF19.32c 数值权相同、但在 modulus 上另施 exact-shell 的辅助
    odd--Hecke 级数：Weil 界、模数分段和 restricted Euler 乘积给出
    \(B^{-1}A^{-11/4+\varepsilon}(kn)^{1/4+\varepsilon}(k,n)^{1/2}\)
    的绝对界。CF19.62--CF19.67 另用
    \(\sum_{d\mid A}\mu(d)\operatorname{Spec}_{ABd}^{\pm}\) 精确选出
    \(v_p(c)=1\ (p\mid A)\)：同号 diagonal 由
    \(\sum_{d\mid A}\mu(d)=0\) 消失，Maaß/holomorphic/Eisenstein
    与 non-squarefree levels 的 oldforms 全部保留；CF19.61 使其
    odd--Hecke 截断具有唯一的整体 regulated 极限。这个
    \(\infty\infty\) 壳与 Andersen--Kıral 的 \(0\infty\)、
    \((c,N)=1\)、\(1/(c\sqrt N)\) 核不同，故 reciprocity 仍不能
    逐项移植，点态有理 multiplier 与物理共同 regulator 的识别仍开。
    CF19.61a--CF19.61b 把变化 Bessel 尺度
    \(X_\phi^{-1/2-\eta}\) 显式恢复，禁止把它藏进 test 常数；
    CF19.68--CF19.70 再以 gcd 矩阵的一次 Schur test 装配任意两条
    dyadic \(k,n\) 列。在不极端失衡的长度上，全部 index 费用为
    \((K_0N_0)^{3/4+\varepsilon}\)，但 actual 每个模数权具有共同
    \(C_\phi,X_\phi\) 的 normalized-seminorm 仍须由 CF19.D 证明。
    CF19.71--CF19.75 对固定 \(ABr\asymp C_0\) 权允许 test
    随 odd--Hecke index \(t\) 变化；直接 Weil 求和使
    \(t\)-质量精确降为
    \(\prod_{p\mid A}(1-p^{-1})^{-1}\)，并得到
    \(C_0^{1/2+\varepsilon}A^{-3+\varepsilon}B^{-1}(k,n)^{1/2}\)。
    CF19.76--CF19.78 则保持 actual common test，并精确记录
    它使模数壳移到 \(ABr\asymp tC_0\)；相应
    \(t\)-质量为 \(\prod_{p\mid A}(1-p^{-1/2+\eta})^{-1}\)，
    仍只付 \(A^\varepsilon\)。两种对象的非极端 dyadic 列长度费用
    都为 \((K_0N_0)^{1/2+\varepsilon}\)，但不能在局部账上互换。
    这些仍是 auxiliary exact-shell 估计，不能据此宣称原物理零列
    已映射；其他 local/principal/axis/native 行同样仍未支付。
    CF19.79--CF19.82 进一步从主笔记 §412 的字面 quotient Poisson
    证明 Type-I/Type-I bulk 的几何尺度 \(C_0=AS\)、base index
    \(Ak\)、modulus \(ABm\) 与唯一 Jacobian \(R\)；但
    \(A^{-2}t^{-1}\) 仍只在 zero--zero local multiplier 中由
    CF19.32c 产生，所以没有据此新增 actual spectral coverage。
    最后 CF19.83--CF19.84 给出决定性的反向审计：CF19.32c 的
    odd--Hecke 系数若再送进 CF19.62 的 exact-shell level 容斥，则
    每个 shell prime 的局部和精确为零，故 CF19Z--CF19Z5 不能与
    physical local multiplier 串联。去掉重复 shell 后，正确候选是
    CF19.85 的 level-\(B\) full-spectrum trace；其纯几何界为
    \(B^{-1}A^{-7/4+\varepsilon}(kn)^{1/4+\varepsilon}(k,n)^{1/2}\)，
    actual-common-test 形式为
    \(C_WC_0^{1/2+\varepsilon}B^{-1}A^{-2+\varepsilon}(k,n)^{1/2}\)。
    把这个 lower-level candidate 与 actual Maaß/holomorphic/Eisenstein
    harmonic measure、principal/axes/residues 无损对齐，仍是 CF4 的
    未证命题。CF19.89--CF19.91 则在同一个有限 discrete/compact
    Eisenstein regulator 内逐 datum 完成其中的 unramified oldclass
    multiplier：level difference 的 \(\prod_{p\mid A}D_p(1,0)\) 与
    level-\(B\) odd--Hecke aggregate 精确相同，且没有第二份 harmonic
    \(1/p\)。CF19.92--CF19.98 又从 conductor-one 的两维 oldbasis 直接算出
    除以 \(c_p(1)\) 后的 Steinberg rank-one 系数
    \(-C_{p,0}\lambda_j\)，并核对乘回 outer \(\mu(p)\) 后 actual
    乘子为 \(+C_{p,0}\lambda_j\)；同时证明 conductor
    exponent 至少二在正 index 消失，并利用 primitive-subspace 正交性
    把全部导子模式平方合计为 \(O(A^{-1})\)。CF19.99--CF19.105 随后
    把这些模式严格组成共同有限谱空间上的对角乘子；其算子范数只有
    \(O(A^{-1/2})\)，故一旦共同 scalar ambient large sieve 成立，
    Hilbert 空间 Cauchy 一次就给所需 half-root，不需要新的向量值
    大筛，也没有 \(2^{\omega(A)}\)。CF19.106--CF19.111 进一步把
    mask-free actual zero--zero valuation-one 壳精确写成使用同一 test
    的 full-level trace 差，并在共同 regulator 内把 Maaß、holomorphic、
    oldforms 与全部 Eisenstein cusp labels 重组为这个 native-measure
    乘子。尚未证明的是其余 quotient masks 的同一重组、共同
    nonnegative Bessel majorant/scalar large sieve、解除 regulator，
    以及 principal/axis/residue 的同投影压缩；这些仍属
    CF19.D/CF19.L/CF19.C。

仍未证明：CF9.1 的 signed analytic bound、low-height expanding band、
CF19.D 的完整 physical-shift 核 pullback、CF19.L 所要求的两侧
critical-incidence 共同正交化、principal/equal-prime/axis 到
CF16.6 的精确映射、CF19.C 的实际中心化压缩、所有 bad boxes 的统一 saving、统一
或有效 \(T_0\)。所以不能声明 \(14/17\) 已证明，不能新增承载这些
内容的 Lean axiom 或条件接口。

## CF21. `origin/main` 的物理覆盖不是同一个全输出上界

本节冻结只读盘点于
`origin/main = 180018630782ee32be04e1385acecab98984078d`。它只比较
各文稿自己声明的物理对象与补集，不把有限脚本当解析证明，也不把
不同线性投影的 saving 相乘。

在平衡目标尺度 \(E=T^{6/5}\) 上，当前已合并的局部覆盖可按同一
原 \(\mu(n)\) 分解列成：

| 物理区 | `main` 中已支付的严格范围 | 明示保留的补集 |
|---|---|---|
| short Type-I | `physical-type-i-triple-completion` 支付整个短 Type-I | 全部双长 Type-II、principal、global gate |
| Type-II 短乘积 | `physical-type-ii-hyperbolic-incidence` 支付 \(bc\le T^{11/10}\)，特别含 \(bc\le E\) | \(bc>E\) 的长 signed Type-II |
| Type-II 频率带 | `physical-type-ii-product-frequency-band` 支付 \((q,k\rho\sigma)\ge T^{1/10}\)；common-frequency 稿支付其更窄子带 | 低 product-gcd；素数模数的单位三频尤其全部留在此补集 |
| Type 因子重叠 | `physical-type-ii-factor-overlap` 支付展开式中 \((b,c)\ge T^{1/4}\) 的非平方自由子和 | 原平方自由双长项与小重叠项；该 saving 不能移给原 \(\mu(n)\) 非零支撑 |
| native principal Type-II | `physical-native-type-ii-large-quotient` 支付明确投影中 \(T^{8/15}\le X\le T^{4/5}\) 的无权大商 | 小商、其他 native 坐标、零模与校正 |
| native 低导子 overlap | `physical-native-overlap-low-conductor` 支付 \((m,k)\ge T^{1/10}\) | \((m,k)<T^{1/10}\) 的完整 signed 补集 |
| fixed-\(H/L\) centered packets | prime-\(e\)/all-squarefree-\(q\)、balanced semiprime-\(e\)、small-cofactor-\(e\) 等文稿分别支付其指定整包 | 一般 squarefree \(e\)、composite \(q\)、其他 canonical/\(q_0\)、跨 AFE/标签能量 |
| 全 \(h/\delta\) common-gcd | `physical-common-gcd-full-reassembly` 只在 \(\eta\ge687/550\)，`physical-low-conductor-common-large-sieve` 只在 \(\eta\ge81/65\) | 两个门槛都严格大于 \(6/5\)，所以不能支付目标尺度的完整 canonical 层 |
| global principal/tails | `physical-principal-tail-repair` 支付同一原 \(\mu\)-taper 的全局 \(D+J_{\rm Ram}\) | 完整 centered gate、实际放大系数迁移及共同投影交叉项 |

因而，即使只看原 \(\mu(n)\) 的一个自然内部族，现有文稿的共同补集
仍含下面这个非空交集：
\[
 \begin{gathered}
 bc>E,\qquad (q,k\rho\sigma)<T^{1/10},\qquad (b,c)=1,\\
 X<T^{8/15}\ \hbox{（在相应 native principal 坐标中）},\qquad
 (m,k)<T^{1/10},                                      \tag{CF21.1}
 \end{gathered}
\]
连同一般 squarefree \(e\)、其他 canonical/\(q_0\)、非内部 AFE 和
跨 \(H/L\) 能量。这里各条件属于相应精确投影；CF21.1 是“所有已知
支付域之外仍可能同时出现”的账本描述，不擅自把不同展开的变量声明为
一个新恒等式。prime-\(q\) 的三频全单位长 Type-II 是最直接的实际
代表，因为高 product-gcd 带在 prime-\(q\) 上为空，而 HY 只到短乘积。

更重要的是，这些 `main` 文稿使用原 \(\mu(n)\) 及各自固定线性投影；
CF6/CF19 的目标使用实际 Riesz 放大系数、同一个完整投影和两侧
exact-shell determinant。没有一个已合并文稿证明如下对象等同：
\[
 \text{各局部原-}\mu\text{ 线性上界的集合}
 \quad=\quad
 \text{CF6.2 的 actual common projected quadratic output}. \tag{CF21.2}
\]
因此三角不等式只能在先有一份不重不漏、绝对可和的共同分解后使用；
不能用“每类都有一个 PR”代替 CF19.L，也不能把频率、overlap 与
quotient 的三个 saving 乘在同一项上。

CF21 的结论是正面的路线收缩：下一项应先证明 CF19.D 与 CF19.L 的
无损映射，再对该**同一**实际空间证明 CF19.C；并先在 CF21.1 的
prime-modulus、squarefree、双长低频代表上验证。若这一步成立，再逐项
接回已支付的 Type-I、短乘积、高频和 principal rows。当前它仍不是
all-box bound，更不是高高度 \(14/17\) 定理。
