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
列扩张。反向审计同时撤回一个错误推断：这些 norm-one/isometry
supplier 本身不产生所需 \(P^{-1/12}\) centered contraction。

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
CF5.2 是必须从每个 prime-power Ramanujan kernel 逐项验证的 contract；
在完成该验证前，CF5.1 不能换成 complete-residue PP average。

双 Poisson 的 nonunit axes contract 则含两条 sampling line 与
一次负的 double integral，其系数分别为 \(1/C,1/C,-g_C/C^2\)。
当 \(g_C\ne1\) 时不可把它们写成同一系数。它们与 CF5.1 是不同
tags；“都是 principal-looking”不构成等同或抵消证明。

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

Cochrane--Shi 的任意平移区间四阶矩（其 Theorem 1 明确允许任意
整数起点），经固定总变差的分部求和并在 exact Gauss--Poisson 后
把完整对偶轴分块，均匀给
\[
 {1\over q-1}\sum_{\chi\ne\chi_0}
       |\mathcal T_{q,a,\alpha}(\chi)|^4
 \ll_W A^2(\log P)^{12},\qquad A<q.                    \tag{CF15.7}
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
RV5 的分块 Abel--Minkowski 证明只使用
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
4. CF6 给出不允许静默丢项的 master-tag contract；只有 adapter 已验证
   的行才能进入 expanded 分支，其余必须留在 native complement。
   因此本稿不把 CF6.2 对全部原行的等同性列为已证；
5. CF7A：从 oldspace Gram 定义重证 exact-shell local kernel；CF7.9--
   CF7.10 只把 \(A^{-1/2}\) half-root 证明为显式 valuation-averaged
   projective mass，并核对它没有与 harmonic/progression 权重复。
   把这份纯 valuation mass 迁移为实际 coefficient/Bessel/complete-shift
   算子界仍是 CF19.D/CF19.L 的开放 adapter；
6. CF8.1--CF8.3：输出修正到全高度余量的显式接口义务，而非已证
   height reassembly；
7. CF11.1--CF11.3：保留两侧角色与共同 tags 的 exact zero-alias
   Fourier projector 及其无 alias 单边 isometry；
8. CF13.1--CF13.2：两篇 2025--2026 原始 Kloosterman 定理在真实尺度
   的数值与对象适配边界；
9. CF14.1--CF14.3：任意有限秩中心化后部分匹配算子仍有范数 1 的
    严格 no-free-contraction 引理；
10. CF15.1--CF15.11：对实际 Riesz 素数权的 varying-prime-modulus
    prime--interval 四阶矩及正交有限标签扩张，准确支付 scalar
    \(P^{-1/12}\) leaf 与一侧 divisor-output；它不正交化物理
    cofactor 的 scalar 求和。
11. CF16.1--CF16.6：带任意双素数单位相位的 cross-prime mutual-character
    operator 是 contraction；双方非主投影后仍成立。CF16.7--CF16.8
    证明一旦 critical cofactor 已成为正交输出，共享 Fourier 相位不再
    产生 zero-alias 长度损失。
12. CF17.1--CF17.5：乘上短角色和后的算子按 \(q\) 逐块成为 centered
    multiplicative-incidence 矩阵；非主输入仍能以常数代价承载任意
    \(z_{p,q}\)。因此 CF16 本身没有 coefficient-uniform
    varying-level power saving。
13. CF18.1--CF18.5：固定 cofactor 的短逆边注入给实际 Riesz 加权
    平方条目能量 \(\ll BA M_YS_Y\)，包括正交有限标签与 exact
    determinant 子支撑；CF18.6 同时证明若先退化成一般算子范数，
    只能得到 \((A/P)^{1/2}\) 而非 \(A/P\)。
14. CF19.1--CF19.7：cross-prime contraction 的算子值版本、共享乘积
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
    展成仅含正奇 local valuation 的 Hecke shifts，证明每个有限截断
    在 \((A_{00},kn)=1\) 时没有 primitive diagonal；共同 Bessel test
    下的无限极限、off-diagonal、principal 与 axis 仍开放。
    CF19.34--CF19.35 又把同一零列精确识别为
    \(L^{(M)}(1+s,\pi)^{-1}\) 乘一个在 \(\Re s>-1/2\) 绝对收敛的
    Euler product；它同时说明逐 form 移线会重新遇到未知 zeros，不能
    代替所需 joint spectral estimate。

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
