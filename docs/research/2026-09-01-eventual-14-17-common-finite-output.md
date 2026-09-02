# 高高度 \(14/17\) 的共同有限输出：投影、端点、零模与全谱残项的一次重组

## 结论边界

本文首先关闭一个代数层问题：把实际零点自适应系数、唯一共同投影、
quotient 两端点、Poisson 零模与轴、Maaß/holomorphic/Eisenstein 全谱、
exact valuation-one shell、连续谱的 PP/PQ/QP/QQ 四行及局部余项放进
**同一个有限 Hermitian 输出**。所有操作先在有限截断上进行；没有先对
level、box、谱型或端点分别取绝对值。

此外本文证明若干独立 supplier：exact zero-alias Fourier isometry、
cross-prime contraction、短逆边实际 Riesz 平方能量、affine
physical-shift 导数/尾引理，以及 actual-Riesz 四阶矩的共同 Hilbert
列扩张。反向审计同时撤回一个错误推断：这些 norm-one/isometry
supplier 本身不产生所需 \(P^{-1/12}\) centered contraction。

本文不证明这个共同输出的所需上界。最后剩下的命题准确等于 HR16，
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
3. 实际输出系数 \(b^\sharp\) 与一次投影修正采用 MC1--MC3；输出到
   全高度余量采用 HR1--HR16。冻结文件来源分别为
   `e2f359bf54c8d98f7becdaa08833a1c92d090dcc` 的
   `2026-08-31-projected-coefficient-common-mellin-columns.md`、
   `b7fe1134d855120b43494f9cc2b8116fd589abe3` 的
   `2026-08-31-projected-complete-height-reassembly.md`，以及
   `9cf69d59a03bcdfa630612fcbae662376a11f83f` 的
   `2026-08-31-common-projection-finite-coefficient-correction.md`。
   CT1--CT9 取 `0c9f90f969f6e248a44b7bb26776813939af2c39` 的
   `2026-08-30-mwkf-common-ttstar.md`。
4. 谱局部行采用 AFE/Bessel 延续稿的 (446.1)--(446.4)、
   (463.2)、(465.1)--(465.6)、(472.1)--(472.8)、
   (475.1)--(475.3)、(477.1)--(477.5) 与 (488.1)--(488.5)。
   CF344、CF386--CF387、CF395--CF405 的冻结母稿取提交
   `1810d3fbe2a3bd7dccb4da6d375b4a16a58747fd`；本稿没有读取该树中
   与这些节无关的 dirty 修订。原核 KW1--KW7 取独立提交
   `dc0fbb93fcb4a6eb18943fe0fc11d5f1c74db51b`。

有两个不能混合的 Möbius 记号约定。

- native 行直接携带
  \(b^\sharp_{q_0r}\overline{b^\sharp_{q_0s}}\)，不得再乘一个
  “原 mollifier” Möbius 符号；
- 在平方自由 canonical 子域使用 MC16 时，先定义
  \(B(d)=\mu(d)b^\sharp_d\)，再且只再出现一次
  \(\mu(r)\mu(s)B(q_0r)\overline{B(q_0s)}\)。

下面 (475.3) 中的 \(\mu(A)\mu(B)\) 是 quotient 展开的符号，
不是第三份 mollifier 符号。exact shell 内的
\(\mu(A)/c_A(h\delta)\) 已包含在 (472.2) 中，也不再作为一个独立
level 系数复制。

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
采用 PCF/MC 的同一 \(z=G^{-1}v\)、离散低响应 \(A_i\) 与连续低响应
\(B_i\)。记
\[
 \delta_i=A_i-B_i,
 \qquad
 F_\sharp=\sum_n c_\sharp(n)w_n,
 \qquad
 \Delta_z=\sum_i z_i\delta_i.
 \tag{CF1.2}
\]
PCF10/MC2 逐点给出精确等式
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
\(b^\sharp\)，(CF1.5) 退回 (488.2) 的
\(K-q^*G^{-1}q\)；反之，(CF1.5) 是把这个 dense correction 送入
一次有限系数修正后的精确增广形式，不遗漏长距离 cross terms。
PCF11--PCF16 控制 \(\Delta_z\)，但该控制不是 (CF1.5) 的前提。

## CF2. 物理层只展开左上短移位块，外权只出现一次

CT/AFE 把 (CF1.5) 的左上块送到临界线 moment；它给的是上界传输，
不是把输出 Gram 与一个谱和宣称相等。对每个固定高度壳 \(T\)、
原 smooth partition、AFE 方向、符号、\(q_0,R,S,H_1,H_2\) 与
原有限整数支撑，物理 atom 的输入系数仍是同一个
\[
       b^\sharp_{q_0r}\overline{b^\sharp_{q_0s}}.        \tag{CF2.1}
\]
在允许 MC16 的平方自由行，(CF2.1) 只是按 CF0 的第二约定重写，
不是更换系数。

每个 atom 的字面标量为
\[
                 \frac{2T}{q_0RS}.                       \tag{CF2.2}
\]
quotient Poisson 后 (472.2) 的 \(R\) 在 native trace 外。故任何谱
估计的物理恢复顺序必须是
\[
 \frac{2T}{q_0RS}\ \times R\ \times
       (\text{frequency sum})\ \times(\text{one native trace}).
 \tag{CF2.3}
\]
不能再从 Blomer--Milićević 的 \(C^{-1/2}\) convention 引入一个
\(\sqrt{AS}\)：(472.4)--(472.6) 已说明该量与 test 中的
\((AS)^{-1/2}\) 恰好抵消。

## CF3. quotient 两端点必须先组成同一个四行列

在 \(r,s>1\)、\((r,s)=1\) 与平方自由 \(q_0\) 的有限行，定义
\[
 \gamma_A={\bf1}_{(A,q_0)=1},\qquad
 \gamma_B={\bf1}_{(B,q_0)=1}.
\]
对任意尚未拆开的物理权 \(\Phi\)，(475.2) 给出
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
不塞入 (475.1)。

固定 \(r,s\) 把所有 divisor labels 求完时，CF3.1 的前三行各自为零，
最后一行恢复原系数。这证明 CF3.1 不是 contraction；它是端点选择器。
所以 joint Poisson、Kuznetsov 或 reciprocity 必须作用于
\(\mathcal U_{A,B}\) 整体。只估 bulk 后称端点较小会删除原和本身。

## CF4. 非零 quotient frequency 的全谱共同列

对 \(k\ne0\)，先使用 corrected lift (CF0.1) 与 exact-shell
resummation。固定所有局部 Hecke 截断 \(\boldsymbol J\)，且
\(J_p\ge(a_p+b_p)/2\)。对 Maaß 两 parity、holomorphic 与
Eisenstein 分别采用其真实 Bessel/Petersson test；holomorphic 行不把
\(t=i/2\) 插入 Maaß multiplier。把两 Maaß parity 在使用同号与异号
Kuznetsov 前写成 average/difference。

对每个这样的共同 test，(446.4) 是有限核等式
\[
 \mathcal T^h_{A,B,z,d}
     =\mathfrak D^h_{A,B,z,d}
       +\mathcal O^h_{\boldsymbol J;A,B,z,d}
       +\mathcal R^h_{\boldsymbol J;A,B,z,d}.             \tag{CF4.1}
\]
其对角恰为
\[
 \delta_{m,n}\mathfrak D[h]
 \prod_{p\mid A}\{-(1-t_p)\tau_p(a_p+b_p)\}
 \prod_{p\mid B}\{{\bf1}_{a_p=b_p}
               -(1-t_p)\tau_p(a_p+b_p)\}.               \tag{CF4.2}
\]
只有一个全局 \(\mathfrak D[h]\)。非零 Hecke shifts 全留在
\(\mathcal O\)，含任一 exact local remainder 的项全留在
\(\mathcal R\)。

在 trivial-character exact shell 的连续谱中，非平凡 primitive
Eisenstein 数据因第一 Fourier index 含 shell prime 而逐系数为零；
剩下 level-one Eisenstein，native measure 是
\[
       \frac{dt}{\zeta(1+2it)\zeta(1-2it)}.              \tag{CF4.3}
\]
对其两个原 shift 变量，(465.3) 在系数层逐项给
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
逐 \(d\) 精确抵消。只延长 PP 不合法。CF4.4--CF4.5 把连续谱
residues 放回同一原系数行，但不声称它已与物理 principal/axis 抵消。

## CF5. quotient 零模与双 Poisson 轴是不同的共同坐标

quotient Poisson 的 \(k=0\) 行是 (472.8)，即
\[
 Z^{(0)}_{A,B}=\frac{\mu(A)\mu(B)R}{A}\widehat f(0)
 \sum_{\substack{B\mid s\\(A,s)=1}}\frac{g(s/S)}s
 \sum_{h,\delta}v(h/H_1)w(\delta/H_2)c_s(h\delta).       \tag{CF5.1}
\]
对每个 prime power modulus，(477.1) 的有限二维差分核给
\[
 c_s(h\delta)=
 \sum_{\substack{d\mid s,d\mid h\\e\mid s,e\mid\delta}}b_s(d,e),
 \qquad
 \sum_{d,e\mid s}\frac{b_s(d,e)}{de}=\frac{\varphi(s)}s,
 \quad
 \sum_{d,e\mid s}\frac{|b_s(d,e)|}{de}\le\tau(s)^2.   \tag{CF5.2}
\]
这保留全部 mixed valuation splits。短边反例 (478.5) 表明
CF5.1 不能换成 complete-residue PP average。

双 Poisson 的 nonunit axes 则使用 (452.1)：两条 sampling line 与
一次负的 double integral，其系数分别为 \(1/C,1/C,-g_C/C^2\)。
当 \(g_C\ne1\) 时不可把它们写成同一系数。它们与 CF5.1 是不同
tags；“都是 principal-looking”不构成等同或抵消证明。

## CF6. 一个不重不漏的 master tag 集

在所有有限截断固定后，先按已经证明的 adapter 作一个互斥分割：
\(\mathscr P_{\rm exp}\) 是能合法使用 MC16/CF3/CF4 的指定平方自由
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

令 \(C_\omega\) 是从原有限和按上述恒等式逐次展开得到的系数。
这一定义唯一地保留以下规则：实际 \(b^\sharp\) 对只出现一次；
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

CF6.2 的证明是有限恒等式的复合：先 CF3，再 quotient Poisson 与
corrected lift，再 CF4/CF5，最后只在共同有限系数下求和。因此没有
Fubini 问题。取 \(\boldsymbol J\to\infty\) 时只使用每个固定
\(A,B\) 已证明的 local remainder limit；取 Eisenstein \(d\) cutoff
到无穷时必须把 CF4.5 四行一起取极限。本文不交换这些极限与全部
varying-level 外和。

## CF7. shell 的 \(A^{-1/2}\) 只计一次

在 shell prime \(p\) 的 ambient oldclass harmonic convention 中
\[
 P_1(0,0)=\frac1{(p+1)\rho_p}\asymp p^{-1}.              \tag{CF7.1}
\]
exact-shell ratio 是相对于 CF7.1 定义的。unshifted ratio
\(D_p(0,0)/P_1(0,0)=1-1/p\) 没有额外 saving；shifted \(b=0\) cell
给 \(O(p^{-1+\theta})\)；\(b=1\) AFE cell 的 ratio 是 \(O(1)\)，
但系数能量密度为 \(p^{-1}\)，故 Hilbert norm 为 \(p^{-1/2}\)。

所以 product shell 的 \(A^{-1/2}\) 是在 ambient harmonic measure
归一化后的 coefficient norm。CF6.2 中既不能再乘 CF7.1 的
\(p^{-1}\)，也不能另引入旧错误 cross-cusp 模型的第二个
\(p^{-1/2}\)。物理外权 CF2.2、Poisson 外因子 \(R\) 与该局部
Hilbert norm 是三个不同来源，各只计一次。

## CF8. 共同投影与 CF6.2 的精确接口

CF1.5 的 \(F_\sharp\) 左上块由 CT9 送入同一个
\(\mathfrak M_\sharp\)。HR14 在不改变 \(b^\sharp\) 的前提下给
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

CF1 的增广残差由 PCF11--16 在 HR15 中支付，得到已证明归约
\[
 \mathcal E_{\rho,P,\mathcal L}
 \le 2C_KH^2(\log N)^2\mathfrak R_\sharp(P)
       +O_\varepsilon(XHQ_PP^{a_*+\varepsilon}).         \tag{CF8.3}
\]
因此 projection top block 已进入同一链：它先以 CF1.5 的增广 Gram
精确出现，再通过唯一 \(b^\sharp\) 修正与显式残差进入 CF8.3。
它既未被删除，也未被错误送进一个只有短 shift support 的 QCT box。

## CF9. 当前唯一充分上界及其量词

固定一个假设零点 \(\rho=\beta+i\gamma\)、\(\beta>14/17\)，置
\[
 g=(17\beta-14)/3>0,\qquad \eta=g/4.
\]
先按 HR5 选择固定 \(K,r_{\rm cut}\)，再固定由此得到的同一个
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
这就是 HR16 的 CF6.2 展开版，没有新增 gate。特别地：

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
原稿 (405.5) 对固定 \(n=h\delta\) 给
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
\(P^{-1/24}\) 失败账，不是 HR16 的证明。

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
\(\chi,\psi\) 无关的 CF344.6 norm-one mixed-Bruhat 自伴块都可以
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
更一般地，把 (405.5) 的 \(A_{1,*}\mid h\delta\) 作为 \({\cal W}_q\)
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
 {\sqrt{A_tA_k}\over P};qquad
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
CF387.1 给 determinant 与全部 finite tags 的精确输运；CF386.1--CF386.4
给局部 shell 的有限 projective atoms；KW6 给归一化 archimedean 核的
有限阶一致导数。对固定紧支撑光滑部分，CF19.8 的连续变量分离可由
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

1. CF387.1 不改变任何系数地把完整 physical-shift 核写成
   \(pa_0t-qb_0k=j\)。这里 shell 的第一频率仍是 \(a_0j\) 或
   \(b_0j\)，没有把 \(t,k\) 冒充 shell frequency。
2. 在 balanced generic 支撑上
   \(|j|,|t|,|k|,a_0,b_0<P<p,q\)；因此 CF11 所需单位条件全部成立。
   \((a_0,b_0)=1\) 由 CF19.7 分离，费用 \(P^\varepsilon\)。
3. CF386.1--CF386.4 把每侧 exact shell 写成有限 projective atoms，
   总质量分别为 \(a_0^{-1/2+\varepsilon}\)、
   \(b_0^{-1/2+\varepsilon}\)。leading \(C_1\) 因 (405.4) 成为
   divisor-output，并由 CF19.6 支付；其他三个 atoms 有更强局部幂次，
   其总和已经包含在同一 projective mass 中。
4. CF344.6 的两种 mixed-Bruhat orientation 组成 norm-one 块。这个
   局部事实允许一个**已经构造出的**跨 level 分块映射作为
   CF19.1 的 \(\Theta_{p,q}\)，但它自身没有构造该映射。本步必须停留
   在 CF4.1 左侧的共同 geometric trace 上；不能把 Maaß parity、
   holomorphic、Eisenstein、diagonal 与 local remainder 擅自宣称为
   正交直和。

原先把这四步直接接到 CF19.10 是不合法的。首先发生了变量同名造成的
误接：KW6 控制的是原核
\(\Psi(r/R,s/S,\delta/L_h,h/H_M)\) 的归一化导数；CF387.1 中
\(G_{x,y,j}(v)=W(v/V)I_{x,y,j}(v)\) 的 \(v\) 是**第二次 Poisson 前的
physical shift**。CF387.1 只证明代数恒等式，没有证明后一个 \(v\) 的
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
\(\widehat G(-t/Q_0)\) 的一致 Schwartz 尾；KW6 不能代替 CF19.D。

其次，CF386.1--CF386.4 只给逐 level 的有限 projective atoms，
CF344.6 只给每个已选 mixed-Bruhat 块的范数一，CF387.1 只逐项输运。
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
其中左边是 CF387.6 的原带符号 determinant 行，右边的
\(E^L_\nu,E^R_\nu\) 必须逐字等于 CF377.3 已支付一次 shell half-root
后的 energies。特别不能把 \(a_0,b_0\) 的求和藏进
\(\Theta_{p,q}\) 的“有限维”二字。CF19.L 正是尚缺的 two-sided
critical-incidence orthogonalization，而不是 CF344.6 的推论。

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

CF19.D 中纯 affine-lattice 的 physical-shift 部分可以单独闭合，并且
不需要误用 KW6。不过短移位必须作为一个显式归一化坐标保留，不能
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
KW6 已控制原核的归一化 \(u,v,\alpha,\beta\) 导数；现在仍须逐项
写出这些坐标到 \((d/D,c/C,(P_0d-Q_0c)/V)\) 的链式映射，并核对
全部 finite tags。不能把短移位重新藏回 product 坐标，也不能仅凭
符号 \(v\) 相同而引用 KW6。

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

CF19.16 精确说明 CF19.C 可以如何被证明：必须把 opposite-shell 的
全部 auxiliary outputs 在变化 \(q\) **之前**写成同一组
\(q\)-无关向量 \(z_p\)，允许随后用 \(R_q\) 收缩。有限正交标签可放入
\({\cal H}\) 的直和，只需逐 \(p\) 保持总平方范数有界。反之，若实际
输出是任意 edge array \(z_{p,q}\)，它一般不能写成 CF19.15；CF17.4
已经给出这种数组仍可存在于非主子空间的精确反例。故 CF19.16 是
新的无损 analytic supplier，但“实际 mixed-Bruhat/complete-shift
输出属于共同 Hilbert 列”仍是 CF19.L 中必须逐项证明的解析内容。

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

本文已证明的只有：

1. CF1.5：共同投影的精确增广 Gram 等式；
2. CF3.1--CF3.2：quotient 两端点共同四行；
3. CF4.1--CF4.5：非零频率的全谱有限列与 Eisenstein 四行同系数；
4. CF5.1--CF5.2：零模、mixed valuations 与轴坐标不重不漏；
5. CF6.2：已展开行与显式 native complement 在唯一物理外权下的
   有限 master equality；这不声称补集已经谱化；
6. CF7：\(A^{-1/2}\) 与 harmonic/local shell 权不重复；
7. CF8.3：已有输出修正与全高度余量的接口；
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
    balanced generic 结论；现有 KW6、CF344、CF386、CF387 均不蕴含
    这三个输入。CF19.11--CF19.14 已独立支付第二次 Poisson
    的 affine physical-shift 导数与远频尾，把 CF19.D 缩成原完整
    \(F\) 的 normalized-seminorm pullback。CF19.15--CF19.18 把
    actual-Riesz 四阶矩严格扩张到任意共同 Hilbert 列及其逐模数
    contractions；它不接受 CF17 的任意 \(z_{p,q}\) edge array。
    CF19.8 仍须对实际 CF6.2 tags 完成逐行映射或独立支付。

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
