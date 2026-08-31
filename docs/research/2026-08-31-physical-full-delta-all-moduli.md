# 全平方自由模数：完整 h/δ 包的三色重组

白话结论：本文去掉 #542 对 q 的“大素因子”限制。在同一个自然内部
FP3 双整除包中，完整单位容斥与三色素因子分配把所有原除数项变成
一族变尺度的辅助顶项。完整低／高导子连同原校正给
O(D200 T^(1+ε))，范围仍为 E=T^η、687/550≤η≤5/4。
新增的是含小素因子的 q，而不是更低的 E 门槛。η 不是零点实部；
其余 canonical 分配、q₀ 外层、AFE 尾和 14/17、2/3 结论仍未解决。

English summary: an exact three-colour divisor expansion removes the
roughness restriction on squarefree moduli in the natural internal full
h/delta FP3 packet. The auxiliary kernels are rescaled native kernels,
not ordinary AFE kernels with unchanged parameters. The old E-shell mark,
all unit masks, principal terms and zero modes remain explicit. This is
a local analytic argument, not a Lean theorem or a global zero-free claim.

## AM1. 冻结来源和完整原式

定义源为 49cfacd70c60372757280177c7b63fd4f7760817 的
docs/research/2026-08-24-mobius-weighted-off-diagonal.md，(4.4)–(4.5)。
直接父版本 #542 为 4755f16066830f17b13716bd160761cbf100b5a0，
本文使用其 RD1/RD2 的原包，**删去 rough 限制而不添加 q 硬盒**。
解析证明来源为：

- #538 f6c23380c481fbfa22874fbc57b88f102c46d452，TD3–TD8；
- #536 b3a758bcc01540aed5855bd3f1b10e4b7b660721，修补后的 RP6–RP9；
- #529 e833305712e4229c2eb141a7d84312f7581f9550，CH5–CH9；
- #532 08f7b664b294cb9649d76223188ed1da7f95eb83，FD2–FD6。

这些来源保持冻结。下文重跑适用证明，不把旧有符号总和的界直接
赋给任意新子项，也不引用另一条固定 H/L 双素数互反路线。

固定 q₀=1、T≥2、N=T³、R,S≍T³、M,K≍√T、KS≍MR、MK≪T。
原 e∈[E,2E)，E=T^η；n≍R、s=eq≍S 由原平滑权决定。
e,q 平方自由，(e,q)=(n,eq)=1，q>1。整个内部包保证 n,s≤N/2；
不是在后来的平滑权中另插二变量硬截断。q≍S/E 仅由原支持推出。
保留 B₀=p_N(n)p_N(s)F_R(n)F_S(s) 及全部实际 AFE 因子，定义
\[
 A_m(v)=\frac{F_M(m)F_K(y)}{\sqrt{my}}
 \int W(t/T)V_t(my)(sy/(nm))^{it}\,dt,\qquad
 y=(nm+ev)/s.                                             \tag{AM1}
\]
m 是正整数，y 始终连续；在 m,y>0 外按原紧支撑平滑延零。
固定本 AFE 层时 δ 整数有限、h Fourier 绝对收敛，故可合回完整 h/δ
分割；本文不保留额外 F(|ev|/L)，也不是任意固定 H/L 包的界。

目标是整个原 centered 和
\[
 \mathscr C_E=2\sum_{e,q,n,m}
 \frac{\mu(e)\mu(n)B_0}{\sqrt{ns}\,s}
 \sum_{(v,q)=1} A_m(v)
 \left\{\sum_{d\mid(q,nm+ev)}\mu(d)d-\frac{c_q(m)}{\varphi(q)}\right\}.
                                                               \tag{AM2}
\]
括号已经融合外 μ(q)，不再乘或删除一个 μ(q)。
D200 与 TD7 相同：原固定缩放因子的 C^200 范数加1按出现次数取乘积，
再乘
\[
 1+\max_{j+k\le200}\sup_{x>0,\ T\le t\le2T}
 (1+x/T)^{200}x^jT^k|\partial_x^j\partial_t^kV_t(x)|.
\]
结论为
\[
 |\mathscr C_E|\ll_\epsilon\mathcal D_{200}T^{1+\epsilon},
 \qquad 687/550\le\eta\le5/4.                            \tag{AM3}
\]
原 correction 单独由 FD14 支付。以下估计全部 raw 除数项，不遗漏 d=1。

## AM2. 完整单位容斥与旧 E 壳标记

写 q=d l。在 d|(nm+ev) 时，(v,d)=1 等价于 (m,d)=1；
对剩余 (v,l)=1 完整容斥，v=bw、b|l。令
\[
 e'=eb,\qquad q'=q/b,\qquad s=e'q'=eq.
\]
μ(e)μ(b)=μ(e')，全部原 n-unit 与 e'/q' 互素条件不变。
先对原 e∈[E,2E) 合计，再取绝对值，得到
\[
 \beta_E(e')=\sum_{\substack{b\mid e'\\E\le e'/b<2E}}1,\qquad
 \begin{split}
 \mathscr R_E=2\sum_{e',q',n,m}
 \frac{\beta_E(e')\mu(e')\mu(n)B_0}{\sqrt{ns}\,s}
 \sum_{d\mid q'}\mu(d)d\,1_{(m,d)=1}
 \sum_{d\mid nm+e'w}A'_m(w).                         \tag{AM4}
 \end{split}
\]
A' 是 (AM1) 用 e'、s 定义的同一个核。β≤τ(e')，非空时 e'≥E。
q'=1 也保留；精确有限版本的标记还有 bq'>1。渐近本域 e'=s≍S≫E，
故 q'=1 时 b=1 不在标记中，两写法一致。有界 T 用固定常数处理。

单个展开项不再要求 (w,q'/d)=1；也不补 (m,b)=1。
这是有符号展开项的重组，不是同一组原整数元组的无交子集。
没有独立原 q 硬盒至关重要：否则标记可能同时依赖 e'、q'。

## AM3. 完整频率系数的三色恒等式

记 x=q'/d。仿射 Poisson 的 Jacobian 为 x，原系数 d 使其成为 q'；
频率 k=xj，互反后所有项具有共同相位
\(e_{e'}(knm\overline{q'})\)。因此有限乘子恰为
\[
 \begin{split}
 C_{q'}(m,k)
 &=\sum_{\substack{x\mid q',\,x\mid k\\(m,q'/x)=1}}\mu(q'/x)\\
 &=\mu(q'/g)1_{g\mid k}1_{(k/g,q'/g)=1},\qquad g=(m,q').
                                                               \tag{AM5}
 \end{split}
\]
对每个 p|q'，C_p=1_{p|m}+1_{p|k}−1。乘开得到
\[
 C_{q'}(m,k)=
 \sum_{\substack{abc=q'\\a,b,c\ {\rm pairwise\ coprime}}}
       \mu(c)1_{a\mid m}1_{b\mid k}.                  \tag{AM6}
\]
这里“三色”是每个素因子分配给 a、b、c 的唯一标签；不同标签项
可在同一个 m,k 上同时非零，不能称为原支持的互不相交分割。
m、k 不要求平方自由；不能新增 (m/a,a)、(m/a,c) 或 (k/b,b)。
k=0 时 (AM5) 为 1_{q'|m}，不是恒零。全文保留所有整数频率。

## AM4. 每个颜色分量的原核精确缩放

置 m=az、k=bj、q'=abc。相位精确化为 \(e_{e'}(nzj\bar c)\)。
在连续变换 J_{bj}(az) 中令 y'=by，定义
\[
 S^*=S/(ab),\quad M^*=M/a,\quad K^*=bK,\quad s^*=e'c=s/(ab),
\]
\[
 F_M^*(z)=F_M(az),\quad F_K^*(y')=F_K(y'/b),\quad
 V_t^*(X)=V_t(aX/b).
\]
于是 J_{bj}(az)=(ab)^{-1/2}J_j^*(z)，且时间标量变为
\((s^*/(nz))^{it}\)。连同唯一物理外权，
\[
 \frac{q'}{\sqrt{ns}\,s}(ab)^{-1/2}
 =\frac1{ab}\frac{c}{\sqrt{ns^*}\,s^*}.                \tag{AM7}
\]
B₀ 精确保留为 p_N(n)p_N(ab s*)F_R(n)F_S(ab s*)。
逆 Poisson 因而把该颜色分量变成 1/(ab) 倍的辅助顶项
\[
 2\sum_{e',c,n,z}\frac{\beta_E(e')\mu(e')\mu(n)\mu(c)c\,B_0}
                         {\sqrt{ns^*}\,s^*}
                \sum_{c\mid nz+e'v}A_z^*(v).         \tag{AM8}
\]
这里 **没有 (v,c)=1，也没有 (z,c)=1**；不能调用带这个掩码的旧
TD2 结论而不重做证明。原 (n,e'abc)=(e',abc)=(a,b)=(ab,c)=1 全留，
不得新增 (z,ab) 或 (v,ab)。以下给所需重跑。

K*S*=M*R，但 M*K*=(b/a)MK 可超过 T，所以这不是原参数不变的普通
AFE 包。归一化 z=M*ζ、y'=K*ξ 后，
\[
 (a/b)M^*K^*\zeta\xi=MK\zeta\xi.
\]
原 V 的自变量及其缩放导数恰好不变；原 n,ab s*≤N/2 支持亦不变。
故辅助核的一致预算来自原 D200，而不是假设 V*_t 满足未缩放的衰减范数。

## AM5. 高导子：删除相应容斥，不删除 gcd 所迫的掩码

固定 a,b 及 e'≍E'、c≍Q*=S*/E'。令 h=(e',z)、e'=hA₀、z=hZ。
保留 (A₀,Z)=1，不加 (Z,h)=1。现在只展开 (n,c)=1，n=fx、c=fy；
符号为 μ(h)μ(A₀)μ(f)μ(x)μ(y)，还留
\[
 (h,A_0)=(f,hA_0)=1,\qquad
 (x,fhA_0ab)=(y,fhA_0ab)=1,\qquad (Z,A_0)=1.         \tag{AM9}
\]
固定 a,b 的原 e'/c 单位条件始终保留。**没有 (Z,f)=1**：
旧 CH2 的第二次 (Z,y) 容斥整个不出现。模 A₀ 的字符及其
primitive 分解仍合法，因为 n,c,Z 是 A₀-unit；w-unit 由同余强迫。

对 native 剖面用 TD12–TD13 的精确构造，换入 R,S*,M*,K*。
其归一化前因子 R S* M*/[√(ns*)s*√(zy')] 一致有界。
明确记 w_raw=(nz+e'v)/c=h w₀，则
u=log(cw_raw/(nz))=log(cw₀/(nZ))；角色 Poisson 使用下降后的 w₀。
在这个 u 上作 Fourier，保留 1/T；原 t 积分的
v=t/T 四十次 IBP、参数八阶和 uT 二十阶导数只需68阶原振幅导数。
AM4 保证这些导数由同一 D200 支付，即使 K*>T 也不损失。

现在重跑 CH5–CH9，等价于其数值计算取旧 l=1，并使用 (AM9) 的
正确较弱掩码。共同长 x 列与 yZr 产品列仍满足普通 primitive hybrid
large sieve 的条件；原 f、a、b 的单位限制是固定单列系数。
β(e') 在高导子仅为模数行乘子，可在取模后用 τ(e')。
这里使用 [Conrey–Iwaniec–Soundararajan (1.6)](https://arxiv.org/pdf/1105.1176)
的普通不等式，不使用该文的渐近大筛。CH9 节的完整 h/f/c/j 计数给
未乘物理外权的四项
\[
 RM^*S^*,\quad Q^*RM^*\sqrt{R/T},\quad
 (Q^*)^2M^*\sqrt{RE'},\quad
 (Q^*)^2RM^*/\sqrt{T\Lambda}.
\]
乘一次 2T/(R S* M*) 得
\[
 \mathcal D_{200}T^\epsilon
 \left[T+\frac{\sqrt{RT}}{E'}+
 \frac{TS^*}{\sqrt R(E')^{3/2}}+
 \frac{\sqrt T S^*}{(E')^2\sqrt\Lambda}\right].        \tag{AM10}
\]
a≍A、b≍B 的行数 O(AB) 抵消 (AM7) 的 1/(ab)，但不抵消
S*=S/(ab) 本身的缩小。合计这一颜色壳后四项是
\[
 T,\quad T^2/E',\quad
 T^{5/2}/[AB(E')^{3/2}],\quad
 T^{7/2}/[AB(E')^2\sqrt\Lambda].                      \tag{AM11}
\]

## AM6. 低导子：完整平方自由列与四个时间均值项

低导子用 TD3–TD6 的诱导 Poisson，保留 principal ℓ=1、
Ramanujan 非单位频率、Gauss 相位与 μ 的融合。为免变量混淆，
本节沿 TD7 记 A₀=ℓdflC、n=fjX、c=ljY；这些 f,l 与 AM5 的 f
不是同一分配。它们是 e'/h 的因子，故 (Z,fl)=1 **仍必须保留**。

相对旧 TD7 只移除来自旧 (z,c)=1 的 j、Y 上的 Z-unit：
f,l,C 平方自由两两互素，(flC,hkZℓ)=1，
\[
 (j,flhd\ell)=1,\quad
 (X,jflhd\ell)=(Y,jflhd\ell)=1.                      \tag{AM12}
\]
另保留原 a,b 对 e',n,c 的单位掩码；不加 (C,j)、(C,X)、(C,Y)。
C 列禁因子为原 D₀=flhkZℓ 再合并固定 ab。它不依赖 X,Y,j。
时间与字符仍严格是
\[
 (\ell d l^2CY/(XZ))^{it},\qquad
 \chi(XZr_0)\overline{\chi(l^2CY)}.
\]
因此每个固定 ℓ,χ 具有共同 X/Y 系数。用
[Vaughan Theorem 26.A](https://personal.science.psu.edu/rcv4/597-5f25/Class597-26.pdf)
的均值界 \(T^\epsilon\sqrt{N_1N_2(T+N_1)(T+N_2)}\)，不能删 Q*<T 的项。
TD10 的一般尺度版本、全部 h/d/f/l/j 计数给基本费用
\[
 L_0=\frac{\sqrt{RQ^*M^*/K^*}\sqrt T}{(E')^{3/2}}
 \left[1+\sqrt{T/Q^*}+\sqrt{T/R}+\frac T{\sqrt{RQ^*}}\right]. \tag{AM13}
\]
乘 (AM7) 并计整个 a,b 壳，四项依次为
\[
 \frac{T^{7/2}}{AB(E')^2},\quad
 \frac{T^{5/2}}{\sqrt{AB}(E')^{3/2}},\quad
 \frac{T^{5/2}}{AB(E')^2},\quad
 \frac{T^{3/2}}{\sqrt{AB}(E')^{3/2}}.                 \tag{AM14}
\]
仅有 |β|≤τ 不能使用下一节的振荡改进：必须用其实际除数标记结构。

## AM7. 旧 E 标记的振荡列预算

固定 F₀=hℓdfl，使 e'=F₀C 且 (F₀,C)=1。每个旧标记除数唯一写成
b_mark=b₁b₂，b₁|F₀、b₂|C。置 C=b₂X₀，保留 (b₂,X₀)=1。
旧条件变为
\[
 E\le F_0X_0/b_1<2E.                                \tag{AM15}
\]
与 C 的 dyadic 支持相交仍是 **一个 X₀ 区间**；其指标是单变量 BV，
不是未支付的联合硬边缘。φ(C)=φ(b₂)φ(X₀)，
\(b_2^{it}\bar\chi(b_2)\) 是固定模长≤1的标量；不得把它改作原线性和相等。
b₁ 只有 τ(F₀) 个。新的平方自由列禁因子包含 D₀b₂，所有原单位仍在。

取真实指数对 (κ,λ)=(1/62,57/62)、δ=1−λ+κ=3/31。
[Robert §5.1–5.2 (20)](https://perso.univ-st-etienne.fr/rool6510/robert-2015-indag.pdf)
与 TD8 的完整平方／单位容斥给 X₀ 列的
\(\ell^\delta T^\kappa(X_0\hbox{长度})^{-\delta}+T^{-1}\)。
明确先保留平方除数 u 的 (u,D₀b₂ℓ)=1，再展开单位除数；
不把重叠 lcm 错当乘积，不截掉大平方除数。

设 H₀=max(1,E'/E)，则 b₂≲H₀，且
\[
 \sum_{b_2\lesssim H_0}\frac{b_2^\delta}{\varphi(b_2)}
       \ll_\epsilon H_0^{\delta+\epsilon},\qquad
 \sum_{b_2\lesssim H_0}\frac1{\varphi(b_2)}
       \ll_\epsilon H_0^\epsilon.
\]
这正是标记的全部新费用。原 C_*^{-δ} 的 E' 不可先换成 E；
只有在 h≤O(M*)、d≤O(D*)（D*=T/K*）合计后，才使用
\[
 (M^*D^*/E')^\delta H_0^\delta
       \asymp [T/(abE)]^\delta.                     \tag{AM16}
\]
当 D*<1 时此处是中央尺度表达式，不虚构非零整数 d；
实际非空大环按下一节计数。导子个数和 AP 降长度仍分别支付
Λ^(3/2+2δ)、Λ^(3/2)，所以低部上界为 (AM14) 四项之和乘
\[
 T^\kappa[T/(ABE)]^\delta\Lambda^{3/2+2\delta}
                  +T^{-1}\Lambda^{3/2}.            \tag{AM17}
\]
多出的 D₀^ε 含无界频率，要留到每个频率环再支付，不能提前当成 T^ε。

## AM8. 全部无限环、短尺度和唯一范数

AM6 的非零 reciprocal 频率 k 在 |k|≍vD* 环时，
k=dr₀ 的非空行仅有 O(vD*/d) 项；非空强制 vD*/d≳1。
小于整数阈值的整行为空，绝不统一补 +1。大 v 的十二次原 y'-IBP
给 v^(-12)，h,d 求和增加 v^δ，环计数和除数范数增加
v^(1+ε)；几何和收敛。负频和小环也保留，不能只留驻相主项。
D*<1 时只有相应大环非空，同一全环上界仍成立。

AM5 的两个无限参数环逐项使用 CH8：新 Mellin |t'|≍τ 的剖面预算
(1+τ/T)^(-12)，对偶环 s₀ 小端最多 log⁸(1/s₀)，大端
s₀^(-10)log⁸(2s₀)。四个大筛项随 s₀ 至多一次幂增长，
随 τ/T 至多一次幂增长；额外除数 ε 幂均可吸收。
即使中央对偶长度小于1，实际大环仍按相同比例计数，不删掉整条尾。
a≤O(M)、abc≍S/E' 使全部有限参数在 T 的固定幂内；无界环另显式付费。

低部 I_k 仅消耗 F_K、V 的原范数；共同列分离只消耗原 F_R、F_S、
两份 p_N；外 W、F_M 各一次。高部剖面携带原范数，Poisson 符号
只用固定冗余 cutoff。AM4 的缩放不新增范数乘积，故始终是一份 D200。

## AM9. 三种零项与 c=1 不得混淆

第一，原完整 Fourier 的 k=0，由 (AM5) 强制 q'|m。
|J₀|≪D200 T√(K/M)T^(-12)，n/e'/q'/m 行数为
R·E'·Q'·(M/Q')，但外面仍有 Q'。用 E'Q'=S，费用为
\[
 \mathcal D_{200}T^{1+\epsilon}\sqrt{RMK/S}\,T^{-12}
       \ll\mathcal D_{200}T^{3/2-12+\epsilon}.       \tag{AM18}
\]
没有额外 1/Q'。本文可始终在 (AM6) 保留全 k；(AM18) 是独立核对，
不是又减一次同一个零项。

第二，辅助 v=0 现在允许 c|z，不能引用旧 top 的自动排除。
c≍C_*、E'C_*=S* 时，直接整包对角计数为
\[
 \frac1{ab}\frac{E'C_*R(M^*/C_*)\,C_*T}
                   {\sqrt{RS^*}\,S^*\sqrt{M^*K^*}}
       \ll T/(ab).                                  \tag{AM19}
\]
同样没有额外 1/C_*：原顶系数恰抵消除数稀疏性。
AM5–AM6 的全同余证明本已包含该点，此式说明即使另分出亦在预算内。

第三，AM6 内部 ℓ=1 的 reciprocal Poisson r=0 与原 k=0 不同。
十二次 IBP 的一般尺度成本是
\[
 \mathcal D_{200}T^{1-12}\sqrt{RQ^*M^*K^*/E'}
   \asymp\mathcal D_{200}T^{9/2-12}/(aE').
\]
计适配外权和 a,b 壳后为 D200 T^(9/2-12+ε)/(AE')。
ℓ>1 的该零项由 primitive 零延拓为零，不删除 principal。

最后 c=1 是无约束整数 v 格，不为空。按 FD 的模1格及完整外层计数
为 O(D200 T^(1+ε)/(ab))；也可在 AM6 的完整字符分解中保留处理。
a,b 每壳的 Σ1/(ab)≪1，所有这些边项只有对数层数成本。

## AM10. 所有模数、颜色和 E' 的合计

取 Λ=max(2,T^(5−4η))。AM11、AM14、AM17 对 E'≥E、A,B≥1
的指数均在最小尺度 E'=E、A=B=1 最大（E' 上界由原 s 和整数 c 给定）。
高部四项因此仍为 TD14；低部主指数仍为
\[
 \frac{749}{62}-\frac{275}{31}\eta\le1
       \quad\Longleftrightarrow\quad\eta\ge687/550.   \tag{AM20}
\]
左端的低部第二项指数是 2/275，高部为 (1,413/550,689/1100,1)。
各 E'/a/b dyadic 层仅 O(log³T)，边项 AM9 更小。
低 ℓ<Λ 与高 ℓ≥Λ 是同一辅助字符展开的严格互补，既不重叠也不删 principal。
由 (AM4)–(AM8) 的精确等式以及 AM10–AM19 得 raw 部分 O(D200 T^(1+ε))；
加 FD14 的原 correction，证明 (AM3)。

这不是先对每个原除数取绝对值后少算行数：β_E 先完整合计，
颜色之后才逐 a,b 壳估计；其全部 AB 行数已在 AM11/AM14 支付。
也不是把 #542 的粗模数节省乘另一频率投影的节省。

## AM11. 真正新增的原支持及未付范围

令 Y→∞，选互异素数 p≍Y^481、r≍Y^482，置 X=(16pr)^(229/321)，
由 Bertrand 选素数 X<e<2X。令 q=2pr、s=eq、N=8s、T=N^(1/3)，
R=S=s、M=K=√T、E=T^(687/550)。则
\[
 e/E=(e/X)^{321/550}\in(1,2^{321/550})\subset(1,2).
\]
取 n 为 (s,2s) 内素数、原 h=δ=e、u=v=1、x=3√T/4。
对大 Y，全部原 gcd、内部 mollifier、HL≤RS/T 和正 x/y 支持成立；
q 含素因子2，严格在 #542 rough 域之外。这里不声称任意权积分非零。

有限例 T=10^6、M=K=1000、e=32000011、p=50021、r=50101，
q=2pr、s=160390590878246662、n=160390590878246669、x=750，
脚本用精确整数／有理数核查原支持及 E≤e<2E。
新覆盖只去掉此自然 full h/δ FP3 包的 rough 限制。其他 canonical
分配、q₀ 外层、非内部尺度、跨 AFE 尾、整个 signed gate 仍保留；
不称 Reρ≤14/17 或 Reρ≤2/3 已证明，也不把固定 H/L 包一起认证。

有限测试核对原单位容斥、带联合权重组、三色完整频率、原核缩放、
标记列、零项费用及反例。它们不是解析指数对、混合大筛、统一尾界
或 Lean 的替代品；发布后的独立审查与 main 集成仍是另一个门禁。
