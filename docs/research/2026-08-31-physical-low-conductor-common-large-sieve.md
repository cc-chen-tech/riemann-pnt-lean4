# 低导子共同列：全 h/δ 共同 gcd 层降至 81/65

白话结论：之前低导子部分逐角色使用时间均值，丢失了不同导子之间的
共同系数结构。本文保留这个结构，对两条真实 Möbius 列一起使用普通
混合大筛，将 #549 同一局部原式的 gcd 尺度门槛从 687/550 降至 81/65。
这里 η 是共同 gcd 的尺度指数，不是 ζ 零点实部；仍未证明 14/17、2/3
或完整长 mollifier 渐近式。本稿不写 Lean，也不改变任何冻结父版本。

English summary: the exact low-conductor expansion has two coefficient
sequences shared across primitive conductors. Applying the ordinary hybrid
large sieve jointly, after a uniform bound for the separate squarefree column,
improves the same full h/delta common-gcd packet to 81/65 <= eta <= 5/4.
All canonical allocations at this fixed common-gcd layer are included.
This is a local analytic bound, not a new Möbius conjecture or a zero-free theorem.

## LC1. 原式、来源与命题

直接父版本 #549 为 d4b8de45932f77aaa98acf7ef7f84ff48074dd4f，
使用其 [CG1–CG18](2026-08-31-physical-common-gcd-full-reassembly.md)。
定义源固定 49cfacd70c60372757280177c7b63fd4f7760817 的
docs/research/2026-08-24-mobius-weighted-off-diagonal.md (4.4)–(4.5)。
辅助低部来源为
[TD5–TD10](2026-08-31-physical-full-delta-top-divisor.md)、
[AM12–AM17](2026-08-31-physical-full-delta-all-moduli.md)；
不把它们原结论直接赋给新范围，而重新估计同一个展开。

固定 q₀=1、T≥2、N=T³、R,S≍T³、M,K≍√T、KS≍MR、MK≪T。
比较常数固定，n,s 的整个内部包保证 n,s≤N/2。
保留原 p_N(n)p_N(s)F_R(n)F_S(s)、F_M、F_K、W、V_t；
不插入新的联合硬角点。原 h,δ 的全部分割合回，不保留固定 H/L 截断。
范数 D200 完全沿 CG1：每个原缩放因子的 C^200 范数加1按出现次数
相乘，再乘原 V 的加权混合导数范数；下文只支付这一份范数。

令原共同 e=gcd(s,h,δ)∈[E,2E)，E=T^η。对象严格是 CG4 的
\(\mathscr C_E^{\rm common}\)，包含全部 canonical a₀,b₀ 分配，
原条件为 gcd(q,u,v)=1 而不是 (uv,q)=1。定理：
\[
 |\mathscr C_E^{\rm common}|
 \ll_\epsilon \mathcal D_{200}T^{1+\epsilon},
 \qquad \frac{81}{65}\le\eta\le\frac54.                \tag{LC1}
\]
这是整个该层的界，不是每个 a₀,b₀ 硬子壳的单独界。

CG 中先在完整 centered 差里补回两轴，然后得到
\(\mathscr C_E^{\rm common}=\mathscr R_E-\mathscr P_E\)。
原 q=1 的整个 centered 括号为零；辅助 q'=1、两轴、辅助对角及
三种零频仍按 CG5 分别保留；
本稿既不删除它们，也不将原校正与新字符 principal 混同。

## LC2. 能跨导子共用的两条实际系数列

CG7 的 unmasked 顶项按 E'≥E 的自然壳分组，Q'=S/E'。
它有原有符号标记 β^μ，不添加 (V,q') 或 (m,q')。
沿 AM12 取 h=(e',m)，m=hz，e'=h a，
\[
 a=\ell d f l C,\quad n=fjX,\quad q'=ljY,\quad k=dr.
\]
这里 h 是 gcd(e',m)，不是原 Fourier h；d 是 reciprocal 频率 gcd，
不是原 Ramanujan 展开除数。χ 为模 ℓ 的本原角色，ℓ=1 的唯一角色另留。
精确时间与角色因子为
\[
 \left(\frac{\ell d l^2CY}{Xz}\right)^{it},\qquad
 \chi(Xzr)\overline{\chi(l^2CY)}.                    \tag{LC2}
\]
符号 μ²(f)μ²(l)μ²(C)μ(j)μ(X)μ(Y)、φ(f)φ(l)φ(C) 分母及
μ(ℓ)τ(\barχ)/φ(ℓ) 完整保留。I_k(t;hz) 是 TD5 的原积分，
与 X,Y,C,ℓ 无关。

固定 h,d,f,l,j,z,k 后，C 长度为 C_*=E'/(hℓdfl)，
N₁=R/(fj)、N₂=Q'/(lj)。f,l,C 平方自由两两互素，且
\[
 (flC,hkz\ell)=1,\quad(j,flhd\ell)=1,\quad
 (X,jflhd\ell)=(Y,jflhd\ell)=1.                       \tag{LC3}
\]
不添加 (C,j)、(C,X)、(C,Y) 或旧 TD 的 (Y,z)=1。
其中 X,Y 的 ℓ-unit 已由 χ 的零延拓精确保留。
去掉这种重复书写后，共同列系数就是
\[
 a_X=\mu(X)1_{(X,jflhd)=1}w_X(X/N_1),\quad
 b_Y=\mu(Y)1_{(Y,jflhd)=1}w_Y(Y/N_2).                 \tag{LC4}
\]
外层的 ℓ-unit 条件只筛选允许的导子；不会产生新的 X/Y 掩码。
它们的能量分别为 O(T^ε N₁)、O(T^ε N₂)。

共同权不是仅在固定 ℓ 下才可分离。明确置
\[
 c=C/C_*,\quad x=X/N_1,\quad y=Y/N_2.
\]
则 n=Rx、e'=E'c、q'=Q'y、s=E'Q'cy，原 B₀ 及抽出的归一化
幂次因子是同一个不依赖 ℓ 的光滑函数 w(c,x,y)。
原独立 e',n,q' 壳分别成为 c,x,y 的单变量区间。
三维 Fourier 分离满足
\[
 \sum_\nu|\widehat w(\nu)|(1+|\nu_c|)
 \ll\|w\|_{H^3},                                    \tag{LC5}
\]
因为 2·3>3+2。C 列的一个 BV 因子由此支付，X/Y 的 atom 系数可对
ℓ、χ、t 共用。允许 C 长度随 ℓ 变化；它下一步只用一致上界。
整包内部支持使原 mollifier 硬角点冗余，不另补 joint indicator。

## LC3. 先给 C 列一致界，再联合混合大筛

取 [Robert §5.1–5.2 (20)](https://perso.univ-st-etienne.fr/rool6510/robert-2015-indag.pdf)
的对数相位指数对 A³B(0,1)=(1/30,13/15)，记 κ=1/30、δ=1/6。
TD8 的完整平方／单位展开给每个固定 χ,t 的实际 C 列界
\[
 T^\epsilon\|w_C\|_{\rm BV}
 [T^\kappa(hdfl/E')^\delta\ell^{2\delta}+T^{-1}].
                                                               \tag{LC6}
\]
一份 ℓ^δ 来自 AP 分拆，另一份来自 C_* 的长度；二者都保留。
展开 μ² 时先保留平方除数 u 的 (u,D₀ℓ)=1，再令 C=u²vy，
不能将有重叠的 lcm 当成乘积，不截掉大 u。
此处 α=λ−κ=5/6，Σu^(-2α) 收敛；reciprocal-φ 的卷积也收敛。
非空极短 C 区间用平凡界，LC6 可大于1，不能据此删去该行。

令 L≤ℓ<2L、ℓ>1。对于 LC4 的两条共同列，记对应多项式 Aχ(t)、Bχ(t)。
取模后将 LC6 的一致界抽出，并使用一次 Cauchy 及
[Conrey–Iwaniec–Soundararajan (1.6)](https://arxiv.org/pdf/1105.1176)：
\[
 \sum_{\ell\asymp L}\frac{\sqrt\ell}{\varphi(\ell)}
  \sum_\chi^*\int_T^{2T}|A_\chi(t)B_\chi(t)|\,dt
 \ll T^\epsilon L^{-1/2}
       \sqrt{N_1N_2(L^2T+N_1)(L^2T+N_2)}.            \tag{LC7}
\]
这里 \(\sqrt\ell/\varphi(\ell)\ll T^\epsilon L^{-1/2}\)；
使用文献不带 ℓ/φ(ℓ) 的普通 hybrid large sieve 即可。
允许导子的扩和只发生在 Cauchy 后的正范数中。μ、固定单位条件和
任意复 atom 均留在共同系数中；不声称取模后仍是原复线性和等式。
Gauss 的 √ℓ 恰好计入 LC7 一次。

ℓ=1 的唯一新 principal 单独用普通时间均值，其费用等于下述 L=1
的四项；不在每个模数上复制诱导 principal，也不以 χ(0)=0 删除它。

## LC4. 四项、全部除数层与频率尾

LC7 展开的四项为
\[
 L^{-1/2}N_1N_2,\quad
 L^{1/2}\sqrt T\,N_1\sqrt{N_2},\quad
 L^{1/2}\sqrt T\,\sqrt{N_1}N_2,\quad
 L^{3/2}T\sqrt{N_1N_2}.                              \tag{LC8}
\]
先保持 z,k 固定应用 LC7，再计 z≍M/h、k/d≍T/(Kd)。
不含角色/Gauss 因子的唯一原物理系数为
\[
 \frac{\sqrt{TM/K}}
 {hd(E')^{3/2}\sqrt{RQ'}\,\varphi(f)\varphi(l)}.      \tag{LC9}
\]
乘 (fl)^δ 后，f,l,j 的幂依次为
\[
 (\delta-2,\delta-2,-2),\
 (\delta-2,\delta-\tfrac32,-\tfrac32),\
 (\delta-\tfrac32,\delta-2,-\tfrac32),\
 (\delta-\tfrac32,\delta-\tfrac32,-1).
\]
均不大于 −1，完整大 f,l,j 范围仅花对数／除数 ε 成本。
h≤O(M)、非空 d≤O(T/K) 的第一项求和给
T^κ(T/E')^δ，第二项为调和和。

记
\[
 B_1=\frac{T^{7/2}}{(E')^2},\quad
 B_2=\frac{T^{5/2}}{(E')^{3/2}},\quad
 B_3=\frac{T^{5/2}}{(E')^2},\quad
 B_4=\frac{T^{3/2}}{(E')^{3/2}}.
\]
每个导子壳的费用为
\[
 \mathcal D_{200}T^\epsilon
 [T^\kappa(T/E')^\delta L^{2\delta}+T^{-1}]
 [B_1L^{-1/2}+(B_2+B_3)L^{1/2}+B_4L^{3/2}].         \tag{LC10}
\]
特别 Q'<T 时 B₂,B₄ 仍保留，不把所有行当作两条长列。

在 |k|≍vT/K 的全非零环，k=dr 的真实计数为 O(vT/(Kd))，不补 +1。
原 I_k 的十二次非驻相积分给 v^-12；行数、h/d 改进和与含 k 的
除数范数至多增加 v^(1+δ+ε)，故全部大环收敛。负频及小环均保留。
每个环中先固定 z,k 使用 LC7，故 I_k 不会破坏共同列。
低部只消耗原 F_K,V 与共同权的相应预算，仍是一份 D200。

## LC5. 有符号旧 E 壳标记没有破坏共同系数

CG6 的 β^μ 不能改为任意 bounded 乘子。固定 F₀=hℓdfl，
e'=F₀C、(F₀,C)=1，每个标记除数唯一写成 d₁d₂，
d₁|F₀、d₂|C。令 C=d₂X₀，保留 (d₂,X₀)=1，则
\[
 E\le F_0X_0/d_1<2E.                                \tag{LC11}
\]
与原 C 壳相交仍是一个 X₀ 区间。μ(d₁)μ(d₂)、1/φ(d₂)、
所有原单位与 d₂ 的角色/时间标量保留；不新增 μ(X₀)。
对每个 ℓ，d₁ 仅有 τ(F₀) 项；逐项应用同一个区间一致界再求和即可。
无需假定不同 ℓ 的 d₁ 除数集合相同，因为抽出的只是 C 列上界。
X/Y 的支持与系数仍为 LC4；外部 ℓ、d₂ 互素仅筛允许导子。

H₀=max(1,E'/E) 时 d₂≲H₀，
\[
 \sum_{d_2\lesssim H_0}\frac{d_2^\delta}{\varphi(d_2)}
 \ll T^\epsilon H_0^\delta,\qquad
 \sum_{d_2\lesssim H_0}\frac1{\varphi(d_2)}\ll T^\epsilon.
\]
先支付 H₀^δ，再使用 (T/E')^δH₀^δ≍(T/E)^δ。
因此标记只将 LC10 括号内的 E' 换成旧 E；B₁,…,B₄ 中的 E' 不变。
原 dq'>1 条件保留；q'=1 仍沿 CG5 的模1格界单独支付，
可从本混合大筛估计中剥离，不能错误删除其有限贡献。

## LC6. 同一原式的低／高接合

2δ−1/2=−1/6，使第一项的 dyadic L 和收敛。
全部 ℓ<Λ（包括新 principal ℓ=1）的非零部分满足
\[
 \begin{split}
 |\mathscr R_{E,E',<\Lambda}|
 \ll \mathcal D_{200}T^\epsilon\big[&
 T^{1/30}(T/E)^{1/6}
   \{B_1+(B_2+B_3)\Lambda^{5/6}+B_4\Lambda^{11/6}\}\\
 &+T^{-1}\{B_1+(B_2+B_3)\Lambda^{1/2}+B_4\Lambda^{3/2}\}\big],
 \end{split}                                                       \tag{LC12}
\]
零频另外沿 CG5：内部 reciprocal 零频只在 ℓ=1 存在，
为 O(D200 T^(9/2−12+ε)/E')；原 unmasked 零模无 q'|m 稀疏性，
为 O(D200 T^(9/2−12+ε))。辅助 V=0 和 q'=1 格的费用是 O(D200 T^(1+ε))。
这些本来就在精确全式中，不能再次加减或强称每个投影保留原排零。

同一展开的 ℓ≥Λ 沿 CG10 的高部为
\[
 \mathcal D_{200}T^\epsilon
 [T+T^2/E'+T^{5/2}/(E')^{3/2}
                   +T^{7/2}/((E')^2\sqrt\Lambda)].    \tag{LC13}
\]
该原 native 剖面的 68 阶导数预算、高部完整 Mellin/对偶无限尾未变；
本文只改变低部的 Cauchy 顺序，不改变高部的对象或权。

取 Λ=max(2,T^(5−4η))。B_i 随 E' 增大下降，故最坏为 E'=E。
在 η=81/65、5−4η=1/65 时，LC12 第一行四指数为
\[
 (1,\ 124/195,\ 1/78,\ -68/195),
\]
第二行四指数为
\[
 (1/130,\ -47/130,\ -64/65,\ -35/26),
\]
高部为 (1,49/65,41/65,1)。所有指数随 η 增大下降或保持不变，
因此在闭区间 [81/65,5/4] 均不超过1。第一项准确为
37/10−13η/6；它在 η=6/5 仍为11/10，不得宣称该尺度已经支付。
有限高度 Λ=2 的常数可吸收。全部 E' 自然壳只有 O(log T) 个。

CG14–CG17 的实际 Ramanujan 校正独立为 O(D200 T^(1+ε))，
没有 η 下限，也不是上述新 ℓ=1 principal 的替代品。
将它与 LC12–LC13 在同一个 \(\mathscr R_E-\mathscr P_E\) 中接合，
得到 LC1。

## LC7. 新范围的意义、非空支持与边界

旧门槛减新门槛恰为 21/7150；这是该 gcd 尺度范围的小幅扩大，
不是零点实部的改进，也没有证明新的 μ 符号专属均值定理。
改变来自原共同系数上的标准混合大筛。

真实原整数支持存在：令 T→∞，选素数 e∈[T^(81/65),2T^(81/65)]，
再选素数 q≈T³/(100e)，s=6eq，选 n 素数在 (s,2s)。
取原 h=2e、δ=3e，得到 gcd(s,h,δ)=e，
canonical a₀=2、b₀=3，(n,s)=1，s,n≤N/2。
x=3√T/4 时 y=(nx+δ)/s 落在 [√T/2,2√T] 内（充分大 T）；
并且 hδT≪s²。由 Bertrand 可构成无限族，且 e/T^(687/550)→0。
这是原整数域非空，不声称任意给定 W,V 的积分必然非零。
脚本另用精确整数和有理数检查一个低于旧线的具体例子。

本稿仍不支付：η<81/65 的其余共同 e 层、q₀ 外壳、非内部 AFE
尺度及跨尺度统一尾、全局有符号算术 gate、14/17 或 2/3 零点排除。
不与其他固定 H/L 包的投影节省相乘。有限守卫验证共同掩码、
归一化、标记和有理指数；不替代 LC3 的解析输入、导数或无限尾证明。
