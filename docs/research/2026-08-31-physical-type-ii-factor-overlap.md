# 长 Type-II：Möbius 因子重叠与稀疏共同列

白话结论：两个 Möbius 因子若有大公因子，合并后的整数必含一个
大平方因子。先合并这些项，再对共同列作大筛，可以保留这个
稀疏性，而不用逐公因子取绝对值。E≈T^(6/5)、gcd(b,c)≥T^(1/4)
时，该 Type-II 展开子和的上界从 A₃₀T^(11/10+ε) 改善到
A₃₀T^(39/40+ε)，节省1/8次幂。素数模数也允许。

这不是原 μ(n) 非零支撑中的新子族：阈值大于1时，本子和只落在
Type 恒等式扩展后的非平方自由 n 上。完整 I+II 才恢复原 μ(n)。
小因子重叠、全部原平方自由难点、principal 和全 gate 仍未支付。

## FO1. 冻结来源、完整物理对象及线性分账

直接父版本为 #535 的 a35e948c6d1a3846fe81575b51488ca4624a88c9，
复用 [IB0、IB7–IB11](2026-08-31-physical-type-ii-product-frequency-band.md)
中合回原商坐标的共同列，而不应用其频率投影。
Type 恒等式及完整单位容斥来自
[HY](2026-08-31-physical-type-ii-hyperbolic-incidence.md)
799e5224d386832ca2d2a166030b46a07fc20d52。
解析输入固定为 #514 的
[DP 全文](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/7cc9646c8b8a8589b920e24652c86bd063f4b1d7/docs/research/2026-08-31-physical-centered-character-poisson.md)。
不修改这些冻结树，也不引用 #490 旧非平方自由删项。

仅取 q₀=a₀=b₀=1，同一 FP1 重插原 F 的 smooth 内部包。
e,q 平方自由，e∈[E,2E)、q∈[Q,2Q)，Q≥2、(e,q)=1，
EQ≈S、R≈S、HL≲RS/T；整包 n,eq≤N/2，基础尺度在固定 T 幂范围内。
实际联合核 Ψ_sm 及 taper 的30阶预算记作 A₃₀，沿 DP2–DP4 定义，
不是对旧硬标签包求导。原物理系数是
p_N(n)p_N(eq)Ψ_sm(n/R,eq/S,ev/L,eu/H)，唯一外权2T/(RS)。

设 Ω 为独立于 e,q 的固定整数对集合，包含于 b>U_c、c>V_c，
max(U_c,V_c)<R/2；可再限制 bc>B_*，不要求逐 bc 块估计。
取实数 G≥1，定义
\[
 \Gamma_G(n)=\sum_{bc\mid n,\ (b,c)\in\Omega\atop\gcd(b,c)\ge G}
                         \mu(b)\mu(c).                 \tag{FO1}
\]
这里 (b,c)∈Ω 是有序对，不是互素条件。不能加 gcd(b,c)=1。
原商坐标 n=bc m 的核仍是
\[
 K_{q,\alpha}(m,u,v)=1_{(muv,q)=1}
       \{e_q(-\alpha uv\bar m)-\mu(q)/\varphi(q)\},
       \qquad\alpha=e\overline{bc}\pmod q.             \tag{FO2}
\]
原外部 (bc,eq)=1、(m,e)=1 全保留。把这些项按 n 合并，恰为
\[
 II_{\Omega,\ge G}={2T\over RS}
 \sum_{e,q,n,u,v\atop(e,q)=(n,e)=1}
 \mu(e)\mu(q)\Gamma_G(n)p_N(n)p_N(eq)
 \Psi_{\rm sm}(n/R,eq/S,ev/L,eu/H)K_{q,e}(n,u,v).       \tag{FO3}
\]
u,v≠0、全部原支持仍在；K 包含 (nuv,q)=1，故 n 的 q-unit 条件
没有删除。FO3 不强制 n 平方自由。其相位是原 e_q(-euv/n)，
标签乘积 uv 没有被独立替换为任意系数。

原 II_Ω=II_(Ω,≥G)+II_(Ω,<G) 是逐整数有限线性分账。
不把它叫频率正交投影，不删除任一能量交叉项。G>1 时 μ(n)≠0
意味着 Γ_G(n)=0，但 Γ_G(n) 自身不恒为0；不能因此将 FO3 删除。

## FO2. 完整 e/n 容斥后仍有统一稀疏能量

非零 μ(b)μ(c) 使 g=gcd(b,c) 平方自由，且 g²|n。因此
\[
 |\Gamma_G(n)|\le\tau_3(n),\qquad
 \operatorname{supp}\Gamma_G\subset
 \{n:\exists g\ge G,\ \mu^2(g)=1,\ g^2\mid n\}.       \tag{FO4}
\]
完整展开 (e,n)=1，e=fa、n=ft。因 e 平方自由，f 平方自由，系数
准确变为 μ(f)²μ(a)Γ_G(ft)1_(a,f)=1；不添加 (t,f)=1。
原 (e,q)=1 给 (f,q)=(a,q)=1，原 (n,q)=1 给 (t,q)=1。

令 B=R/f。对任意平方自由 f、B≥1/2、G≥1，有有限计数界
\[
 \#\{1\le t\le2B:\exists\text{ sf }g\ge G,\ g^2\mid ft\}
       \le {4B\tau(f)\over G}.                         \tag{FO5}
\]
证明：正确周期是 g²/(g,f)，不是 g²。并集计数不要求见证 g 唯一，
每个周期的点数至多 floor(2B(g,f)/g²)，所以无需额外 +1。
再用
\[
 \sum_{g\ge G}{(g,f)\over g^2}
 =\sum_{d\mid f}\varphi(d)\sum_{g\ge G,d\mid g}g^{-2}
 \le {2\tau(f)\over G}.                              \tag{FO6}
\]
内和至多 2min(d⁻²,(dG)⁻¹)，分别按 d≥G、d<G 即得最后不等式。
FO6 可放大到所有 g；FO5 只需平方自由 g 的子集。
如果 2fB<G²，支持为空，原和直接为0。

结合 FO4，所有模长≤1的共同权 ξ_t 和任意额外单位掩码均满足
\[
 \sum_{B/2\le t\le2B}|\xi_t\Gamma_G(ft)|^2
 \le \max_{1\le t\le2B}\tau_3(ft)^2\,{4B\tau(f)\over G}
 \ll_\epsilon {B\over G}T^\epsilon.                   \tag{FO7}
\]
只把除数函数的增长吸收进 T^ε；G⁻¹ 不丢失。
f 可与 g 重叠。例如 f=t=g=7 时 Γ₇(49)=1（Ω 取 b,c>1），
正确周期是7而非49。f 的平方自由性也必要，不能推广到任意 f。

## FO3. 保留真实列范数，而不缩短大筛长度

固定 f、q=cℓ、primitive conductor ℓ≈Λ>1。令
A=E/f、B=R/f、U=H/E、V=L/E。A 列保留 (a,fc)=1，
B 列为 Γ_G(ft)1_(t,c)=1，ℓ-unit 由角色零延拓；无 (t,f) 掩码。
各外部 (f,cℓ)=1 等原条件也在。
对 u/v 的 c-unit 用 j,k|c 完整容斥，允许 j,k 重叠。

原角色相位、Gauss 因子、两次 Poisson 和中心减项均与 DP5–DP8
相同，只有共同 B 列由 μ(t) 类系数变为 Γ_G(ft)。其中 Γ 不依赖
变化的 ℓ、e、u、v；固定 f 后可作共同系数。μ(f)²留在外部。

原五变量联合核先双 Fourier，再依 DP9 的 H³ 分离。两个对偶
自然长度 D₁=Λj/U、D₂=Λk/V 可小于1，非零整数块记 M₁、M₂≥1/2。
实际预算仍是
A₃₀(1+M₁/D₁)^(-8)(1+M₂/D₂)^(-8)，原导数阶≤27<30。
共同原子只给 t 列乘模长1的 Fourier 权，FO7 对每个原子一致。

按 DP10，仅取模后共轭 A 列，与双对偶标签组成乘积列。
该列长度 K≈A M₁M₂、能量≪K^(1+ε)；单独的 B 列能量现在是
BT^ε/G。使用 [primitive 乘法大筛 Theorem16.2](https://kskedlaya.org/ant/chap-largesieve2.html)
后，每块上界（不含上述核预算）为
\[
 {UV\over jk\varphi(c)\Lambda^{3/2}}
 \sqrt{(B/G)K(B+\Lambda^2)(K+\Lambda^2)}\,T^\epsilon
 \prod_{i=1}^2(1+M_i/D_i)^\epsilon.                    \tag{FO8}
\]
特别是 B+Λ² 没有改成 B/G+Λ²：这是稀疏能量，不是短区间长度。
它恰为 DP11 的 G⁻¹/² 倍，且不依赖双尾尺度。
DP12 的 max(√t,t) 几何级数支付全部无限尾，包括 D_i<1。
无穷对偶区间的除数增长保留在该收敛级数中，不直接称作 T^ε。

## FO4. 所有外层与净节省

求双尾后保留的共同因子是 G⁻¹/²。j,k|c 的总费用至多τ(c)²；
Σ_(c≈Q/Λ)τ(c)²/φ(c)≪T^ε，不能再乘一次模数个数 Q/Λ。
四项 f 幂仍为 −2、−3/2、−3/2、−1，FO7 多出的 τ(f)^(1/2)
及有限除数增长由最初较小的 ε 吸收；末项 harmonic log 保留。
所有 Λ≤2Q、全部 f≤2min(E,R)、两个对偶无限尾均已包含。
恢复原外权得到
\[
 \boxed{|II_{\Omega,\ge G}|\ll_\epsilon
 {A_{30}T^{1+\epsilon}\over RS\sqrt G}
 \{ER\sqrt Q+R\sqrt{HL/E}\sqrt Q
       +E\sqrt R Q^{3/2}+\sqrt{RHL/E}Q^{3/2}\}.}        \tag{FO9}
\]
全过程先合并全部 g≥G，不能在已给 G⁻¹/² 后再对 g 逐个求和。
也没有将 #533/#535 的频率节省与之相乘。

平衡 R=S≈T³、H=L≈T^(5/2)、E≈T^η、Q≈T^(3−η)、G≈T^γ 时，
完整四指数是
\[
 (\eta-1)/2-\gamma/2,\quad2-\eta-\gamma/2,\quad
 1-\eta/2-\gamma/2,\quad7/2-2\eta-\gamma/2.            \tag{FO10}
\]
η=6/5、γ=1/4 给 (−1,27,11,39)/40；γ=1/5 已达到1。
原 DP 对此固定 Ω 的无稀疏性 majorant 为11/10，故本例改善1/8，
不是从平凡项估计中另取一个可相乘的 saving。实际 A₃₀ 始终保留。

## FO5. 展开子和的非空性及仍然开放的部分

存在无限原整数/AFE 支持的 Type-II 展开见证：取互异素数
e≈Y²⁴、q≈Y³⁶、g≈Y⁵、b'≈Y⁸，再在
(eq/(g²b'),2eq/(g²b')) 用 Bertrand 选素数 c'≈Y⁴²。
令 b=gb'、c=gc'、m=1，则 n=bc∈(eq,2eq)、gcd(b,c)=g，bc>E。
取 R=S=eq、N=8S、T=N^(1/3)≈Y²⁰，G≈Y⁵；阈值常数可取
使 g≥G。相邻 dyadic 包取整只改固定常数。
明确取原 AFE 尺度 K_z=M_z=√T，H=L=S/√T；因 R=S，
K_zS/(M_zR)=1 且 K_zM_z=T。u=v=ceil(H/e)≈Y²⁶<q，全部原单位条件成立。
x=3√T/4 使 y=(xn+ev)/S∈[√T/2,2√T]，对充分大Y成立。
bc>E、b,c>floor√E，故也属于现有短乘积结果未支付的长区。
取 Ω 为这两个下界及 bc>E；唯一可重复的素数是 g，两个自由
素数必须分别分配给 b,c，故 Γ_G(n)=2，合并后也不是零系数。
原三频自然长度为 Qbc/R≈Y³⁶、QE/H≈Y¹⁰，单位频率(1,1,1)
在其中，prime-q 的 centered 三频谱非零；不靠频率尾制造见证。

一个有限实例是 e=101,q=103,b=35,c=55,m=7，n=13475，
R=S=10403、N=8S。gcd(b,c)=5、bc>E、n 为非平方自由；
Γ₂(n) 在 b,c>floor√E、bc>E 的集合上非零。
这证明展开子和与实际核支持非空，不证明任意指定 W/F 的积分
非零，更不称它在原 μ(n) 非零支撑上非空。

与已发表平方自由分布估计的适配比较：

| 输入 | 这里的适配边界 |
| --- | --- |
| [Gorodetsky–Matomäki–Radziwiłł–Rodgers，Theorem1](https://arxiv.org/abs/2006.04060) | 无权短区间方差范围 H<X^(6/11−ε)，不直接控制原 signed Γ/μ 双列；旧 S=T³,D=T² 也超出此范围。 |
| 同文 Theorem2 | 本文陈述为素数模数、单位剩余类方差，不能替代此处全部平方自由 q 与共同系数。 |
| primitive 大筛 + FO5 | 确实保留真实列能量；给 FO9，但不从平方自由密度臆造原 μ 消去。 |

本结果不是文献新颖性声明；新增的是相对于本项目既有费用，
明确支付了大 factor-overlap 的长 Type-II 展开区域。
低 gcd(b,c)（尤其互素因子）、完整原平方自由难点、principal、
其他 canonical/q₀、跨 AFE 尾及共同能量四项仍开放。
不能以 FO9 支付 #490 的整个 E_nsf，二者没有在此建立同一分账。
原 gate 和完整 twisted moment 均未证明。

English: a square-divisor support bound survives the full e/n inclusion–
exclusion and improves the common-column energy by G^(-1). It pays a
large factor-overlap sector of the expanded Type-II sum, including prime
moduli, not the original nonzero Möbius support or the complete gate.
