# 增长小因子乘大素数：原 Type-II 的完整 CRT 两分支

白话结论：#524 的素数模数结论不能直接套给合数。把原核拆成
“小因子的原相位 × 大素数中心核”和“小因子中心核 × 大素数均值”，
两部分都付费后，可以覆盖一个小因子随 T 增长的真实合数区域。
例如 E≈T^(6/5)、小因子≤T^(1/10)、bc≤T^(3/5)，费用为
O(A₁₄₄T^(3/5+ε))；逐 bc 完成的旧预算为 T^(6/5+ε)。
这不改善整个长 Type-II 补集，也不证明全部合数模数或完整 moment。

## NP0. 固定原式、唯一大素数标签与实际光滑权

直接父版本是 #524 的 b33add1b6bd494a226e5ab00d3b3ced26b0d17c2，
[PII0–PII18](2026-08-31-physical-type-ii-prime-incidence.md)。
继续使用 TTC/FP1 重插 F 的内部 smooth 包，q₀=a₀=b₀=1，
r=n、s=eq、h=eu、δ=ev，外权唯一为 2T/(RS)。
本篇改变的是允许的约化 q 子族，不改原核、截断或 Möbius 系数。
e∈[E,2E)、q∈[Q,2Q)，R≈S≈EQ；e,q 平方自由，(e,q)=1。
全部原单位条件、n,s≤N/2 的整包支持、HL≲RS/T 及固定幂尺度
仍按 PII1 保留。A_j 是同一个实际归一化核的 j 阶半范数。

取 C_*≥1、C_*²<Q，选择
\[
 q=\ell p,\qquad \ell\le C_*,\quad p\text{ prime},
 \quad(\ell,p)=1.                                      \tag{NP1}
\]
ℓ=1 包括原素数列，但本篇也覆盖增长的 ℓ>1。
每个这样的 q 只有一个标签：p=q/ℓ≥Q/C_*>C_*≥ℓ；
若两个不同大素数都满足条件，第一个必整除另一个的 cofactor，
与该 cofactor≤C_* 矛盾。因此以下始终按原 q 行计数，
不能先付 Q 行又额外乘 C_*。

取 max(U_c,V_c)<R/2，沿 PII2 的精确 μ(n) 恒等式写 C=I+II，
II_≤ 选 b>U_c、c>V_c、B=bc≤B_*；II_> 是完整剩余部分。
没有 (b,c)=1，也没有对无符号商重新加 μ 或平方自由限制。
固定 e,q,b,c，要求 (B,eq)=1；(n,e)=1 完整容斥给
n=Bdz、d|e、a=e/d，剩余掩码为 (zuv,q)=1，
全部符号 μ(e)μ(q)μ(b)μ(c)μ(d) 不变。定义
\[
 \alpha=a\bar B\pmod q,\quad
 Z=R/(Bd),\ X=H/e,\ Y=L/e,\quad (a,B)=1.               \tag{NP2}
\]
实际非分离权仍是
\[
 W(z,u,v)=p_N(Bdz)p_N(eq)
       \Psi(Bdz/R,eq/S,ev/L,eu/H).                      \tag{NP3}
\]
它在归一化紧盒上光滑，z>0、z≤2Z、0<|u|≤2X、0<|v|≤2Y，
没有新增联合硬边缘；z/u/v 的零点附近权为零。内部 taper 平滑，
混合每轴 J 阶由 A₃ⱼ 支付，归一化后无 B、d、ℓ 的导数因子。

## NP1. 先在物理域保留两个 CRT 分支

令 e_t(x)=exp(2πix/t)，定义带完整单位掩码的三个周期核
\[
 R_{t,\beta}=\mathbf1_{(zuv,t)=1}e_t(-\beta uv\bar z),\quad
 P_t={\mu(t)\over\varphi(t)}\mathbf1_{(zuv,t)=1},\quad
 K_{t,\beta}=R_{t,\beta}-P_t.                           \tag{NP4}
\]
t=1 时 R=P=1、K=0。CRT 所需的**物理**系数是
α_ℓ=α·p⁻¹ mod ℓ、α_p=α·ℓ⁻¹ mod p；不是简单的 α mod ℓ。
逐整数精确有
\[
 K_{q,\alpha}=R_{\ell,\alpha_\ell}K_{p,\alpha_p}
                      +K_{\ell,\alpha_\ell}P_p.         \tag{NP5}
\]
这是 R_ℓR_p−P_ℓP_p，不能换成 K_ℓK_p。
特别是第二项并不自动为零，本篇 NP13–NP16 将独立估计它。

采用正号三变量有限 DFT。记 R_t、P_t、H_t 为上述三个核的谱。
CRT 下每个局部的 α,k,ρ,σ 都乘互补模数的逆元。TTC4 的
Ramanujan 公式在这四个参数同乘单位时取值不变，所以仅在
**谱的数值表达式**里，可以将局部四参数写回 α,k,ρ,σ：
\[
 H_q=R_\ell H_p+H_\ell P_p,\qquad
 H_p=p^2\mathbf1_{(k\rho\sigma,p)=1}
      \{\mathbf1_{p\mid ak+B\rho\sigma}-1/(p-1)\}.      \tag{NP6}
\]
例如 q=6、ℓ=2、p=3、α=1、k=ρ=σ=2 时第一项为 −9/2；
频率非 q 单位不能删除。q=15、ℓ=3、p=5、k=5、ρ=σ=1 时
第一项0、第二项−9/2；p 整除 k 的低模项也不能删除。
TTC4 的每素数 raw 谱满足 |R_r|≤2r²（四种单位/非单位情形
直接检查），于是 |R_ℓ|≤τ(ℓ)ℓ²。这只用于高分支的上界。

## NP2. 高分支的常数必须整体反变换

三维 Poisson 的系数为 q⁻³。NP6 高分支的常数谱是
−R_ℓ p²/(p−1)·1_(kρσ,p)=1。完整逆变换精确等于
\[
 -{1\over p(p-1)}\sum_{z,u,v}W(z,u,v)
     R_{\ell,\alpha_\ell}(z,u,v)c_p(z)c_p(u)c_p(v).     \tag{NP7}
\]
无额外 ℓ 或 q 因子。证明可先在有限群 q 上作反变换：
CRT 把 q⁻³ 分成 ℓ⁻³p⁻³，R_ℓ 反成原物理核，p 的三个单位
频率和各反成 c_p，p² 剩下1/p。再用普通 Poisson 接到 W。
这个证明不需要 W 分离，也不要求 Z,X,Y 比 p 小。

由 PII8 的离零 floor 界和 |R_ℓ|≤1（此处是物理核），
\[
 |\mathrm{Const}_{B,d,e,q}|
   \ll A_0 ZXY/p^2\le A_0 C_*^2 ZXY/q^2.             \tag{NP8}
\]
这里“常数”是高分支 Fourier 校正，不是原 global Ramanujan
principal。若允许 u=0 或 v=0，上述无 +1 的计数会失效。

## NP3. 高分支的整数共振和全部非零同余尾

高分支 incidence 的谱系数满足 q⁻³p²|R_ℓ|≤τ(ℓ)/q。
令 Δ=ak+Bρσ。整数 Δ=0 仍强制
\[
 k=Bt,\quad\rho\sigma=-at,\quad t\ne0.               \tag{NP9}
\]
保留其 p 单位条件；上界时可扩大。由于 |k|Z/q≈a|t|，
完全沿 PII11–PII12 求全部 d|e 和 t，有
\[
 \sum_{d\mid e}|\mathrm{Res}_{B,d,e,q}|
      \ll_J A_{3J}\tau(\ell)XY/B.                    \tag{NP10}
\]
依据是 Σ_a τ(a)a^(1−J) 与 Σ_t τ(t)t^−J 在 J≥4 时收敛；
不把无限 t 的除数函数界写成统一 T^ε。

取 Λ≥2，并强化原 PII13 为实际条件
\[
 B_*\Lambda^2(4EQ/R+16E^2Q^2/(HL))\le Q/(2C_*).        \tag{NP11}
\]
自然频率 K=q/Z、L₁=q/X、L₂=q/Y 的 Λ 矩形内
|Δ|≤Q/(2C_*)<p，所以 p|Δ 只可能是 Δ=0。
并没有把 p 换成 q 来使用素数间隙。
对全部矩形外频率，用 PII14 对任意 L>0 的统一尾界
Σ_(|n|>ΛL,n≠0)(1+|n|/L)^−J≪_J LΛ^(1−J)，得到
\[
 |\mathrm{Tail}_{B,d,e,q}|
      \ll_J A_{3J}\tau(\ell)q^2\Lambda^{1-J}.         \tag{NP12}
\]
K,L₁,L₂ 小于1时不补成1；p 单位已排除三个整数零坐标。
三轴各 J 阶衰减来自总阶3J，所有频率尾绝对可和。

## NP4. 低 cofactor 分支：显示条件下的完整周期完成

NP5 第二项的真实物理形式为
\[
 -{1\over p-1}\mathbf1_{(zuv,p)=1}
                         K_{\ell,\alpha_\ell}W.       \tag{NP13}
\]
它不适用 NP11 的 p 频率间隙。另要求
\[
 2H/E<Q/C_*,\qquad 2C_*E/H\le1/2.                    \tag{NP14}
\]
第一条使 |u|≤2X<p，且 u≠0，所以 **只有 u 的 p-unit 掩码**
在真实支持上冗余；z、v 的 p-unit 条件全部留在原整数和内。
第二条给 X≥H/(2E)≥2C_*≥2ℓ。不能从 HL≲RS/T 自动推出它们。

固定 z,v；若非 ℓ 单位该行0，否则 u↦K_ℓ 的一周期均值恰为0：
Σ_(u modℓ)^* e_ℓ(−α_ℓv z̄u)=μ(ℓ)，正好减去 μ(ℓ)。
每个有限 Fourier 系数模长≤2ℓ。对实际 W 的 u 坐标作完整
一维 Poisson（其余坐标只是固定参数），零频精确消失，故
\[
 \left|\sum_u K_{\ell,\alpha_\ell}(z,u,v)W(z,u,v)\right|
 \ll_J A_J X\sum_{k\ne0}(1+|k|X/\ell)^{-J}
 \ll_J A_J X(\ell/X)^J.                              \tag{NP15}
\]
J>1 时全 k 和收敛；ℓ=1、2 时中心核本来恒零。
光滑分片避免联合硬边缘，固定 z,v 后原 u 导数由 A_J 统一控制。
取 z/v 的有限整数绝对和（正 z 及非零 v），得到逐行
\[
 |\mathrm{Low}_{B,d,e,q}|
   \ll_J {A_J ZXY\over p}(\ell/X)^J.                 \tag{NP16}
\]
该项中不把 μ(ℓ) 或其它外符号当作新 Möbius 消去。

## NP5. 全外层费用、真实新增范围及剩余量

恢复全部 e,q,d,b,c。共振和尾用至多 O(Q) 个原 q 行，
τ(ℓ)≤T^ε；分别得到 HLQ/E 和 EQ³B_*Λ^(1−J)。
常数用 Σ_(bc≤B*)1/(bc)≪log²(2B*)、Σ_(d|e)1/d≪T^ε、
Σ_e e⁻²≪1/E、Σ_q q⁻²≪1/Q，得 C_*²RHL/(EQ)≈C_*²HL。
低模项用 (ℓ/X)^J≤(2C_*E/H)^J，且由唯一标签精确有
\[
 \sum_{q\text{ in NP1}}1/p
   =\sum_q\ell/q\le C_*\sum_{Q\le q<2Q}1/q\ll C_*.
                                                               \tag{NP17}
\]
不是 Σ_q q/p，也不能再乘一次 cofactor 数量。
因此低模费用为 A_JT^ε RHL C_*/E·(2C_*E/H)^J。
所有外和有限；NP12、NP15 的可和 majorant 允许所用积分/求和
换序，没有未付的频率截断。恢复唯一外权，得到
\[
 \boxed{|II_\le|\ll_{J,\epsilon} A_{3J}T^\epsilon
 \left\{ {THLQ\over RSE}+C_*^2{THL\over RS}
 +{TEQ^3B_*\over RS}\Lambda^{1-J}
 +{THL C_*\over SE}(2C_*E/H)^J\right\}.}              \tag{NP18}
\]
同一证明只使用 b,c 模长≤1、原单位条件和短乘积范围，故若
U_cV_c≤B_*，也支付 I+II_≤，不是两种 saving 相乘。

平衡 R=S≈T³、H=L≈T^(5/2)，置 E=T^η、Q≈T^(3−η)、
B_*=T^β、C_*=T^γ、Λ=T^ω。NP11 渐近充分条件为
β+1+2ω+γ<3−η；NP14 与唯一性要求分别为
5/2−η<3−η−γ、γ+η<5/2、2γ<3−η。
NP18 四个指数是
\[
 3-2\eta,\quad2\gamma,\quad
 4-2\eta+\beta-(J-1)\omega,\quad
 3-\eta+\gamma+J(\gamma+\eta-5/2).                    \tag{NP19}
\]
取 η=6/5、β=3/5、γ=1/10、ω=1/25、J=48，四项分别
3/5、1/5、8/25、−557/10，频率间隙为1/50。
取 U_c=V_c=floor(T^(1/10))，新 II_≤ 包含两个长因子。
原 TTC16 逐 bc 的两个指数为2/5、6/5；新最大3/5，
相对旧可用上界改善3/5。A₁₄₄ 明确保留，不是无条件把它取1。

无限真实合数非空族：Y₀→∞，由 Bertrand 选择互异素数
e≈Y₀²⁴、ℓ≈Y₀、p≈Y₀³⁵、b≈Y₀⁵、c≈Y₀⁵（相邻倍长区间），
设 q=ℓp、R=S=eq≈Y₀⁶⁰、N=8S、T=(8S)^(1/3)≈Y₀²⁰，
H=L=S/√T、K_z=M_z=√T。于是 ℓ≤C_*≈Y₀²、B≈Y₀¹⁰≤B_*≈Y₀¹²，
b,c>U_c,V_c≈Y₀²。选素数 m∈(S/B,2S/B)，其尺度Y₀⁵⁰
大于其它素数，置 n=Bm。令 u=v 为 ceil(H/e) 或其后一个整数，
选择非 ℓ 倍数者；ℓ>2 保证存在，u≈Y₀²⁶<p，因此 (uv,q)=1。
全部 (n,eq)=1、(s,h,δ)=e、n,s≤N/4 成立。
原 x₀=3√T/4 给 y=(x₀n+ev)/S 落原 AFE 支持。
NP11 左右比 O(T^(-1/50))，NP14 也最终严格满足。
取相邻有限个 dyadic smooth 包只改固定常数；不声称任意指定
W/F 的积分非零或该区域具有正密度。

本结果只扩大短乘积的模数范围，不降低长乘积总账。作为比较，
在与 [DP4/DP14](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/7cc9646c8b8a8589b920e24652c86bd063f4b1d7/docs/research/2026-08-31-physical-centered-character-poisson.md)
完全相同的 smooth 包上限制 qprime，DP 的非主分解只余 c=1、ℓ=q，
取模后的 CS/大筛正能量可扩大模数集。因此 η=6/5 时已知
|C|≪A₃₀T^(11/10+ε)。结合 #524 的 I+II_≤ 界，**整个** prime
II_> 有 A₁₄₄T^(11/10+ε) 上界；不是每个 B 块的同界，更不是
任意重新加权后的算子界。该现有推论不作为本篇新增覆盖。

尚未付：NP1 以外的合数 q、全部长 II_>、其它 canonical 分配、
外 q₀/非内部尺度及尾、原 principal 与完整共同能量交叉项。
有限脚本只检查 CRT、相位、计数、指数与支持；不证明解析尾、
实际 A₁₄₄ 的全局预算或完整 coupled-kernel gate。

English: an exact raw/centered CRT split extends the short-product Type-II
bound to a genuinely growing small-cofactor family. Both the large-prime
incidence and the low-cofactor branch are paid, with every Fourier tail
and outer count retained. The full modulus and long-product complements
remain open.
