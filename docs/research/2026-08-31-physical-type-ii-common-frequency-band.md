# 长 Type-II：共同频率因子带的精确降模与局部预算

白话结论：在原三变量完成式中，三条频率共同含有模数的一个较大
因子时，可以精确降模，再恢复一个随剩余模数共同的系数列。
这不是给整个长 Type-II 换一个名字：在 E≈T^(6/5) 时，
共同因子≥T^(1/10) 的这个频率带得到 A₃₀T^(19/20+ε) 上界，
已经落入局部 T 预算；较小共同因子的完整有符号补集仍未支付。
特别地，素数模数的这一高因子带为零，素数模数难点没有因此解决。

## CB0. 固定原式和范围

直接父版本是 [HY0–HY19](2026-08-31-physical-type-ii-hyperbolic-incidence.md)
的799e5224d386832ca2d2a166030b46a07fc20d52（#528），其 TTC 来源为
779c0cffb51a0e834d39ea86f5571a5d21b1f008。解析共同列方法引用
[DP1–DP15 的冻结全文](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/7cc9646c8b8a8589b920e24652c86bd063f4b1d7/docs/research/2026-08-31-physical-centered-character-poisson.md)
（#514）。这两个依赖源均不修改。本篇不是把 DP14 原定理的
Q 换掉就直接套用；下文重新检查它的证明，原 R、S 和外权不变。

仅取 HY 的 q₀=a₀=b₀=1、同一个 FP1 重新插 F 后的内部 smooth 包：
r_phys=n，s_phys=eq，h=eu，δ=ev，e∈[E,2E)、q∈[Q,2Q) 平方自由，
(e,q)=1，R≈S≈EQ，HL≲RS/T，整包满足 n,s_phys≤N/2。
原 Ψ 和两个 taper 的归一化30阶预算记 A₃₀；不省去它的实际增长。
全部尺度和非零倒数处在固定 T 幂范围，Q≥2，u,v≠0。
不添加一般硬 H/L 边缘，不补入商变量的平方自由条件。

在 TTC2 的精确 C=I+II 中，I 有整体负号，II 为正号。
选定 II 中一个固定整数对集合 Ω，独立于 e、q 和其他外层标签；
可取整个 b>U_c、c>V_c，也可取它的乘积壳或 b/c 矩形。
max(U_c,V_c)<R/2 排除了 TTC 的小 n 有限边界。
写 B=bc、n=Bm，外掩码 (B,eq)=1，保留 μ(b)μ(c)。
周期核（单位掩码包含在核里）为
\[
 K_{q,\alpha}(m,u,v)=1_{(muv,q)=1}
   \{e_q(-\alpha uv\bar m)-\mu(q)/\varphi(q)\},
 \qquad \alpha=e\bar B\pmod q .                         \tag{CB1}
\]
核在非单位点定义为零。剩余 (m,e)=1 是核外掩码。
权为 p_N(Bm)p_N(eq)Ψ(Bm/R,eq/S,ev/L,eu/H)，唯一外权2T/(RS)。
以下投影是在这个已经确定的 Type-II 商坐标展开上操作；不宣称
它与先在未分解 μ(n) 的原 C 上做投影交换。

## CB1. 有限 Fourier 投影，不删除合数非单位频率

采用 TTC 的正号有限 DFT H_q(k,ρ,σ)，逆变换有负号及 q^(-3)。
对 r|q，定义 Π_r 保留 r|k、r|ρ、r|σ 的频率；这里 r 是
共同频率因子，不是原物理 r_phys。令 ℓ=q/r，则 CRT 精确给
\[
 H_q(rk,r\rho,r\sigma;\alpha)
   =\mu(r)\varphi(r)^2 H_\ell(k,\rho,\sigma;\alpha\bar r),
 \qquad
 \Pi_rK_{q,\alpha}
   ={\mu(r)\varphi(r)^2\over r^3}
                      K_{\ell,\alpha\bar r}.             \tag{CB2}
\]
证明：q 的 r 与 ℓ 局部分量互素。r 端三条加性频率均为零，
raw 核的三变量总和及 principal 的总和都等于 μ(r)φ(r)^2。
ℓ 端的原指数含 CRT 因子 r̄；加性频率 rk/q=k/ℓ，不再含该因子。
对 raw 乘积减 principal 乘积作差得到第一式，除以 q³ 得第二式。
不能把 centered 核写成各素数 centered 核的乘积。
ℓ=1 时整个 centered 核为零；没有新增 principal。

注意三条 r-unit 掩码已经被平均，不能重新附加。
例如 q=6,r=2 时 Π₂K 可在 m=2,u=v=1 非零，虽然原 K 在该点为零。
相反，核外的 (B,eq)=1、(m,e)=1 仍须保留。
αr̄ 也不能误写为 α：q=6,r=2,α=1,k=ρ=σ=−2 时
CB2 两边为−9/2，漏掉 r̄ 则右边变成9/2。

共同 gcd 恰为 g 的投影是
\[
 D_g=\sum_{j\mid q/g}\mu(j)\Pi_{gj}.
\]
对任意实数 G≥1，完整高带和低带满足有限恒等式
\[
 P_{\ge G}=\sum_{g\mid q,\ g\ge G}D_g
          =\sum_{r\mid q}w_G(r)\Pi_r,
 \quad w_G(r)=\sum_{g\mid r,\ g\ge G}\mu(r/g),
 \qquad P_{<G}=1-P_{\ge G}.                              \tag{CB3}
\]
w_G(r) 只依赖 r，不依赖剩余模数 ℓ；r<G 时为0，|w_G(r)|≤τ(r)。
这些系数有符号，例如 w₂(6)=−1；不能用正的投影和代替 CB3。
G=1 时只有 w₁(1)=1；q 为素数且 G>1 时只可能剩 Π_q=0。
三条整数零频率面已由 TTC 精确消去，其他合数非单位频率仍在。

在原 Type-II 和中以 P_(≥G)K 替换 K，定义 II_(Ω,≥G)。
在相同有限和中用 P_(<G) 定义其补集；两者严格相加为 II_Ω。
对于光滑原权，有限周期投影与普通 Poisson 兼容。即使先做
m=dz、d|e 的单位容斥，(d,q)=1 保证
gcd(q,dk,ρ,σ)=gcd(q,k,ρ,σ)，所以频率带没有被容斥换掉。

## CB2. 先还原完整单位条件，再建立共同列

固定投影 r、q=rℓ，保留 (r,ℓ)=(e,rℓ)=1。CB2 与外 μ(q) 融合为
\[
 \mu(q){\mu(r)\varphi(r)^2\over r^3}
     =\mu(\ell){\varphi(r)^2\over r^3}.                   \tag{CB4}
\]
仍有 (B,rℓe)=1，但 m,u,v 只须在 ℓ 端为单位。
把 HY 中 d|e 的完整容斥重新合并，或直接用 (m,e)=1，得到
\[
 \Gamma_r(n)=\sum_{bc\mid n,\ (b,c)\in\Omega\atop (bc,r)=1}
                            \mu(b)\mu(c),
 \qquad |\Gamma_r(n)|\le\tau_3(n).                       \tag{CB5}
\]
(B,e)=1 与 (m,e)=1 合成 (n,e)=1；B 的 ℓ-unit 条件由 n 的 ℓ-unit
条件强制。由此固定 r 的原和，除了 φ(r)^2/r³ 以外，精确是
\[
 {2T\over RS}\sum_{e,\ell,n,u,v}
  \mu(e)\mu(\ell)\Gamma_r(n)
  p_N(n)p_N(er\ell)\Psi(n/R,er\ell/S,ev/L,eu/H)
  K_{\ell,e\bar r}(n,u,v).                               \tag{CB6}
\]
核外保留 e,ℓ 平方自由及 (e,rℓ)=(r,ℓ)=(n,e)=1。
没有 (n,r)=1！n 可以有平方因子；它是原 μ 分解的代数子和。
若 Ω 限制依赖 ℓ，CB5 就不一定是共同列，本篇不认证那种扩展。

再次完整展开 (e,n)=1，e=fa、n=ft，其中 t 不是高度。
新的精确系数是
\[
 \mu(f)\mu(fa)\Gamma_r(ft)
   =\mu(f)^2\mu(a)\Gamma_r(ft)1_{(a,f)=1}.                \tag{CB7}
\]
f,a 与 r 互素；不能添加 (t,f)=1 或 (t,r)=1。
例如 e=2,n=4,r=3、Ω={b>1,c>1}，Γ₃(4)=1，f=1,2 项是−1,+1；
错误添加 (t,f)=1 把原来的0变成−1。

## CB3. 降模后的 DP 证明：原物理外权不变

写 ℓ=cλ，λ>1 为 primitive 角色的导子。
固定 r,f,c 及 λ≈Λ 时，A=E/f、B₀=R/f、U=H/E、V=L/E。
A 列保留 (a,frc)=1；B₀ 列为 Γ_r(ft)，仅保留 (t,c)=1，
λ-unit 用角色零延拓。外 (f,r cλ)=1 等原条件仍在。
Γ_r(ft) 随 λ 共同，且在 ft≤2R 上
\[
 \sum_{t\asymp B_0}|\Gamma_r(ft)|^2\ll_\epsilon B_0T^\epsilon.
                                                               \tag{CB8}
\]
非空时 A,B₀,U,V≥固定正常数；空整数域直接为0。
相对于 DP 的角色式，系数 e/r 仅多 χ(r^(-1))，模长为1，
不是向标签中塞入新的随 λ 变化的算术系数。

原权的第二坐标是 er cλ/S，不是 e cλ/S。
在 λ≈Λ≤2Q/r、c≈(Q/r)/Λ 上，E r cΛ/S≈1，
故五变量归一化分离的原30阶预算仍是 A₃₀，不产生 r 的导数损失。
特别地 S 不等于 E(Q/r)，绝不能据此缩小 S 或外权2T/(RS)。

对 u,v 的 c-unit 作 j,k|c 容斥，j,k 可以重叠。
两次 primitive Poisson 的系数模长仍为
UV/(jk φ(c)λ^(3/2))·λ/φ(λ)；r=0 或 s=0 的两个对偶整数
因非主 primitive 角色而消失。为避免记号混淆，以下称对偶整数
ξ,ζ，共同频率因子仍叫 r。对偶变量不补回 c-unit 掩码。

DP9 的真实联合权先部分 Fourier，再以五维 H³ 重建共同原子。
其推导对 u,v 各用12阶衰减、参数至多3阶，总阶≤27<30，
所以在 |ξ|≈M₁、|ζ|≈M₂ 上的 ℓ¹ 预算至多
A₃₀(1+M₁/D₁)^(-8)(1+M₂/D₂)^(-8)，D₁=Λj/U、D₂=Λk/V。
缩放 ercΛ/S 的有界性是复用此步骤的实际理由。

仅在取模后共轭 A 列，并把 aξζ 合为同一个整数乘积列。
τ₃ 碰撞能量≤K^(1+ε)，K≈AM₁M₂；B₀ 列用 CB8。
由 [primitive 乘法大筛 Theorem 16.2](https://kskedlaya.org/ant/chap-largesieve2.html)，
一个对偶块仍有 DP11 的费用
\[
 {UV T^\epsilon\over jk\varphi(c)\Lambda^{3/2}}
      \sqrt{B_0K(B_0+\Lambda^2)(K+\Lambda^2)}.            \tag{CB9}
\]
Γ 的额外除数界只需在初始选择更小的 ε；所有基础尺度在固定幂内。
无穷对偶的除数增长则保留为 (1+M_i/D_i)^ε，不能吞入 T^ε。
取 g(x)=max(√x,x)，DP12 的
Σ_(M≥1/2 dyadic)(1+M/D)^(-8+ε)g(M/D)≪1 对每个 D>0 一致，
因此所有双无限尾及 D_i<1 的边缘均支付，绝不把 D_i 补成1。

全部 j,k|c 只付 τ(c)^2；模数层的 Στ(c)^2/φ(c)≪T^ε。
固定 f 的四项是 AB₀√Λ、B₀√(AUVΛ)、A√B₀ Λ^(3/2)、
√(AB₀UV)Λ^(3/2)。全部 f≤2min(E,R) 的幂分别为
−2、−3/2、−3/2、−1，末项的 harmonic log 也已保留。
这逐项重跑了原 DP 证明，不要求 Λ²≤A,B₀。

因此固定 r，CB6 的绝对值在恢复 CB4 后至多
\[
 {A_{30}T^{1+\epsilon}\over RS\,r}
 \{ER\sqrt{Q/r}+R\sqrt{HL/E}\sqrt{Q/r}
       +E\sqrt R(Q/r)^{3/2}+\sqrt{RHL/E}(Q/r)^{3/2}\}.
                                                               \tag{CB10}
\]
|w_G(r)|≤τ(r) 吸收在除数预算；r≥G 的两种数列是 r^(-3/2)
和 r^(-5/2)，分别可和为 O(G^(-1/2)) 和 O(G^(-3/2))。
若 Q/r<1，唯一可能有效模数为1，而核为0，不调用空层大筛。
最终
\[
 \boxed{|II_{\Omega,\ge G}|\ll_\epsilon
 {A_{30}T^{1+\epsilon}\over RS}
 \{ER\sqrt{Q/G}+R\sqrt{HL/E}\sqrt{Q/G}
       +E\sqrt R(Q/G)^{3/2}+\sqrt{RHL/E}(Q/G)^{3/2}\}.}  \tag{CB11}
\]
这是线性和的估计，不是整个共同能量算子的范数界。

## CB4. 新支付的区域、非空见证和仍未支付的部分

平衡 R=S≈T³、H=L≈T^(5/2)，E≈T^η、Q≈T^(3−η)、G≈T^γ，
CB11 的四个指数为
\[
 {\eta-1-\gamma\over2},\quad 2-\eta-\gamma/2,\quad
 1-\eta/2-3\gamma/2,\quad 7/2-2\eta-3\gamma/2.           \tag{CB12}
\]
η=6/5 时，γ=1/10 给 1/20、3/4、1/4、19/20；γ=1/15 时最大值为1。
故大于这一共同因子阈值的长 Type-II 频率带付到了目标尺度。
不计 A₃₀ 增长时可这样比较指数；实际结论始终包含 A₃₀。
这是在旧完整 DP 的11/10基线上重新证明带上界，不是把某个独立
节省乘到 DP 或 HY 上。仅沿 HY 计数降模所得的1/G界更弱，
这里不将两个证明的节省重复相乘，也不包装成两项独立新覆盖。

在同一个包内取 U_c=V_c=floor(√E)<R/2。
I 的 bc≤E 已由 HY18 支付；II 严格 b,c>√E，从而 bc>E，
没有漏掉一个小乘积 II 边条。CB11 可用于整个这样的 II。
它并没有支付 II_(<G)；素数 q 全部落在那个补集。

给出不依赖密度定理的无限支撑：取 Y→∞，由 Bertrand 选互异素数
r≈Y、e≈Y¹²、ℓ≈Y¹⁷、b≈Y⁷、c≈Y⁸，令 q=rℓ、B=bc，
R=S=eq、N=8S、T=N^(1/3)≈Y¹⁰。取 m 为 (S/B,2S/B) 中素数，
m≈Y¹⁵，因而和前面素数不同；n=Bm 位于原壳中。
H=L=S/√T，取 ceil(H/e) 起连续三个整数中与 q 互素的 u，再令v=u。
ℓ 大于这些候选，而 r 至多排除一个，故选择存在。
原单位、n,s_phys≤N/2、genuine gcd=e、连续 AFE 支撑均满足；
b,c>√E。选择相邻光滑/dyadic 包只付固定常数。
原三条频率 k=ρ=σ=r 的共同 gcd 恰为 r。
它们在自然尺度 qB/R≈Y³、qe/H≈Y⁵ 内，不只是人为选出的远尾。
ℓ>2 时单位三频谱始终非零，CB2 的投影也非零。
这证明算术/频率范围非空，不断言任意指定 Ψ 的 Fourier 权非零。

脚本另检 e=101、r=5、ℓ=103、b=29、c=31、m=59 的原整数/AFE
支持见证，并检被平均掉的单位掩码、合数谱、带容斥的负系数、
Γ_r 的非平方自由 n 和所有有限归一化。有限检查不能证明解析大筛
或双无限尾；这些依据是 CB8–CB11 的重推。

仍开放：低共同频率因子带、原整个 signed Type-II、其他 canonical
分配、q₀外和、非内部包、跨 AFE 无限尾，以及共同能量的全部交叉项。
原 principal 与本 centered 投影分账；不将 #490/PT 或 #529 的
另一展开项移来支付本项，也不把原 μ 的商展开免费迁移到 amplified b。
总量的平方必须保留 band 与 complement 的两个交叉项。
没有证明完整 twisted moment、2/3 或14/17零点结论。

English: a disjoint common-frequency-divisor band in the fixed Type-II
completion admits an exact CRT descent and a common-column reconstruction.
Rerunning the double-Poisson proof pays that band, with the original physical
normalization and all dual tails. The low-common-divisor signed complement
and the full coupled-kernel gate remain open.
