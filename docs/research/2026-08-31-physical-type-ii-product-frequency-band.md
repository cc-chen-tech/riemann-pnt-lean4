# 长 Type-II：频率乘积因子带与七类单位掩码

白话结论：不必要求一个大因子同时整除三条频率。只要模数的
若干素因子分别落在某条频率中，也可以精确降模；代价是保留
七类单位掩码，不能只拿其中一项。在 E≈T^(6/5) 时，
gcd(q,kρσ)≥T^(1/10) 的带满足 A₃₀T^(19/20+ε) 上界。
因此共同 gcd 小于该阈值、但乘积 gcd 大于该阈值的部分，
是本次新支付的区域。素数模数和低乘积 gcd 补集仍未解决。

## IB0. 原式、冻结来源与精确投影对象

直接父版本是 [CB0–CB12](2026-08-31-physical-type-ii-common-frequency-band.md)
的34e68771e46a0df3054ebc3b6604fa4c9305a7df（#533）。原 Type-II
来自 [HY](2026-08-31-physical-type-ii-hyperbolic-incidence.md) 的
799e5224d386832ca2d2a166030b46a07fc20d52（#528）；解析第二来源是
[DP 冻结全文](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/7cc9646c8b8a8589b920e24652c86bd063f4b1d7/docs/research/2026-08-31-physical-centered-character-poisson.md)
（#514）。这些已发布源树不修改。

范围完全沿用 CB0：q₀=a₀=b₀=1，同一个 FP1 重插 F 后的 smooth
内部包；e,q 平方自由，e∈[E,2E)、q∈[Q,2Q)、(e,q)=1，
R≈S≈EQ、HL≲RS/T、Q≥2，整包 n,eq≤N/2。全部基础尺度和
非零倒数处在固定 T 幂范围，原核和 taper 的30阶预算保留为 A₃₀。
Ω 是独立于 e,q 的固定 b,c 整数对集合，可取完整的长 Type-II
b>U_c,c>V_c，也可取其固定子集；max(U_c,V_c)<R/2。

先在原 μ 恒等式中令 B=bc、n=Bm。保留外部 (B,eq)=1、
(m,e)=1 及 μ(b)μ(c)。单位条件 (muv,q)=1 已放进周期核
\[
 K_{q,\alpha}(m,u,v)=1_{(muv,q)=1}
 \{e_q(-\alpha uv\bar m)-\mu(q)/\varphi(q)\},
 \qquad\alpha=e\bar B\pmod q.                       \tag{IB1}
\]
物理权是 p_N(Bm)p_N(eq)Ψ(Bm/R,eq/S,ev/L,eu/H)，外权2T/(RS)。
下面分解这个已固定 Type-II 商坐标核；不宣称投影与先前的 μ(n)
分解交换。投影后原非单位点可有贡献，两带相加才恢复原来的零；
不能在核外重新补回 (muv,q)=1。

## IB1. 局部不振荡因子的七项精确核

对 r|q，定义有限 Fourier 投影 I_r 保留 r|kρσ 的频率。
因为 q 平方自由，这要求每个 p|r 至少整除 k、ρ、σ 中的一条，
不是要求 p 同时整除三条。TTC 的正号谱约定不变。

在这样的 p 上，raw 三变量谱恰等于 principal 谱
\[
 P_p(k,\rho,\sigma)=-{c_p(k)c_p(\rho)c_p(\sigma)\over p-1}.
\]
但全 q 的 centered 谱是 raw 乘积减 principal 乘积，不是各
局部 centered 谱相乘；所以不能因此删除这部分合数频率。

记 u_p(x)=1_(p∤x)、a_p=(p−1)/p，定义
\[
 J_p(n,u,v)=-{1\over p-1}\left[
 a_p\{u_p(n)u_p(u)+u_p(n)u_p(v)+u_p(u)u_p(v)\}
 -a_p^2\{u_p(n)+u_p(u)+u_p(v)\}+a_p^3\right].          \tag{IB2}
\]
证明：一维单位函数的零 Fourier 模是常数 a_p，非零模为
u_p−a_p。将 principal 物理核 −u_p(n)u_p(u)u_p(v)/(p−1)
减去三个非零模的乘积，就得到 IB2。七项符号和常数项均必需。

令 J_r=∏_(p|r)J_p、J₁=1，ℓ=q/r。CRT 精确给出
\[
 \boxed{I_rK_{q,\alpha}(m,u,v)
          =J_r(m,u,v)K_{\ell,\alpha\bar r}(m,u,v).}    \tag{IB3}
\]
ℓ 端 α 要乘 inverse(r)；r 端的 principal 只含单位指示，因此
CRT 的互补逆元不再改变它。J_r 已是归一化逆 DFT，不能再乘 r⁻³。
ℓ=1 时 centered 核为零，不产生一个可另行移账的 principal。
J_r 对全部 r 剩余类的平均是 μ(r)φ(r)²/r³，恢复 CB2 的三条
频率同时为零的投影，但 J_r 本身不等于这个平均值。
例如 J₃(1,1,1)=−13/27、J₃(0,1,1)=−1/27。

## IB2. 七类掩码的全部费用

每个 p|r 选择 S_p⊂{n,u,v}、|S_p|≤2。令
r_i=∏_(p:i∈S_p)p，其中三个 r_i 可以两两重叠，但没有共同素因子。
记一组选择为 σ。则
\[
 J_r(n,u,v)=\mu(r)\sum_\sigma\theta_\sigma(r)
 1_{(n,r_n)=(u,r_u)=(v,r_v)=1},
\quad
 \theta_\sigma(r)={1\over\varphi(r)}
       \prod_{p\mid r}(-1)^{|S_p|}a_p^{3-|S_p|}.        \tag{IB4}
\]
共有7^ω(r)项，且
\[
 \sum_\sigma|\theta_\sigma(r)|
 \le {7^{\omega(r)}\over\varphi(r)}
 \ll_\epsilon r^{-1+\epsilon}.                       \tag{IB5}
\]
这是有限张量展开，不把掩码当光滑导数。原 μ(q) 和 IB4 的 μ(r)
融合为 μ(ℓ)，只融合一次；选择 σ 的正负号仍保留。

设 g_prod=gcd(q,kρσ)，g_com=gcd(q,k,ρ,σ)。与 CB3 同样的有限
Möbius 反演给出不交高带
\[
 P^{\rm prod}_{\ge G}=\sum_{r\mid q}w_G(r)I_r,
 \qquad w_G(r)=\sum_{g\mid r,\ g\ge G}\mu(r/g),
 \quad G\ge1.                                       \tag{IB6}
\]
w_G 不依赖剩余 ℓ，|w_G(r)|≤τ(r)、r<G 时为零，并可取负值。
原低带严格为1−P^prod_(≥G)。因为 g_com|g_prod，新部分的投影
严格是 P^prod_(≥G)−P^com_(≥G)，对应 g_com<G≤g_prod。
这是两个嵌套投影的差；估计它时用三角不等式，不把两个节省相乘。
三个全零坐标面仍为零，其他合数非单位频率完整保留。

## IB3. 原单位容斥和共同列没有换对象

固定 r、σ。B 是 r 的单位，故 J_r(m,u,v)=J_r(Bm,u,v)。
恢复 n=Bm，并合回 CB 的完整 d|e 容斥，仍恰得到
\[
 \Gamma_r(n)=\sum_{bc\mid n,\ (b,c)\in\Omega\atop(bc,r)=1}
                      \mu(b)\mu(c),\qquad|\Gamma_r(n)|\le\tau_3(n).
                                                               \tag{IB7}
\]
固定 σ 的原和，除了 θ_σ(r) 外，成为
\[
 {2T\over RS}\sum_{e,\ell,n,u,v}\mu(e)\mu(\ell)\Gamma_r(n)
 p_N(n)p_N(er\ell)\Psi(n/R,er\ell/S,ev/L,eu/H)
 1_{(n,r_n)=(u,r_u)=(v,r_v)=1}K_{\ell,e\bar r}(n,u,v). \tag{IB8}
\]
外部保留 e,ℓ 平方自由及 (e,rℓ)=(r,ℓ)=(n,e)=1。
没有完整 (n,r)=1，只有这一 σ 指定的 (n,r_n)=1。
例如 Γ₃(12)=1（Ω 为 b,c>1），而 J₃(12,1,1)≠0；把 n 强制
为 r 的单位会删除真实投影项。n 也不再强制平方自由。

完整展开 (e,n)=1，e=fa、n=ft，系数是
μ(f)²μ(a)Γ_r(ft)1_(a,f)=1。由于 (e,r)=1，f 与 r 互素，
新增 n 掩码恰为 (t,r_n)=1；不添加 (t,f)=1。
在 ℓ=cλ、λ 本原导子、λ≈Λ 时，令
A=E/f、B₀=R/f、U=H/E、V=L/E。
A 列保留 (a,frc)=1，B₀ 列为 Γ_r(ft)1_(t,c r_n)=1，
它对 λ 共同且平方范数≪B₀T^ε。其余 (f,r cλ)=1 等外掩码保留；
λ-unit 由角色零延拓。原相位只多模长1的 χ(r⁻¹)。

## IB4. 扩大标签容斥后重新支付 DP 的全部尾

两个标签的单位条件是 (u,c r_u)=(v,c r_v)=1，故容斥范围必须为
j|c r_u、k|c r_v。j,k 可重叠；它们都与 λ 互素。
只对 primitive χ mod λ 作 DP5 的角色 Poisson，绝不把角色
当作模 λr 的本原角色。两个 Poisson 后的模长系数仍是
\[
 {UV\over jk\varphi(c)\lambda^{3/2}}\,
                      {\lambda\over\varphi(\lambda)}. \tag{IB9}
\]
分母没有换成 φ(cr)；额外的 χ(jk)、χ(r⁻¹) 都是单位标量。
两个对偶零模仍消失，对偶整数不补入 r 或 c 的单位掩码。

原核的第二坐标始终是 ercλ/S。因为 ErcΛ/S≈1，固定 r,c,Λ
时仍有一致的五变量归一化预算 A₃₀。替换 u=jx、v=ky 后，
原 u/U、v/V 正是 x/(U/j)、y/(V/k)，不产生 j,k 的导数损失。
所有掩码由算术容斥处理，没有求它们的导数。

双对偶自然长度 D₁=Λj/U、D₂=Λk/V 可小于1。对原两个标签各
12阶分部积分，再加3阶参数导数，共27<30阶，得到 DP9 的
A₃₀(1+M₁/D₁)^(-8)(1+M₂/D₂)^(-8) 联合 C³ 预算。
五维 H³ 重建共同原子的 ℓ¹ 预算；n/标签之外的 Fourier 系数
对变化的 λ 共同。仅在取模后共轭 A 列，与两个对偶标签构成
整数乘积列，并保留全部 Γ_r 的除数预算。

[primitive 乘法大筛 Theorem16.2](https://kskedlaya.org/ant/chap-largesieve2.html)
给每对偶块 DP11 的界。以 g(t)=max(√t,t)，
Σ_(M≥1/2 dyadic)(1+M/D)^(-8+ε)g(M/D) 一致有界，支付全部双尾。
无穷 M/D 的除数增长显式留在这一级数中，不能直接称为 T^ε。
求尾后令 K₀=AΛ²jk/(UV)，费用为
\[
 {T^\epsilon\over\varphi(c)}
 \sqrt{AB_0\Lambda(B_0+\Lambda^2)(A+UV/(jk))}.          \tag{IB10}
\]
四项分别是
\[
 AB_0\sqrt\Lambda,\quad B_0\sqrt{AUV\Lambda/(jk)},\quad
 A\sqrt{B_0}\Lambda^{3/2},\quad
 \sqrt{AB_0UV/(jk)}\Lambda^{3/2}.                       \tag{IB11}
\]
第1、3项没有 j,k，第2、4项因子是1/√(jk)≤1。
所以新增容斥只多 τ(r)²：
τ(c r_u)τ(c r_v)≤τ(c)²τ(r)²，Σ_cτ(c)²/φ(c)≪T^ε。
不能再乘 Q/(rΛ) 个模数。全部 f 的四幂仍是−2、−3/2、−3/2、−1，
末项 harmonic log 保留；不要求 Λ²≤A,B₀。

## IB5. 新覆盖、所有外权和仍然开放的补集

由 IB5，固定 r、全部 σ 与 f/c/双尾后的原费用至多
\[
 {A_{30}T^{1+\epsilon}\over RS\,r}
 \{ER\sqrt{Q/r}+R\sqrt{HL/E}\sqrt{Q/r}
    +E\sqrt R(Q/r)^{3/2}+\sqrt{RHL/E}(Q/r)^{3/2}\}.     \tag{IB12}
\]
这里只付一次1/r，不在 CB10 现有因子之外再乘一次。
所有 r,σ,j,k 的有限除数预算以最初较小的 ε 统一吸收。
对 r≥G 求和的幂仍为−3/2、−5/2，故
\[
 \boxed{|II_{\Omega,\ g_{\rm prod}\ge G}|\ll_\epsilon
 {A_{30}T^{1+\epsilon}\over RS}
 \{ER\sqrt{Q/G}+R\sqrt{HL/E}\sqrt{Q/G}
   +E\sqrt R(Q/G)^{3/2}+\sqrt{RHL/E}(Q/G)^{3/2}\}.}    \tag{IB13}
\]
同一界（固定常数变化）也支付 g_com<G≤g_prod，由 IB6 与 CB11
作差得到。原 R,S 没有替换成 E(Q/r)，外2T/(RS)未变化。
Q/r<1 的可能有效层只有1，centered 核为零，不能对空层调用大筛。

在平衡 R=S≈T³、H=L≈T^(5/2)、E≈T^η、G≈T^γ 时，四指数仍为
(η−1−γ)/2、2−η−γ/2、1−η/2−3γ/2、7/2−2η−3γ/2。
η=6/5、γ=1/10 最大19/20，γ=1/15最大1。
这是扩大已支付的频率区域，不是同一区域把节省再乘一次。
实际界始终包含 A₃₀；本篇没有免费宣称所有原核的纯 T 上界。

严格新增区域非空：沿 CB 的 Bertrand 族，互异素数
r≈Y、e≈Y¹²、ℓ≈Y¹⁷、b≈Y⁷、c≈Y⁸、m≈Y¹⁵，q=rℓ、n=bcm，
R=S=eq、N=8S、T≈Y¹⁰。原整数/AFE 支撑与单位条件均沿 CB 保留。
改取频率(k,ρ,σ)=(1,r,1)，则 g_com=1、g_prod=r。
它们在自然 K≈Y³、L₁,L₂≈Y⁵ 内；r 端 principal 谱为−1，
ℓ>2 的单位三频 centered 谱非零，所以这个新增带并非零投影。
例如 q=15、α=1、(k,ρ,σ)=(1,3,1) 的谱为25/4。
这不声称任意指定 Ψ 的 Fourier 权或实际积分非零。

素数 q 的高 product-gcd 带仍为零：任何非单位频率都是一条
局部零坐标，centered 谱为零。因此低 product-gcd 带、特别是
三频率全部为模 q 单位的部分仍是实际难点。完整 signed II、
其他 canonical/q₀、非内部/跨 AFE 尾及能量交叉项仍开放。
不把 #490/PT、#529 或 #532 的不同校正移来支付这里，不自动迁移
到 amplified b，不声称完整 twisted moment、2/3 或14/17。

English: an exact seven-mask CRT decomposition enlarges the paid band from
the common gcd of three frequencies to the gcd of their product with the
modulus. The original normalization and all dual tails are retained. The
low-product-gcd signed complement and the full coupled-kernel gate stay open.
