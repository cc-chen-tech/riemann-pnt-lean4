# 双标签角色 Poisson：原式光滑重分包与中心化 5/4 区域

白话结论：先从原始未分块和精确插入光滑单位分解，再对两个标签
作角色 Poisson。保留全部对偶尾并重新得到共同系数后，中心化
光滑包在平衡 E≥T^(5/4) 时满足局部 T^(1+ε) 预算。
这不是把旧硬壳免费平滑化，也不是旧 CS7 单个硬包的 5/4 定理。
单包 principal、其他 gcd 分配、非内部包及全局余项不在本定理内。

父版本采用范围修正后 36d62a54497af2545ca1998251ad0b46177a5b19 的
[PL1–PL11](2026-08-31-physical-centered-pv-large-sieve.md)。
CS0/PL1 现同样明确重插原 F，不再认证一般 literal 硬壳。
本篇 DP1–DP4 独立给出新包定义，仅复用精确角色恒等式及经典大筛，
不以旧 0d468dd0/dae4a560 的硬包物理适配作为前提。
原式来自
[冻结物理索引 FP1–FP4](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/7cf2e7d43c4365e38e2aa708d1a250694b698bec/docs/research/2026-08-30-mwkf-frozen-physical-atom.md)，
其定义源为 49cfacd70c60372757280177c7b63fd4f7760817。
不修改这些冻结文件。

## DP1. 必须从 FP1 重分包，不能保留标签硬边缘

FP1 的原标签域是 h,δ≠0。沿用原非负 C_c^∞ dyadic partition F，
支撑在 [1/2,2]，满足
\[
 \sum_{H\in2^{\mathbb Z}}F(|h|/H)=1\quad(h\ne0).
                                                               \tag{DP1}
\]
δ 同理。把两个单位分解插入 FP1，再按原 r、s、AFE 参数分包。
每个固定非零整数对只遇到有限多个 H,L，所以这是逐项的精确
重新分组；不宣称无条件交换尚未控制的全局无限尾。
若先对原标签作任意有限截断，分解恒等式严格成立；该截断不用来
定义下面的单个光滑包。
更具体地，固定 q₀,R,S,K_z,M_z 时 r,s 有限，原 F_(M_z)、F_(K_z)
的紧支撑使 δ 也只有有限个。对这些固定参数，h 和是紧支撑光滑
x 核的 Fourier 系数和，反复 x 分部积分给绝对收敛，允许在这一层
完整插入 DP1。更外层无限 AFE 包仍按原求和约定保留，不由此获得
一致的全局尾估计。

具体令原无 h/δ 硬边缘的 FP1 核经 FP2 的变量缩放后为 Ψ_raw，
把原 r/s 光滑权以及 F(|α|)F(|β|) 吸收进去，得到
\[
 \Psi_{\rm sm}(x,y,\alpha,\beta)
   =\Psi_{\rm raw}(x,y,\alpha,\beta)F(|\alpha|)F(|\beta|).
                                                               \tag{DP2}
\]
原 mollifier 因子另保留；只在 q₀n,q₀eq≤N/2 的内部、HL≲RS/T
工作，并要求与 FP §3 一致的完整实际核参数。这里 q₀ 固定平方自由，
所有基础尺度在固定 T 幂范围内。r/s 原平滑因子若尚未含于
Ψ_raw，则一并含入 DP2，不再额外计一次。
上述 N/2 条件由选定内部整包的支持保证，使原 mollifier 截断冗余；
不再插入 1_(q₀fa cℓ≤N/2) 之类硬的联合 indicator。

新半范数明确为
\[
 \mathcal A^{\rm sm}_J=\max_{|\alpha|\le J}
                         \|\partial^\alpha\Psi_{\rm sm}\|_\infty,
 \qquad J\ge30.                                             \tag{DP3}
\]
它来自原 raw 核及新光滑分割，不是对旧硬截断包求导。
内部固定阶导数由原核预算控制；更大 log-core 须付其实际半范数。

选择同一 FP3 算术层 s=eq、r=n、h=eu、δ=ev：
e∈[E,2E)、q∈[Q,2Q)，EQ≈S，e,q 平方自由，
(e,q₀q)=(n,q₀eq)=(uv,q)=1。新包定义为
\[
 C_{\rm sm}={2T\over q_0RS}\sum
 \mu(e)\mu(q)\mu(n)p_N(q_0n)p_N(q_0eq)
 \Psi_{\rm sm}(n/R,eq/S,ev/L,eu/H)
 \{e_q(-euv\bar n)-\mu(q)/\varphi(q)\}.                     \tag{DP4}
\]
所有 u,v≠0 求和；**不再附加**旧 H≤|h|≤2H、L≤|δ|≤2L
硬 indicator。a/b/q 的一变量硬壳可留在系数或允许模数中。
旧硬包若权在边缘非零，只有 BV，Fourier 尾一般为 1/|ξ|，
不能由本篇回溯认证。全部光滑包与原和的关系由 DP1 保证；
未估计的包必须留在补集，不能选取部分包后称已恢复整个原和。

中心项没有换对象：此算术层上
c_(eq)(hδ)/φ(eq)=μ(q)/φ(q)，因为 (eq,hδ)=e。
这里只估计 global centered 和的真实光滑线性包，不估计其单包
principal，也不在平方量中删除 cross 项。

## DP2. 容斥、单位掩码与两次精确角色 Poisson

完整展开 (e,n)=1，e=fa、n=fb，保留
μ(f)μ(a)μ(b)1_(ab,f)=1，不重新加 (a,b)=1。置
A=E/f、B=R/f、U=H/E、V=L/E；全部 f≤2min(E,R) 在内。
原 r 的支持含于 [R/2,2R]。非空时 A,B≥1/2，且
1≤|u|≤2U、1≤|v|≤2V，所以 U,V≥1/2；空包直接为0。
新光滑支持在 |u/U|、|v/V|∈[1/4,2]，并非旧 [1,2] 硬壳。
对平方自由 q=cℓ 使用 CS5–CS7 的唯一 primitive 分解：
ℓ>1、(c,ℓ)=1、(c,fq₀)=(ℓ,fq₀c)=1。A/B 列仍保留
(a,fq₀c)=(b,fq₀c)=1；ℓ-unit 用角色零延拓。

固定 f,c 及导子壳 ℓ≈Λ。对标签 c-unit 作完整容斥，
j,k|c，可重叠，不能要求 (j,k)=1。用 Fourier 约定
\(\widehat w(\xi)=\int w(x)e(-x\xi)\,dx\)，primitive χ mod ℓ 有
\[
 \sum_m w(jm/U)\chi(jm)
 ={U\over j}{\chi(j)\tau(\chi)\over\ell}
       \sum_{r\in\mathbb Z}\bar\chi(r)
                      \widehat w(rU/(j\ell)).             \tag{DP5}
\]
这是分剩余类后作普通 Poisson，再用 primitive Gauss 恒等式；
参见 [Tao 的 twisted Poisson 式 (51)](https://terrytao.wordpress.com/2014/12/15/254a-supplement-3-the-gamma-function-and-the-functional-equation-optional/)。
该文用正号 Fourier，换成本篇负号约定后得到 DP5。
ℓ>1 时 χ(0)=0，双对偶的 r=0 或 s=0 项均精确消失。
ℓ=1 始终是 principal，不用于 DP5；平方自由 q=2 无非主部分。

原 CS7 Gauss/符号满足
\[
 \tau(\bar\chi)\chi(-1)\tau(\chi)^2=\ell\tau(\chi).
                                                               \tag{DP6}
\]
因此两个 Poisson 后，原归一化的模长准确是
\[
 {UV\over jk\,\varphi(c)\ell^{3/2}}
                          {\ell\over\varphi(\ell)}.       \tag{DP7}
\]
原 μ(f)、μ(ℓ)、μ(j)μ(k)、barχ(c)χ(jk) 与
τ(χ)/√ℓ 全留在精确表达式；取上界时才用其模长≤1。
对偶 r,s 不再带 c-unit mask，不可重新加上它。

## DP3. 先变换真实联合权，再重建共同列；含完整无限尾

这一步不先把旧 BV 原子当 Schwartz。保持参数
p=(b/B,a/A,ℓ/Λ)，令 W_f(p,x,y) 为原实际联合权，
x=u/U、y=v/V。其标签因子包括 F(|(a/A)x|)、F(|(a/A)y|)；
原 Ψ 的其他坐标为 b/B、(EcΛ/S)(a/A)(ℓ/Λ)。
固定的外 cutoff 只在这些联合支持的投影上等于1，不制造硬边缘。
在固定紧盒上，W_f 的 C^J 预算≪A^sm_J，统一于所有允许参数。
内部 p_N(q₀fa cℓ) 包含于此光滑权，p_N(q₀fb) 可留在 b 列。

对 W_f 的 x,y 先作二维部分 Fourier，记 Φ_f(p,ξ,ζ)。
两次 DP5 后的精确算术相位是
\[
 \chi(a)\bar\chi(b r s),
 \qquad
 \Phi_f\bigl(p,rU/(j\ell),sV/(k\ell)\bigr).               \tag{DP8}
\]
这是五变量真正联合权，未假装已可分离。

令 D₁=Λj/U、D₂=Λk/V，可以小于1。
将全部非零对偶整数分为平滑 dyadic 块 |r|≈M₁、|s|≈M₂，
M_i≥1/2，分别处理符号。置 t_i=M_i/D_i。对归一化坐标
(p,r/M₁,s/M₂)，其 Fourier 权是
Φ_f(p,t₁(r/M₁)/(ℓ/Λ),t₂(s/M₂)/(ℓ/Λ))。
固定紧盒上所有总阶≤3的归一化导数满足
\[
 \|\cdot\|_{C^3}\ll
 \mathcal A^{\rm sm}_{30}(1+t_1)^{-8}(1+t_2)^{-8}.
                                                               \tag{DP9}
\]
明确的导数账：频率/参数的3次链式求导最多各带 t_i³。
对原 x,y 分别应用 (1−∂_x²)^6、(1−∂_y²)^6，使各频率衰减12阶；
频率微分只产生紧支撑 x/y 矩。加最多3阶参数导数，所需原总阶
≤24+3=27<30，故留下至少9阶衰减，DP9 的8阶安全。

在五维用 Sobolev H³ 与 Cauchy，因 2·3>5，共同 Fourier 原子的
ℓ¹ 系数和由 DP9 控制。这次没有额外标签 BV 权。
每个原子的 a、b、r、s 系数对变化的 ℓ 共同；只要求固定
f,c,j,k,Λ,M₁,M₂ 后共同，不跨这些外参数假设共同。

## DP4. 只在取模后共轭 A，再作共同大筛

一个分离原子的字符部分为 Aχ Bbarχ Rbarχ Sbarχ。
先逐 (ℓ,χ) 取模，再用
\[
 |A_\chi B_{\bar\chi}R_{\bar\chi}S_{\bar\chi}|
 =|B_{\bar\chi}|\,
            |\overline{A_\chi}R_{\bar\chi}S_{\bar\chi}|.  \tag{DP10}
\]
这里 overline(Aχ) 的系数也共轭。不能把这步写成原线性和的恒等
代换！右边第二因子是整数产品 a r s 的共同 barχ 列。
其长度 O(K)，K=A M₁M₂，能量≪K^(1+ε)，由有限整数 τ₃ 碰撞界；
b 列能量≪B。所有原 A/B 单位掩码均在系数内。

[primitive 乘法大筛 Theorem 16.2](https://kskedlaya.org/ant/chap-largesieve2.html)
和一次带 ℓ/φ(ℓ) 的 Cauchy 给每块（不含 DP9 预算）
\[
 \ll {UV\over jk\varphi(c)\Lambda^{3/2}}
             \sqrt{BK(B+\Lambda^2)(K+\Lambda^2)}\,T^\epsilon
             \prod_i(1+t_i)^\epsilon.                    \tag{DP11}
\]
基础尺度在固定 T 幂内；后两个因子显式容纳无穷尾中的 τ₃ 损失。
实际 K 的整数支持非空时 K≥固定正常数，不把 D_i 当作整数长度。

设 K₀=A D₁D₂，g(t)=max(√t,t)。由于
\[
 {\sqrt{K(K+\Lambda^2)}\over\sqrt{K_0(K_0+\Lambda^2)}}
 \le g(t_1)g(t_2),\qquad K=t_1t_2K_0,
\]
对任意 D>0，dyadic 求和
\[
 \sum_{M\ge1/2\ {\rm dyadic}}
       (1+M/D)^{-8+\epsilon}g(M/D)\ll_\epsilon1
                                                               \tag{DP12}
\]
一致成立（取内部 ε≤1 即可）：M/D<1 时靠平方根几何级数，
>1 时靠至少负6阶。故所有双对偶尾绝对可加，D_i<1 也不增加 +1。
这证明了重新分离/大筛与无限求和的合法性，而非形式截断。

## DP5. 聚合与真实区域

由 DP11–DP12，固定 f,c,j,k 的费用≪T^ε/φ(c) 乘
\[
 \sqrt{AB\Lambda(B+\Lambda^2)(A+UV/(jk))}.                \tag{DP13}
\]
此处恒等化简使用 K₀=AΛ²jk/(UV)；从未要求 Λ²≤A,B。
放大 UV/(jk)≤UV，再求全部 j,k|c，费用至多 τ(c)²。
各 Λ 层的 c≈Q/Λ 费用为
Σ τ(c)²/φ(c)≪T^ε，见 PL6。不能重加 Q/Λ 个数。
四项完整展开后分别是
\[
 AB\sqrt\Lambda,\quad B\sqrt{AUV\Lambda},\quad
 A\sqrt B\,\Lambda^{3/2},\quad
 \sqrt{ABUV}\,\Lambda^{3/2}.
\]
求全部 f 与所有 Λ≤2Q，f 幂依次为 −2、−3/2、−3/2、−1；
最后的 harmonic log 保留在 T^ε 中。恢复唯一物理外权，得到
\[
 \boxed{|C_{\rm sm}|\ll
 {\mathcal A^{\rm sm}_{30}T^{1+\epsilon}\over q_0RS}
 \{ER\sqrt Q+R\sqrt{HL/E}\sqrt Q
          +E\sqrt R\,Q^{3/2}+\sqrt{RHL/E}\,Q^{3/2}\}.}   \tag{DP14}
\]

固定 q₀=1，R=S≈T³、H=L≈T^(5/2)、E≈T^η、Q≈T^(3−η)。
四个指数准确为
\[
 (\eta-1)/2,\qquad 2-\eta,\qquad
 1-\eta/2,\qquad 7/2-2\eta.                              \tag{DP15}
\]
故在 5/4≤η≤2 全部≤1。例如 η=13/10 的最大值为9/10，
而单包 principal 的现有绝对界仍为3−η=17/10。
非空性沿同一原支持构造：e≈Y¹³、q≈Y¹⁷ 为互异素数，
R=S=eq、N=8S、T=(8S)^(1/3)≈Y¹⁰、H=L=S/√T，
u=v=ceil(H/e)≈Y¹²<q，n 为 (S,2S) 中素数。选择相邻光滑
dyadic 包保留该整数，连续原 AFE 支持同 FP3 构造满足。
不声称任意给定 W/F 的核积分非零。

一个容易误算的替代分组：若 A 单列、B 与双对偶标签成产品，
会出现 R√E Q^(3/2)，其物理指数是5/2−η，不是2−η；
它自身不能给5/4。这正是 DP10 只在估计中共轭重分组的必要性。

全局 principal/AFE 重组由上游独立负责；本篇不赋予单个包相同界，
也不再次扣除全局已登记的主项。其他 canonical 分配、q₀ 外和、
非内部包、全部未估计补集与尾必须继续支付，14/17 和 2/3 均未证明。
此结论不用 Möbius 专属消去，不新增 Lean 外壳；有限测试不替代解析证明。

English: exact smooth re-packetization of the original sum permits two
primitive-character Poisson transforms. Uniform dual-tail control and a
modulus-only conjugation regrouping give a centered smooth-packet bound
at E≥T^(5/4). This does not smooth a pre-existing hard packet for free,
nor prove the principal, the global residual estimate, or zero exclusion.
