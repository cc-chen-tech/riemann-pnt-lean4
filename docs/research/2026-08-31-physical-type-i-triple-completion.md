# 三变量共同完成：支付原短 Type-I，保留真正的 Type-II

白话结论：原 Type-I 有一个不带 Möbius 系数的商变量。把它与两个
光滑标签一起完成，可用乘积同余的除数计数，支付整个短 Type-I，
不必先拆成平方自由均值和误差。例如 E=D≈T^(6/5)、
U_c=V_c≈T^(1/10) 时，原归一化 Type-I 为 O(A₁₂T^(4/5+ε))。
**全部长 Type-II 仍未估计**；完整 centered C、principal 和 gate
都没有因此关闭。

## TTC0. 唯一原式与未改动的有符号补集

直接上游是 [TIQ0–TIQ5](2026-08-31-physical-type-i-squarefree-discrepancy.md)，
冻结 e7bb85731286168301f4dd0d795f71b512d6ae39。其物理来源为
[CP0–CP5](2026-08-31-physical-canonical-centered-pv.md)，冻结
9448c71da2cb69a0df0c9ebbe4fec6d9e200cd32；定义源仍固定
49cfacd70c60372757280177c7b63fd4f7760817。

沿用同一新 smooth 包及 canonical 坐标
\[
 r=n,\quad s=a_0b_0eq,\quad h=a_0eu,\quad \delta=b_0ev.
\tag{TTC1}
\]
q₀ 为固定平方自由整数；a₀,b₀,e,q 平方自由且两两互素，
(q₀,a₀b₀eq)=1。保留 (n,q₀a₀b₀eq)=(u,b₀)=(v,a₀)=(uv,q)=1。
原系数 μ(a₀)μ(b₀)μ(e)μ(q)μ(n) 及外权 2T/(q₀RS) 不变。
令 a₀∈[A₀,2A₀)、b₀∈[B₀,2B₀)、e∈[E,2E)、q∈[Q,2Q)，
M=A₀B₀、D=ME，非空支持上 DQ≈S。

Ψ 包含原 F_R(n)F_S(s) 和重新插入的光滑 F(|h|/H)F(|δ|/L)，
不附加旧硬 h/δ 壳或非冗余 n 硬壳。整个支持在 q₀n,q₀s≤N/2，
n/R∈[1/2,2] 是光滑支持。A_J 为该真实核的归一化半范数；
本文支付 J=12，不免费沿用仅六阶的预算。所有尺度、cutoff 及 q₀
均在固定 T 幂内；内部平衡例有各阶 A_J≪_(J,F,W)1。

先扩展 n 到所有正整数，利用原 μ(n)=0 消去非平方自由 n；
再取正整数 U_c,V_c，要求 max(U_c,V_c)<R/2。逐 n 精确有
\[
 \mu(n)=-\sum_{bc\mid n,\ b\le U_c,\ c\le V_c}\mu(b)\mu(c)
       +\sum_{bc\mid n,\ b>U_c,\ c>V_c}\mu(b)\mu(c).
\tag{TTC2}
\]
故 C=I+II，符号和全部权保留。n≤max(U_c,V_c) 时须恢复
μ(n)(1_(n≤U_c)+1_(n≤V_c)) 的有限边界；本篇显示的范围排除了它。
无符号商不能附加平方自由限制，也不能假定 (b,c)=1。

## TTC1. 有限三变量 Fourier：零的是三个坐标面

对平方自由 q>1、(α,q)=1 定义
\[
 K_{q,\alpha}(z,x,y)=1_{(zxy,q)=1}
   \{e_q(-\alpha xy\bar z)-\mu(q)/\varphi(q)\},
\quad
 \mathcal H_q(k,\rho,\sigma)=
 \sum_{z,x,y\bmod q}K_{q,\alpha}(z,x,y)e_q(kz+\rho x+\sigma y).
\tag{TTC3}
\]
固定两个单位变量，对第三个求和，倒数和单位乘法都是置换，
原指数和为 μ(q)。所以 k=0、ρ=0 或 σ=0 时，H_q 精确为零。
这是三个完整坐标面，不只是三条坐标轴；不删除其他非单位频率。
q=1 的原 centered 核直接为零，principal 不随之删除。

令 c_p(v)=p−1（p|v），否则为−1。素数 p 的 raw 与 principal
三变量变换分别为
\[
 R_p=p\,c_p(k+\alpha^{-1}\rho\sigma)1_{p\nmid\rho}
          -c_p(k)c_p(\sigma),\qquad
 P_p=-{c_p(k)c_p(\rho)c_p(\sigma)\over p-1}.
\tag{TTC4}
\]
证明：先对 x∈U_p 求和，得到 p1_(ρ=αy/z)−1；ρ 非单位时第一项
为空，单位时 y=ρα⁻¹z，剩余 z 和就是显示的 Ramanujan 和。
该公式包括任意零或非单位 dual 坐标。

CRT 将 k,ρ,σ,α 同乘 inverse(q/p) mod p；
αk+ρσ 的零性只乘一个非零平方因子，因此 TTC4 的取值不变。
原 centered 核是「raw 乘积减 principal 乘积」，不是各 p 的
centered 核乘积。准确为
\[
 \mathcal H_q(k,\rho,\sigma)=\prod_{p\mid q}R_p-\prod_{p\mid q}P_p.
\tag{TTC5}
\]
逐 p 检查 δ_*=αk+ρσ 的零性与三坐标是否为零，得到
|R_p|≤(p+1)(p,δ_*)、|P_p|≤p(p,δ_*)，因而
\[
 |\mathcal H_q(k,\rho,\sigma)|
       \le(\tau(q)+1)q(q,\alpha k+\rho\sigma).
\tag{TTC6}
\]
例如 q=6、α=1、k=ρ=σ=2 时 H_q=−9/2，不能按本原频率删掉。
这里没有使用 Weil 或谱大筛，也没有把 gcd 因子当作常数。

## TTC2. 所有乘积同余及无限频率的可和预算

固定非零 k，L₁,L₂≥1。展开 gcd 为 Σ_(d|q,d|αk+ρσ)φ(d)。
对每个 d，非零乘积 ρσ 落在一条 mod d 的余类；每个非零整数
乘积至多有 2τ(|ρσ|) 种有序带符号因子表示。于是有限命题为
\[
 \begin{split}
 &\sum_{0<|\rho|\le L_1,\ 0<|\sigma|\le L_2}
               (q,\alpha k+\rho\sigma)\\
 &\quad\le4\max_{1\le j\le L_1L_2}\tau(j)
       \sum_{d\mid q}\varphi(d)
                \{\lfloor L_1L_2/d\rfloor+1\}\\
 &\quad\ll_\nu (L_1L_2)^\nu\{L_1L_2\tau(q)+q\}.
 \end{split}
\tag{TTC7}
\]
Σ_(d|q)φ(d)=q。这里明确支付余类计数的 +1；若允许 ρσ=0，
除数计数就失效，因此 TTC3 的坐标面消失是实质结构。

设 W(z,x,y)=w(z/Z,x/X,y/Y)，w 在固定紧盒上十二阶光滑并以零
延拓，记 B₁₂=max_(|j|≤12)||∂^j w||∞。不要求 w 分离。
令 hatW 为负号 Fourier 变换，则
\[
 |\widehat W(k/q,\rho/q,\sigma/q)|
 \ll B_{12}ZXY
 (1+|k|Z/q)^{-4}(1+|\rho|X/q)^{-4}(1+|\sigma|Y/q)^{-4}.
\tag{TTC8}
\]
每一轴最多四阶，混合总阶最多十二；原实际核也按此收费。
完整 Poisson 及 TTC3 精确给
\[
 \sum_{z,x,y\in\mathbb Z}K_{q,\alpha}(z,x,y)W(z,x,y)
 ={1\over q^3}\sum_{k\rho\sigma\ne0}
       \mathcal H_q(k,\rho,\sigma)\widehat W(k/q,\rho/q,\sigma/q).
\tag{TTC9}
\]
对固定 q，TTC8 已使其绝对收敛，故没有条件性换序。

下面令 q,Z,X,Y 及其非零倒数为固定 T 幂以内。把三个非零频率
分别放到从1开始的 dyadic 环；TTC7 后，对 k 环还须付其长度。
对任何 x>0，有
\[
 \sum_{j\ge0}{2^j\over(1+2^j/x)^4}
       \ll x\min(1,x^3).
\tag{TTC10}
\]
ρ、σ 的乘积项使用同样的一阶和；TTC7 的 +q 项使用零阶和。
无限环上必须用 τ(ρσ)≪_ν|ρσ|^ν，不能写成统一的 T^ε。
取 ν 足够小：每轴多出的 2^(jν) 由四阶衰减吸收；自然尺度的
ν 次幂再计入 T^ε。零阶和至多对数费用，尺度<1时反而有四次衰减。
因此，记 K=q/Z、L₁=q/X、L₂=q/Y，TTC9 的上界至多
\[
 B_{12}T^\epsilon{ZXY\over q^2}
 K\min(1,K^3)\{L_1L_2+q\}.
\]
严格化简为
\[
 \boxed{\left|\sum K_{q,\alpha}W\right|
 \ll_\epsilon B_{12}T^\epsilon(q+XY)\min\{1,(q/Z)^3\}.}
\tag{TTC11}
\]
特别地可舍弃最后的 min。此式对 Z、X、Y 小于1也有效；
没有把缺失的零频补成整数 +1。

另给有限截断的显式尾。只保留 |k|≤K₁、|ρ|≤K₂、|σ|≤K₃，
K_i≥1；TTC6 的粗界 (τ(q)+1)q² 与 TTC8 的积分尾给遗漏量
\[
 \ll B_{12}(\tau(q)+1)q^2
 \{(1+K_1Z/q)^{-3}+(1+K_2X/q)^{-3}+(1+K_3Y/q)^{-3}\}.
\tag{TTC12}
\]
有限外层后仍可逐项求和。主界 TTC11 则已经求完全部无限频率，
没有依赖“只存在对数多个频率”的假设。

## TTC3. 直接接回原 μ(n) 的整个短 Type-I

固定 a₀,b₀,e,q,b,c，记 A=q₀a₀b₀、B=bc、n=Bm。
原条件为 (B,Aeq)=1、(m,Aeq)=(u,b₀)=(v,a₀)=(uv,q)=1。
在取绝对值之前作三个完整单位容斥：
\[
 1_{(m,Ae)=1}=\sum_{d\mid Ae,\ d\mid m}\mu(d),\quad
 1_{(u,b_0)=1}=\sum_{j\mid b_0,\ j\mid u}\mu(j),\quad
 1_{(v,a_0)=1}=\sum_{\ell\mid a_0,\ \ell\mid v}\mu(\ell).
\tag{TTC13}
\]
置 m=dz、u=jx、v=ℓy。全部剩余单位条件就是 (zxy,q)=1，
并保留外面的 (B,Aeq)=1。d 可与 j 或 ℓ 共有素因子；
不误加 (z,d)、(z,e) 或 x/z 间的互素条件。
原相位精确成为 TTC3，参数
\[
 \alpha=e j\ell\,\overline{Bd}\pmod q,\qquad(\alpha,q)=1.
\tag{TTC14}
\]
变换后每项的完整符号为
−μ(a₀)μ(b₀)μ(e)μ(q)μ(b)μ(c)μ(d)μ(j)μ(ℓ)，没有额外 µ(z)。

真实权为
\[
 p_N(q_0Bd z)p_N(q_0a_0b_0eq)
 \Psi(Bd z/R,a_0b_0eq/S,b_0e\ell y/L,a_0ejx/H).
\tag{TTC15}
\]
选 Z=R/(Bd)、X=H/(a₀ej)、Y=L/(b₀eℓ)，归一化四坐标为
(z/Z,a₀b₀eq/S,y/Y,x/X)。全部在原固定紧支持内，
无 d,j,ℓ 的导数损失，B₁₂≪A₁₂。整包内部的 taper 同样光滑。
支撑外直接延拓；标签域为空时贡献为零。

由 TTC11，该固定单位容斥行至多
\[
 \mathcal A_{12}T^\epsilon
        \left\{q+{HL\over a_0b_0e^2j\ell}\right\}.
\tag{TTC16}
\]
∑_(d|Ae)1、∑_(j|b₀)1、∑_(ℓ|a₀)1 全部支付 divisor 费用；
它们是多项式参数的 T^ε，而不是丢弃大 d。第二项的 1/(jℓ)
也可保留后求和，不会增加费用。

## TTC4. 全外层上界、真实非空区域和仍然未付的项

短 b,c 行数是 U_cV_c；只在本步使用其系数模长≤1。
第一项恢复 a₀,b₀,e,q 全和，费用为 MEQ²。
第二项用 ∑e^-2≪E^-1、∑_(a₀,b₀)(a₀b₀)^-1≪1
及 q 壳行数≪Q，费用为 QHL/E。所有非空壳尺度≥1/2，
包含整数1的壳可取尺度1。还原唯一外权2T/(q₀RS)，得到
\[
 \boxed{|I|\ll_\epsilon
 {\mathcal A_{12}T^{1+\epsilon}U_cV_c\over q_0RS}
       \left\{MEQ^2+{QHL\over E}\right\}.}
\tag{TTC17}
\]
这是整个原 Type-I，不是它的固定 e、固定除数或固定频率子项。
无需 TIQ 的平方自由密度误差，也不把两个 saving 相乘。
特别是不能把原含 µ(n) 的 C 直接视为这个无符号商完成和。

在 q₀=1、R=S≈T³、HL≈T⁵、E=T^η、D=T^δ、
U_cV_c=T^β 的内部平衡区域，两个指数为
\[
                   1-\delta+\beta,\qquad3-\delta-\eta+\beta .
\tag{TTC18}
\]
因此 δ≥β 且 δ+η≥2+β 足以支付这一整个短 Type-I。
η=δ=6/5、β=1/5 给最大4/5；η=δ=1、β=0 给1。
这里 cutoff 真可增长：取 U_c=V_c=floor(T^(1/10))，大 T 时
max(U_c,V_c)<R/2。较小的 cutoff 会扩大 II，不能将其隐藏。

η=δ=6/5 的原支持有无限非空族，直接沿 TIQ 的 Bertrand 构造：
互异素数 e≈Y₀²、q≈Y₀³，R=S=eq、N=8S、T=(8S)^(1/3)，
H=L=S/√T、Kz=Mz=√T、a₀=b₀=q₀=1。
取 u=v=ceil(H/e)<q、素数n∈(S,2S)，原连续变量x₀=3√T/4。
所有单位条件、核心尺度及原积分支持成立，且 b=c=1 确在 Type-I。
这证明参数域非空，不断言任意选定光滑权的和非零。

余项仍是同一个 C=I+II；II 保留 TTC2 的正号、b>U_c,c>V_c、
原 n=bc m、全部 µ(b)µ(c)µ(e)µ(q)、原 hδ 相位及同一个 Ψ。
本篇只支付这个线性 I，不给其能量算子范数，也不删除原共同能量
EE*、EC*、CE*、CC* 中的交叉项。principal、其他尺度、外 q₀ 和、
物理尾及完整 gate 仍需各自原式估计。
旧 JQ 的另一坐标 Type-I 分解不是本篇输入，其节省不再累乘。

English: a three-coordinate completion of the unit-centered reciprocal
bilinear kernel has three vanishing coordinate planes. Its complete
Fourier coefficients are controlled by a single product congruence,
yielding a smooth O(q+XY) bound. This pays the original short Type-I
with all coprimality allocations and outer costs; signed Type-II remains open.
