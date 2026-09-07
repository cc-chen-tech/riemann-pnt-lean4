# 固定光滑标签包：双素数互反后的非主角色 hybrid 界

白话结论：保留两个标签完成后产生的连续振荡，先把模数从 q 换到 e，
再把 Mellin 频率和新角色一起平均，可以支付此前未单独控制的新非主角色。
在 E≈T^(6/5) 的真实双素数包，得到 C=P_rec+O(A₃₀T^(1+ε))。
新主角色 P_rec 仍只有 A₃₀T^(11/10+ε) 预算，不能删去；完整包并未付清。
相对于该剩余量原有11/10预算，这次非主部分省去1/10次幂。

本篇是原 μ(n) 输入的局部线性估计，不是 Type 恒等式扩展中的非平方自由
子和，也不使用特殊 Möbius 消去。不是完整 twisted moment 或零点定理。

## RH1. 冻结来源与唯一原物理对象

Git 父版本为 #540 的 1d089ce2db8644799e06bb6c878b51c5438d7ca3；
本篇不使用 FO 的因子重叠投影。原坐标和单位条件沿用
[HY1–HY2](2026-08-31-physical-type-ii-hyperbolic-incidence.md)
799e5224d386832ca2d2a166030b46a07fc20d52。
smooth 范围及联合核来源固定为 #514 的
[DP1–DP4、DP9–DP12](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/7cc9646c8b8a8589b920e24652c86bd063f4b1d7/docs/research/2026-08-31-physical-centered-character-poisson.md)。
它们从 FP1 完整 h,δ≠0 重插原 F 光滑单位分解，不能回溯赋给旧硬 H/L 包。
这里只取一个固定 AFE、H/L 内部包，不重组全 h、全 δ 或跨 AFE 尾。

固定 q₀=a₀=b₀=1，e,q 都为素数，e∈[E,2E)、q∈[Q,2Q)，2E<Q，
r=n、s=eq、h=eu、δ=ev，R≈S≈EQ。原 (n,eq)=(uv,q)=1，u,v≠0。
整包支持保证 n,eq≤N/2；**不另插联合硬截断 1_(eq≤N/2)**。
记 p_N(x)=1−log x/log N。原 centered 线性和为
\[
 C={2T\over RS}\sum_{e,q\ \mathrm{prime}\atop E\le e<2E,\ Q\le q<2Q}
 \mu(e)\mu(q)\sum_{n:(n,eq)=1}\mu(n)p_N(n)p_N(eq)
 \sum_{u,v\ne0}\Psi_{\rm sm}(n/R,eq/S,ev/L,eu/H)
 1_{(uv,q)=1}\{e_q(-euv\bar n)+1/(q-1)\}.             \tag{RH1}
\]
所有独立壳、原 Ψ 支持和符号都在。设 A₃₀ 为上述 smooth 核连同 taper
在归一化坐标上的总阶≤30导数预算；本篇始终保留它，不自动视作 T^ε。
e/q 素数条件属于算术列，不放进光滑导数。可更换共同 μ(n) 为任意有界
共同复系数，估计成本不变；没有把 (n,e) 塞进独立于 e 的共同列。

本篇结论的参数范围是固定比较常数下
\[
 R\asymp S\asymp T^3,\quad H\asymp L\asymp T^{5/2},\quad
 E\asymp T^\eta,\quad Q\asymp T^{3-\eta},\quad1\le\eta\le5/4.
                                                               \tag{RH2}
\]
记 U=H/E、V=L/E、D₁=Q/U、D₂=Q/V，
\[
 K_0=QD_1D_2={Q^3E^2\over HL},\qquad
 \nu={RD_1D_2\over EQ}={REQ\over HL}.                  \tag{RH3}
\]
D₁≈D₂≈√T、ν≈T，故 D_i/E,D_i/Q→0。有限小 T 可增大常数处理。

## RH2. 精确双完成：q⁻² 后是 UV/q

对素数 q 和单位 λ，取正号有限 DFT，有逐有限和恒等式
\[
 \sum_{u,v\bmod q}1_{(uv,q)=1}
 \{e_q(-\lambda uv)+1/(q-1)\}e_q(\rho u+\sigma v)
 =q1_{(\rho\sigma,q)=1}
       \{e_q(\bar\lambda\rho\sigma)+1/(q-1)\}.        \tag{RH4}
\]
先对一个单位变量求和即得。ρ 或 σ 为0模 q 时整个系数精确为0。
连续 Fourier 取负号。将 λ=e/n 代入 RH4、使用 q⁻² Poisson，得到
\[
 C={2T\over RS}\sum_{e,q,n:(n,eq)=1}
   \mu(e)\mu(q)\mu(n){UV\over q}
   \sum_{\rho,\sigma\ne0\atop(\rho\sigma,q)=1}
     \Phi(n/R,e/E,q/Q,\rho/D_1,\sigma/D_2)
       \{e_q(n\rho\sigma\bar e)+1/(q-1)\}.            \tag{RH5}
\]
Φ 的定义包含两 taper 及实际 Ψ 的二维 Fourier 变换；q/Q 的有界缩放
保留在 Φ 中。这里 UV/q 不可替成 UV 或 UV/√q，物理外权仍只有2T/(RS)。
Φ 有 RH6 下述统一 Schwartz 预算，不是 delta；所有非零整数对偶均保留。

把 RH5 旧 +1/(q−1) 项记作 O_q。对固定 e,q,n，
\[
 {UV\over q(q-1)}\sum_{\rho,\sigma\ne0}|\Phi|
 \ll A_{30}{UV D_1D_2\over Q^2}\ll A_{30}.
\]
再数 e,q,n 共 O(EQR)=O(RS)，得到 |O_q|≪A₃₀T^(1+ε)。
这是该项直接支付，不借用全局 PT principal。

## RH3. 三种扩和差：两类非单位对偶和 n=qj

以下所有误差均在保留原联合 Φ 的条件下逐项定义。
先取 RH5 raw 相位项中 e|ρσ 的部分 B_e；仍保留原 q-unit 和 n-unit。
e 素且 ρσ≠0，J=6 的非零倍数尾满足
\[
 \sum_{e\mid\rho,\rho\ne0}(1+|\rho|/D_1)^{-6}
       \ll(D_1/e)^6,\qquad
 \sum_{\sigma\ne0}(1+|\sigma|/D_2)^{-6}\ll D_2.
\]
因此
\[
 |B_e|\ll A_{30}{T\over RS}REQ{UV\over Q}
       [(D_1/E)^6D_2+D_1(D_2/E)^6].                  \tag{RH6}
\]
RH2 下指数为13/2−7η≤−1/2。它不是零项，不能直接删。

余下 e-unit 对偶，先把 (n,q)=1 扩为全部 (n,e)=1，减回 B_n，即 n=qj。
q 为素数，故这是完整掩码差，不是截断容斥。n≤2R 时有 floor(2R/q)
个 j，没有额外 +1；保持 μ(qj) 原值，不误用 μ(q)μ(j)。故
\[
 |B_n|\ll A_{30}{T\over RS}EQ{R\over Q}{UV\over Q}D_1D_2
       \ll A_{30}T^{1+\epsilon}.                     \tag{RH7}
\]
此 B_n 仍带 (ρσ,q)=1。随后去掉 q-dual 掩码，减回 B_q：
它取所有 (n,e)=1、(ρσ,e)=1 且 q|ρσ。用 RH6 相同估计，但倍数尺度
分母 E 换为 Q；其指数为 −23/2+5η<0。保留这条误差后，q、ρ、σ
才可成为独立列，不能把耦合掩码隐藏在三列取模后共轭的步骤里。

记 F 为经过这三步扩和的 raw 主体，准确线性账本是
\[
 C=F+O_q+B_e-B_n-B_q,\qquad
 |O_q|+|B_e|+|B_n|+|B_q|\ll A_{30}T^{1+\epsilon}.      \tag{RH8}
\]
不在新主/非主角色分解之后改变掩码，也没有重复支付交叠部分。

## RH4. 互反后的新 principal 必须显式留下

点态 reciprocity 是
\[
 e_q(n\rho\sigma\bar e)
   =e_e(-n\rho\sigma\bar q)\,e(n\rho\sigma/(eq)).      \tag{RH9}
\]
后一个连续相位的自然参数 ν≈T，不是免费 A₃₀-smooth 因子。
对 (nqρσ,e)=1，利用所有非主角色均 primitive，
\[
 e_e(x)=-{1\over e-1}+{1\over e-1}
             \sum_{\chi\ne\chi_0\bmod e}\tau(\bar\chi)\chi(x).
                                                               \tag{RH10}
\]
据此 F=P_rec+N_rec，两个项都继承 RH8 扩和后的全部剩余 e-unit 条件、
同一 Φ、chirp、系数与唯一外权。P_rec 的精确定义为
\[
 -{2T\over RS}\sum_{e,q\ \mathrm{prime}}\sum_{n:(n,e)=1}
 {\mu(e)\mu(q)\mu(n)UV\over q(e-1)}
 \sum_{\rho,\sigma\ne0\atop(\rho\sigma,e)=1}
 \Phi(n/R,e/E,q/Q,\rho/D_1,\sigma/D_2)e(n\rho\sigma/(eq)).
                                                               \tag{RH11}
\]
P_rec 不含已在 RH3 支付的 q-dual 掩码。N_rec 是 RH10 全部非主角色项。
这是线性分账，不是能量正交投影；EE*、EC*、CE*、CC* 全部仍需保留。
本 principal 不是 PT 全局 Ramanujan 项，也不是全 h/δ 新模 principal。

## RH5. 原核共同分离和 Mellin 驻相预算

对正负 ρ、σ 分别作完整光滑 dyadic 单位分解，|ρ|≈J₁、|σ|≈J₂，
J_i≥1/2。令 λ_i=J_i/D_i、θ=λ₁λ₂、X=νθ、K=K₀θ=QJ₁J₂。
每个整数只有有限相邻 dyadic 权，低于最小整数支撑的块精确为空。
先双 Fourier，再对 n/R,e/E,q/Q,|ρ|/J₁,|σ|/J₂ 五个 log 坐标做
H³ 共同分离，原子系数 ℓ¹ 预算为
\[
 A_{30}(1+\lambda_1)^{-8}(1+\lambda_2)^{-8}.           \tag{RH12}
\]
说明导数账：两标签各11次分部积分，随后 log 参数总阶≤3；每次参数
微分产生的对偶幂在11−3≥8的衰减内支付。原总导数≤25<30。
五维 Fourier 系数的 ℓ¹ 由 H³ 和 3>5/2 给出。独立 e/q 壳和素数条件
不求导；整包 N/2 保证无联合硬边缘。归一化变量均离0且在固定紧集内。

在归一化乘积
z=(n/R)(|ρ|/J₁)(|σ|/J₂)/[(e/E)(q/Q)] 的固定紧范围上取 ψ₀≡1，
ψ₀∈C_c^∞((0,∞))。定义
\[
 M_X(t)=\int_0^\infty\psi_0(z)e(\pm Xz)z^{-it}{dz\over z},
 \quad e(\pm Xz)={1\over2\pi}\int_{\mathbb R}M_X(t)z^{it}dt
 \quad(z\in\operatorname{supp}\Phi).                 \tag{RH13}
\]
正负号由 ρσ 决定。写 z=e^w，二阶相位导数为 ±2πXe^w，故 X≥1 时
van der Corput 给 |M_X(t)|≪X⁻¹/²，统一于 |t|≤CX；|t|≥CX 时
一阶导数离0，任意多次 IBP 给 O_J(|t|⁻ᴶ)。X<1 时是统一 Schwartz。
因此中心时间段宽 O(1+X)，幅度 O((1+X)⁻¹/²)；外段
|t|≈2^j(1+X) 可用 (1+X)⁻¹/²2⁻⁶ʲ。驻点只在符号相符的 t 侧出现。
不能把 M_X 的 ℓ¹ 预算当 O(1)：它可为 O(√X)。以下在 hybrid 积分
之前使用逐 t 的 X⁻¹/²，并明确支付时间段长度。

## RH6. 只在模长后共轭，再做一次 hybrid 大筛

对每个共同原子，四个角色多项式形如
N_χ(t) Q_barχ(−t) R_χ(t) S_χ(t)。e⁻ⁱᵗ、χ(−1) 和 e 原子只在模数
标量中；q、ρ、σ 列已经没有相互依赖的 q-unit 掩码。
先取该乘积模长，再将 R、S 的值连同复系数取共轭。模长不变，
但这不是原复数线性值的替换！于是 q|ρσ| 可合成一个共同整数产品列，
长度 O(K)、系数大小≤τ₃，对偶符号通过固定 χ(−1) 标量处理。
N 列长度 O(R)。所有剩余 e-unit 掩码由角色零延拓精确实现。

无限对偶块须保留
\[
 \|a_N\|_2^2\ll RT^\epsilon,\qquad
 \|a_{q\rho\sigma}\|_2^2\ll KT^\epsilon
                \prod_i(1+\lambda_i)^\epsilon.        \tag{RH14}
\]
这来自整数 τ₃ 能量或除数界；K 并非对所有对偶块都为固定 T 幂，
所以不能把第二式直接写成 KT^ε。以下取辅助 ε<1，最后重命名 ε。

采用 [Conrey–Iwaniec–Soundararajan, (1.6)](https://arxiv.org/pdf/1105.1176)
的普通 hybrid primitive 大筛：
\[
 \sum_{m\le 2E}\sum_{\chi\bmod m}^{*}\int_{-W}^W
 |\sum_{j\le L}a_j\chi(j)j^{it}|^2dt
 \ll(E^2W+L)\sum_j|a_j|^2,\qquad W\ge1.              \tag{RH15}
\]
只在正量中扩至所有 m≤2E；不调用该文 asymptotic 或特殊 mollifier 定理。
|τ(barχ)|/(e−1)≪E⁻¹/²。仅对共同 (e,χ,t) 做一次 Cauchy，中心时间段
W≈1+X 给出每块（未乘2T/(RS)和 RH12 衰减）的界
\[
 {UV\over Q}{A_{30}\over\sqrt{E(1+X)}}
 \sqrt{RK(R+E^2(1+X))(K+E^2(1+X))}\,T^\epsilon
                  \prod_i(1+\lambda_i)^\epsilon.     \tag{RH16}
\]
不可再乘 e 个数或角色个数。外时间段 W≈2^j(1+X) 使根号成本至多
增长2^j，与2⁻⁶ʲ收敛；两个 t 符号都在。这处理全部 Mellin 尾。

在自然对偶尺度展开 RH16 根号得到四项
\[
 {UV\over Q}A_{30}T^\epsilon\left\{
 {RK_0\over\sqrt{E\nu}}+\sqrt E R\sqrt{K_0}
 +\sqrt E K_0\sqrt R+E^{3/2}\sqrt{RK_0\nu}\right\}.   \tag{RH17}
\]
短 X 也必须支付。去掉公共系数后 RH16 平方准确展开为
\[
 {R^2K^2\over E(1+X)}+ER^2K+ERK^2+E^3RK(1+X).
\]
代 K=K₀θ、X=νθ、ν≥1，其相对 RH17 四项平方和至多
2max(θ,θ²)。故一般块最多多付 O(√θ+θ)。与
∏(1+λ_i)^(−8+ε) 相乘，对每个 λ_i 的小/大 dyadic 方向均绝对可和。
该 majorant 保留无限除数增长，证明所有求和/积分交换及短对偶端点。

恢复原2T/(RS)，RH2 下四个指数依次为
\[
 (7/2-5\eta/2,\ 2-\eta,\ 5/2-3\eta/2,\ 1).         \tag{RH18}
\]
η≥1 时均≤1；η=6/5 时为 (1/2,4/5,7/10,1)。因此
\[
 |N_{\rm rec}|\ll_\epsilon A_{30}T^{1+\epsilon}.      \tag{RH19}
\]

## RH7. 留下的同一新 principal 与覆盖边界

对 RH11 固定 e，保留 (n,e)=(qρσ,e)=1；没有 q-dual 耦合掩码。
重复 Mellin 及模长后共轭，用普通 t 均值而非角色大筛。两列此时
允许依赖固定 e，不能声称其掩码对变化 e 共同。最后恢复1/(e−1)
并求 e，Σ_(E≤e<2E)1/(e−1)≪1，得到自然尺度未乘外权的预算
\[
 {UV\over Q}A_{30}\nu^{-1/2}
 \sqrt{RK_0(R+\nu)(K_0+\nu)}\,T^\epsilon.             \tag{RH20}
\]
采用长度均值 (W+L)Σ|a|²；短 X、无限对偶及时间尾按 RH16–RH17
同样保留1+X和增长因子后求和。RH2 下 RH20 的物理指数是7/2−2η，
η=6/5 时仍为11/10。它是上界预算，不是实际下界或不可能性结论。

综上得到已限定的原式分解
\[
 \boxed{C=P_{\rm rec}+O_\epsilon(A_{30}T^{1+\epsilon})}.
                                                               \tag{RH21}
\]
新控制的是此精确定义的新非主角色以及 RH8 误差，非空原 μ(n) 支撑
确实存在。用于比较的旧 DP 界必须重跑，不能从其全平方自由 signed 总和
直接删项：固定 e/n 容斥因子 f 时，A 列加入 1_(fa为素数)，仍对角色
模数共同；q 素数使 DP 的 c=1、ℓ=q。仅在取模/Cauchy 后的正量中
扩至所有 primitive 模数，原 DP 证明于是仍给此 C 的11/10界。
结合 RH20 对 P_rec 的11/10界及 RH8，三角不等式只给 N_rec 的11/10
预算；RH19 将此部分降到1，节省1/10。
整个 C 的11/10瓶颈仍在同一 P_rec 中；尚不支付新 principal、合数 e/q、
其他 canonical/q₀、跨 AFE 尾或共同能量交叉项，不与其他局部 saving 相乘。
本篇不证明 coupled-kernel gate、完整 twisted moment 或14/17。

## RH8. 无限非空族和可形式化有限命题

用 Bertrand 在倍长区间取互异素数 e≈Y⁶、q≈Y⁹，S=eq、R=S、
T=(8S)^(1/3)、N=8S、M_z=K_z=√T、H=L=S/√T，再取素数 n∈(S,2S)。
这给 η=6/5、n,s≤N/4，所有原单位条件成立。u=v=ceil(H/e)<q
且 h,δ∈[H,2H]；x=3√T/4 时 y=(nx+δ)/s∈[√T/2,2√T]。
独立壳可随实际变量作有限 dyadic 取整，比较常数不改变任何指数。
e>2 时新非主局部核模长≥1−1/(e−1)>0，故不是恒零投影。
这里只给整数及核支持非空，不声称任意给定平滑积分非零或正密度。

可直接形式化的有限命题是 RH4、RH9、RH10、RH8 的截断逐项分账、
模长后共轭恒等式及 RH16 平方的短 X 比较；脚本用有理 cyclotomic
表示检查，保留复权和 μ(n)。这些测试不代替 Poisson、驻相、hybrid
大筛或无限收敛证明。本篇不新增 Lean 公理或证明完成接口。
