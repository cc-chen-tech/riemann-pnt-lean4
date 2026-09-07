# Canonical 中心化区域：支付交叉单位条件及全部 gcd 分配

白话结论：只用已冻结的 PV 与共同列大筛，较大的完整 gcd 可以
补偿较小的共同重叠。下面把 FP3 的中心化估计扩展到真正的
a/b/e canonical 分配，并给出一个两参数覆盖区域。例如
e≈T^(13/10)、abe≈T^(3/2)、a,b≈T^(1/10) 时，中心化线性和
为 O(A_J T^(79/80+ε))。这不是 a=b=1 的 FP3，也不依赖新的
双 Poisson 候选。principal、其他参数及外层补集仍单列。

## CP0. 固定来源和对象

原定义为 MWKF-PHYS-v1，定义源
49cfacd70c60372757280177c7b63fd4f7760817。唯一原式映射采用
[CA1–CA6，冻结 a24e1dca](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/a24e1dca631dcaab04fc023d641ae3463cacff77/docs/research/2026-08-31-physical-canonical-gcd-adapter.md)。
解析输入固定为完成 smooth 范围修订的
f42bd65f071e01d1913aa3516ffee0e608104158 的
[PL1–PL9](2026-08-31-physical-centered-pv-large-sieve.md) 和其
[CS2–CS11](2026-08-31-physical-centered-conductor-split.md)。
修订后的 CS0 与本篇均从 FP1 重新插入同一原 F 分割；不引用
旧一般硬壳的未付费共同列适配。原始 CP 推导提交为4cd1d0a1。
不引用未冻结的双标签 Poisson，也不使用旧二次 resonant projector。

固定平方自由 q₀，在原光滑内部箱 HL≲RS/T 上工作。要求整个
n、s 支持位于 q₀n,q₀s≤N/2，而非另插一个联合硬截断。
原核、taper、连续积分支持都保留；基础尺度在固定 T 幂内。
本篇显式使用从完整 FP1 插入重叠光滑单位分解得到的新包：
原 F 支撑在 [1/2,2]，满足 Σ_H F(|h|/H)=1（h≠0），δ 同理。
令 Ψ=Ψ_raw F(|α|)F(|β|)，其中 Ψ_raw 包含 FP2 缩放后的全部
原 r/s 权及连续积分核。定义 A_J 为这个光滑 Ψ 的原半范数，
J≥6。**不再附加旧 H≤|h|≤2H、L≤|δ|≤2L 硬指示函数。**
每个整数标签只遇到有限个包；全局无限尾不因此被无条件换序。
此重分包只用原定义源 (3.1) 和 FP1，不依赖新的 Poisson 估计。
不能声称此包等于旧 CS7 单个硬包：e=fx 后硬 h 壳会成为
x 与 u 的联合硬边缘，不能由一变量 BV 费用免费支付。
下文重用 PL 的共同列论证，而非把其旧包定理不加说明地套入。

用 a₀、b₀ 避免与容斥后的商混淆。唯一原式坐标为
\[
 s=a_0b_0eq,\quad r=n,\quad h=a_0eu,\quad\delta=b_0ev .
                                                               \tag{CP1}
\]
a₀,b₀,e,q 为正平方自由且两两互素；uv≠0，且
\[
 (a_0,v)=(b_0,u)=(uv,q)=1,\qquad
 (n,q_0a_0b_0eq)=(q_0,a_0b_0eq)=1 .
                                                               \tag{CP2}
\]
这是 (s,h,δ)=e、(s,hδ)=a₀b₀e 的精确 canonical 子域。
限制 a₀∈[A₀,2A₀)、b₀∈[B₀,2B₀)、e∈[E,2E)、q∈[Q,2Q)，
令 M=A₀B₀、D=ME，非空时 DQ≈S。整数1与正负标签都包括。
实际权记为
\[
 W=p_N(q_0n)p_N(q_0a_0b_0eq)
       \Psi(n/R,a_0b_0eq/S,b_0ev/L,a_0eu/H).
\]
同一个原线性和内定义
\[
 \begin{split}
 \mathcal C&={2T\over q_0RS}\sum
 \mu(a_0)\mu(b_0)\mu(e)\mu(q)\mu(n)W
 \{e_q(-euv\bar n)-\mu(q)/\varphi(q)\},\\
 \mathcal P&={2T\over q_0RS}\sum
 {\mu(a_0)\mu(b_0)\mu(e)\mu(n)\over\varphi(q)}W,\qquad
 \mathcal O=\mathcal C+\mathcal P .
 \end{split}                                                   \tag{CP3}
\]
没有重复 AFE 的2。q=1 的 C 为0，但其 P 不删除。
密度确为原 c_s(hδ)/φ(s)，只在所有上述单位条件下使用。

## CP1. 全互素容斥与五变量共同系数

固定 a₀,b₀，在取绝对值之前展开 (e,n)=1，置 e=fx,n=fy。
逐项
\[
 \mu(f)\mu(fx)\mu(fy)
 =\mu(f)\mu(x)\mu(y)1_{(xy,f)=1},\qquad
 e_q(-f xuv\,\overline{fy})=e_q(-xuv\bar y).
                                                               \tag{CP4}
\]
保留 (fxy,q₀a₀b₀q)=1、(xy,f)=1；不重新加 (x,y)=1。
令 X=E/f、Y=R/f、U=H/(a₀E)、V=L/(b₀E)。全部
f≤2min(E,R) 都在；非空时 X,Y,U,V≥固定正常数，否则行为空。
具体使用的紧盒边界由原 Ψ 和标签壳确定。

在 y/Y,x/X,q/Q,u/U,v/V 五变量上，实际四坐标为
\[
 y/Y,\quad {a_0b_0EQ\over S}(x/X)(q/Q),\quad
 (x/X)(v/V),\quad (x/X)(u/U).
                                                               \tag{CP5}
\]
系数 a₀b₀EQ/S 一致有界，没有 a₀、b₀ 或 f 的导数损失。
PL2 的加权 Fourier ℓ¹ 预算仍由 A_J 控制：先在联合支持的投影
外乘等于1的固定光滑 cutoff，再作五维 Fourier 分离；H^s、
s>9/2 支付两个标签的 BV 权，J≥6。原 taper 在内部光滑，
x、y 的一变量整数壳留在对应列中，不切割原连续积分支持。
因 e∈[E,2E)，新标签投影满足 |u/U|、|v/V|∈[1/4,2]，
非空时 U,V≥1/2；原分割 F 内的 x 依赖保留在联合光滑权中。

再写 q=cℓ，ℓ>1 为 primitive conductor，c、ℓ 平方自由互素。
精确字符系数为
\[
 {\mu(a_0)\mu(b_0)\mu(f)\over\varphi(c)}
 {\mu(\ell)\beta_{c\ell}\over\varphi(\ell)}
 \bar\chi(c)\tau_\ell(\bar\chi)\chi(-1)
                 X_\chi U_\chi V_\chi Y_{\bar\chi}.           \tag{CP6}
\]
求和还限制 (cℓ,fq₀a₀b₀)=1。归一化后 |β|≤1，
它不含已经在 Gauss 融合中明确处理的 μ(q)。两共同列保留
(x,fq₀a₀b₀c)=(y,fq₀a₀b₀c)=1，系数分别为 μ(x)、μ(y)
乘真实一变量权；ℓ-unit 全由 χ 的零延拓提供。
两标签分别保留 (u,b₀c)=1、(v,a₀c)=1。
固定 a₀,b₀,f,c 后所有这些系数对变化的 ℓ 共同；不要求跨外层共同。

## CP2. 新交叉单位条件的实际费用

低导子端对两个标签分别作 PV。现在必须使用
\[
 1_{(u,b_0c)=1}=\sum_{j\mid b_0c,\ j\mid u}\mu(j),\qquad
 1_{(v,a_0c)=1}=\sum_{k\mid a_0c,\ k\mid v}\mu(k).
                                                               \tag{CP7}
\]
每个 j,k 与 ℓ 互素，χ(j)、χ(k) 保留。允许 j,k 有共同素因子，
不能只对 c 容斥，更不能向 dual 标签添加额外单位条件。
Abel–PV 的费用为
τ(b₀c)τ(a₀c) ℓ log²(2ℓ) 乘两个 BV 范数。
所以 PL4–PL8 的证明适用，只有显式 divisor 预算增加。
例如 (a₀b₀,c)=1 时
τ(b₀c)τ(a₀c)=τ(a₀)τ(b₀)τ(c)²。固定幂尺度下为 T^ε，
不是免费丢弃 a₀、b₀ 的行数。

高导子端把 xuv 合为共同乘积列，长度 O(XUV)，整数三因子
碰撞能量 ≪(1+XUV)^ε XUV；非空时 XUV≥固定正常数。
新增 (b₀,u)、(a₀,v) 掩码只删去表示，不增加其绝对能量界。
y 列能量 ≪Y。沿 CS9–CS11 对所有 c、f 求和；不假设
Q²≤X,Y 或 XUV。PV 和大筛的输入分别是
[经典 PV (1.1)](https://arxiv.org/html/math/0503113v1)、
[primitive 乘法大筛 Theorem 16.2](https://kskedlaya.org/ant/chap-largesieve2.html)。

故对固定 a₀,b₀，记 K₀=HL/(a₀b₀E)，高导子部分（不含外权）
由
\[
 RK_0Z^{-1/2}+\sqrt Q(R\sqrt {K_0}+K_0\sqrt R)
                    +Q^{3/2}\sqrt{RK_0}                     \tag{CP8}
\]
控制。低导子部分由
\[
 ER\sqrt Z+(R\sqrt E+E\sqrt R)Z^{3/2}
                          +\sqrt{ER}Z^{5/2}                 \tag{CP9}
\]
控制。两式统一乘 A_J T^ε，1≤Z≤Q。f 的最慢项为 f^-1，
其 log(2min(E,R)) 计入 T^ε，其余 f^-2、f^-3/2 可和。
对每个 c 分别使用共同列大筛，再付其费用，未重复使用抵消。

## CP3. 全部 a₀、b₀ 的费用：不能使用单行预算

半开壳上
\[
 \sum_{a_0,b_0}(a_0b_0)^{-1}\ll1,\quad
 \sum_{a_0,b_0}(a_0b_0)^{-1/2}\ll\sqrt M,\quad
 \sum_{a_0,b_0}1\ll M .
                                                               \tag{CP10}
\]
整数1无例外。应用于 CP8–CP9 得完整八项
\[
 \begin{split}
 |\mathcal C|\ll_\epsilon{\mathcal A_J T^{1+\epsilon}\over q_0RS}
 \bigg\{&
 {RHL\over E\sqrt Z}
 +R\sqrt{MQHL/E}
 +{HL\over E}\sqrt{QR}
 +\sqrt{MQ^3RHL/E}\\
 &+MER\sqrt Z
 +MR\sqrt E Z^{3/2}
 +ME\sqrt R Z^{3/2}
 +M\sqrt{ER}Z^{5/2}\bigg\}.
 \end{split}                                                   \tag{CP11}
\]
完整 f、c、a₀、b₀、e、q 费用都在。最前一项中 M 被标签长度的
1/(a₀b₀) 抵消；低端的 M 没有抵消。此式保留双 Möbius 到共同列
步骤，但并不使用 Möbius 符号专属估计。

## CP4. 两参数真实覆盖，不是单个 e 阈值

取固定 q₀=1、R=S≈T³、H=L≈T^(5/2)，E≈T^η、D≈T^δ，
M≈T^(δ−η)、Q≈T^(3−δ)、Z≈T^z。要求所有原支持非空，特别是
0≤η≤δ≤3，0≤z≤3−δ。CP11 的八项物理指数准确为
\[
 \begin{array}{c|c}
 \text{高端四项}&
 3-\eta-z/2,\quad 2-\eta,\quad 3-\eta-\delta/2,\quad
                         7/2-\eta-\delta\\
 \text{低端四项}&
 \delta-2+z/2,\quad \delta-2-\eta/2+3z/2,\quad
 \delta-7/2+3z/2,\quad \delta-7/2-\eta/2+5z/2 .
 \end{array}                                                   \tag{CP12}
\]
所有八项≤1，加原非空条件，给一个明确充分覆盖多面体。
δ=η 才退回 FP3；不能在一般分配中仍写 Q=T^(3−η)。
一个便于描述的新增子区域为
\[
 {14\over11}\le\eta\le{4\over3},\qquad
 4-2\eta\le\delta\le{7\eta-6\over2},\qquad z=4-2\eta.
                                                               \tag{CP13}
\]
区间非空恰需 η≥14/11。逐项代入 CP12 验证所有指数≤1；
上界 δ≤(7η−6)/2≤2η−1 保证 z≤3−δ。
这不是所有 canonical 分配的统一 E≥T^(14/11) 定理。

例如 η=13/10、δ=3/2、z=57/40，八项依次为
\[
 {79\over80},\ {7\over10},\ {19\over20},\ {7\over10},
 {17\over80},\ {79\over80},\ {11\over80},\ {73\over80}.
                                                               \tag{CP14}
\]
最大值79/80，低于目标1。该点旧 CA13 加同域 principal 上界
只给中心化预算 T^(17/10+ε)，故相对该既有上界改善57/80。
此比较允许把新光滑包限制到常数个相邻旧硬壳后应用 CA13，
尺度只变固定常数；不是将旧硬壳在五变量分离中强行平滑化。
这不是原和大小的下界；原相位逐项直接计数更大，为
T^(6−δ−η)=T^(16/5)，不可把 principal 预算冒充直接计数。

另一个真实区域无需高端：选 Z=2Q 覆盖最高导子，只使用 CP9
和 CP10，不加不存在的高端。所得四个指数是
(δ−1)/2、5/2−(η+δ)/2、1−δ/2、4−η/2−3δ/2。
故
\[
 \delta\le3,\qquad \eta+\delta\ge3,\qquad \eta+3\delta\ge6
                                                               \tag{CP15}
\]
也是充分覆盖，仍须原支持。这不是把 CP11 中 Z=Q 后自动删高端。

## CP5. 非空族、principal 和未覆盖域

CP14 有无限原式支持族。由 Bertrand 在固定倍长区间取互异素数
a₀,b₀≈Y（可用相邻区间）、e≈Y¹³、q≈Y¹⁵。
令 R=S=a₀b₀eq、N=8S、T=(8S)^(1/3)≈Y¹⁰，
Kz=Mz=√T、H=L=S/√T；此时 U=H/(a₀E)、V=L/(b₀E)≈Y¹¹。
为直接满足原整数壳，取
\[
 u=b_0\left\lceil {H\over a_0 e b_0}\right\rceil+1,\qquad
 v=a_0\left\lceil {L\over b_0 e a_0}\right\rceil+1 .
                                                               \tag{CP16}
\]
有 (u,b₀)=(v,a₀)=1，u,v<q 且 H≤a₀eu≤2H、
L≤b₀ev≤2L 对充分大 Y 成立。另取素数 n∈(S,2S)，满足所有
n-unit 条件。x=3√T/4 时 (xn+δ)/s∈[√T/2,2√T]；
q₀n,q₀s≤N/4。有限 dyadic 取整只改常数。
这是原允许域非空，不声称任意指定 W/F 积分非零或正密度。

同域 principal 的现有绝对预算仍是
O(A_J T^ε HL/(q₀E)·T/S)=O(A_J T^(3−η+ε))
（平衡 q₀=1），CP14 点为17/10，不能由 CP11 自动支付。
若另有已独立证明的全局 principal/AFE 重组，只能全局使用一次；
本篇不依赖它，不把它授予每个子层。其余参数、其他物理尺度、
q₀ 外和、非内部包、尾和 signed mixed terms 全保留。
例如 η=δ=1 的真实小重叠方向并未被这些界控制。

有限守卫仅核验 CP4、CP7 的掩码/符号、规范化计数与指数，
不替代 PV、大筛和光滑预算证明。本篇无 Lean 新定理。
合并只认证以上局部覆盖；完整 coupled-kernel gate、
twisted moment、2/3 和14/17 零点目标均未闭合。

English summary: retain every canonical cross-unit mask and pay the entire
a/b allocation cost before converting the frozen PV/common-column estimate
into a two-parameter coverage polytope. A genuinely non-FP3 family with
shared overlap T^(13/10) has centered bound T^(79/80+epsilon).
The local principal and all remaining signed complements stay separate.
