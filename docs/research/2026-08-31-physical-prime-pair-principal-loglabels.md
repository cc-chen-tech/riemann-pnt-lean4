# 双素数固定光滑包：用无权对数标签支付同一新 principal

白话结论：#545 已支付互反后的非主角色，但把新的主角色留在原式里。
本篇先明确付清两个单位条件的扩和差，再利用主角色中两个没有 Möbius
权的对偶标签。它们的对数振荡把这个主角色的预算从 T^(11/10)
降到 T^(14/15)。与同一包的非主部分合回后，E≈T^(6/5) 的整个
双素数 centered 包为 O(A₃₀T^(1+ε))；不是主导项自动消失。

这是一个真实线性子族的新覆盖。其他模数、canonical/q₀、全局尾部、
显式主项及共同能量交叉项不由本篇支付；完整 twisted moment 仍未证明。

## LP1. 固定来源、同一物理对象与范围

唯一 Git 父版本为 #545 的 **56e0bbd1a426b86b1a58d237b9fa8f3d08feaf30**。
原式、smooth 支持和全部系数是
[RH1–RH3](2026-08-31-physical-prime-pair-reciprocal-hybrid.md)，
主角色严格是该文 RH11，非主界沿用 RH19，扩和账沿用 RH8。
其解析上游仍是 #514 冻结
[7cc9646c 的 DP1–DP4](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/7cc9646c8b8a8589b920e24652c86bd063f4b1d7/docs/research/2026-08-31-physical-centered-character-poisson.md)。
不能把本篇回溯赋给一般硬 H/L 包。

固定 q₀=a₀=b₀=1，e、q 均素数，E≤e<2E、Q≤q<2Q、2E<Q。
r=n、s=eq、h=eu、δ=ev，原式有 (n,eq)=(uv,q)=1。
在固定比较常数下取
\[
 R\asymp S\asymp EQ\asymp T^3,\quad H\asymp L\asymp T^{5/2},
 \quad E\asymp T^\eta,\quad Q\asymp T^{3-\eta},\quad
 1\le\eta\le5/4.                                      \tag{LP1}
\]
整包支持保证 n,eq≤N/2，不另加联合硬截断。唯一物理外权是2T/(RS)。
两 taper p_N(n)p_N(eq)、原 AFE 核和原 F 光滑标签都在 Φ 内；
A₃₀ 是 RH1 定义的实际归一化总阶≤30半范数，始终显式保留。
e/q 素数、μ(e)μ(q)μ(n) 不属于光滑导数。
记
\[
 U=H/E,\quad V=L/E,\quad D_1=Q/U,\quad D_2=Q/V,
 \quad\nu={RD_1D_2\over EQ}\asymp T,\quad D_i\asymp\sqrt T.
                                                               \tag{LP2}
\]
需要估计的同一个 principal 是
\[
 P=-{2T\over RS}\sum_{e,q\ \mathrm{prime}}\sum_{(n,e)=1}
 {\mu(e)\mu(q)\mu(n)UV\over q(e-1)}
 \sum_{\rho,\sigma\ne0\atop(\rho\sigma,e)=1}
 \Phi(n/R,e/E,q/Q,\rho/D_1,\sigma/D_2)e(n\rho\sigma/(eq)).
                                                               \tag{LP3}
\]
这里已经没有 q-dual 掩码：它在 RH8 单列并支付。P 不是 PT 全局
Ramanujan 项，也不是 full-h/full-δ 新模主角色；不得跨对象移账。

## LP2. 先付两个 e 掩码，交叠只减一次

令 P₀ 为 LP3 去掉两个 e-unit 条件的和，仍不插入任何零整数对偶。
Bₙ 为 P₀ 的 e|n 项，B_d 为 P₀ 的 (n,e)=1、e|ρσ 项；两者包含
P₀ 原来的负号及全部联合 Φ。逐项准确有
\[
                         P=P_0-B_n-B_d.               \tag{LP4}
\]
由于 e 是素数，n≤2R 的倍数数目是 floor(2R/e)，没有额外 +1。
μ(ej) 保持原值，不能换成 μ(e)μ(j)。用 UV D₁D₂=Q² 得
\[
 |B_n|\ll A_{30}{T\over RS}(EQ){R\over E}{UV\over QE}D_1D_2
       =A_{30}{TQ^2\over SE}
       \ll A_{30}T^{4-3\eta}.                        \tag{LP5}
\]
对于非零 e 倍数，D_i/E→0，六阶 Schwartz 衰减给
Σ_(e|ρ,ρ≠0)(1+|ρ|/D₁)^−6≪(D₁/E)^6，而另一个标签总量 O(D₂)。
两个标签对称相加，得到
\[
 |B_d|\ll A_{30}{T\over RS}(REQ){UV\over QE}
   [(D_1/E)^6D_2+D_1(D_2/E)^6]
 \ll A_{30}T^{13/2-8\eta}.                            \tag{LP6}
\]
有限小 T 以常数吸收。η≥1 时两个误差都在 T 预算内。完成这一步后，
P₀ 的 n、e、q、ρ、σ 列才没有相互耦合的算术掩码；不能提前把原带
(ρσ,e)=1 的标签当作无权整数和。

## LP3. 同一核的加权共同原子：H⁴，不是 H³

对正负非零 ρ、σ 插入完整 smooth dyadic 单位分解，|ρ|≈J₁、|σ|≈J₂，
J_i≥1/2；低于最小整数支持的块精确为空。设
\[
 \lambda_i=J_i/D_i,\quad\theta=\lambda_1\lambda_2,\quad
 X={RJ_1J_2\over EQ}=\nu\theta.                       \tag{LP7}
\]
由于 R/(EQ) 在固定紧区间内，X≈J₁J₂，J_i≪X；非空块 X 有固定
正下界。这一点用于处理短对偶，不能把一般独立的 X、J_i 免费如此约束。

把 QE/[q(e−1)] 的有界光滑因子放进联合幅度，再对五个 log 坐标
n/R,e/E,q/Q,|ρ|/J₁,|σ|/J₂ 做共同 Fourier 分离。各坐标用固定紧支撑
外 cutoff，在原支持上等于1；独立 e/q 硬壳、素数和 n 壳留在算术列。
无需对联合硬边缘作虚假的分离，因为 LP1 已排除该边缘。

两标签 Fourier 各12次分部积分，再做总阶≤4参数微分，需原导数
至多12+12+4=28≤30；对偶幂最多损失4阶，留下每标签8阶衰减。
因而五维 H⁴ 范数不超过 A₃₀∏(1+λ_i)^−8。原子频率记 ω∈ℤ⁵，
加权 Cauchy 给
\[
 \sum_\omega |c_\omega|
       (1+|\omega_\rho|)^{1/3}(1+|\omega_\sigma|)^{1/3}
 \ll A_{30}\prod_i(1+\lambda_i)^{-8},                 \tag{LP8}
\]
因为4>5/2+2/3。固定 Fourier 周期引入的常数缩放吸收在 ω 中。
普通 H³ 不能直接支付此2/3加权 ℓ¹；这里确实升级到 H⁴。
ρ、σ 两独立外 cutoff 的 BV 统一有界。n/e/q 频移只改共同系数的
单位复相位。A₃₀ 在全证明中只乘一次。

## LP4. 所需对数和界及频移接近零的情形

令 L_J(τ)=Σ_(j≥1)ψ(j/J)j^(iτ)，ψ 为上述固定光滑标签。
这是无 Möbius、无角色、无单位掩码、无除数权的整数和。
经典指数对 (1/6,2/3) 是无条件的；可参照
[指数对定义及 Proposition 5.10](https://teorth.github.io/expdb/blueprint/exponent-pairs-chapter.html)。
这里只需它的 log 相位特例，下面直接给出证明，不调用更强猜想。

对任意固定 c>0、|τ|≥cJ，有
\[
                   |L_J(\tau)|\ll_c |\tau|^{1/6}\sqrt J.        \tag{LP9}
\]
证明先在 [J,2J] 的任意子区间作无权和 S。cJ≤|τ|≤J^(3/2) 时，
二阶导数界给 |S|≪√|τ|+J/√|τ|≪_c |τ|^(1/6)√J。
J^(3/2)≤|τ|≤J³ 时取整数差分长度 H₀≈J|τ|^−1/3；差分相位
τlog(1+h/j) 的二阶导数有固定符号，大小≈|τ|h/J³。差分不等式
和二阶导数估计给
\[
 |S|^2\ll {J^2\over H_0}+|\tau|^{1/2}J^{1/2}H_0^{1/2}
                     +J^{5/2}|\tau|^{-1/2}H_0^{-1/2}
 \ll J|\tau|^{1/3}+J^2|\tau|^{-1/3}
 \ll J|\tau|^{1/3}.                                  \tag{LP10}
\]
H₀≈1 端点的 J² 项已满足目标；|τ|≥J³ 直接用平凡界 J。
整数取整、有限小 J 和有限倍长支持只改常数。负 τ 用共轭；分部求和
只支付 ψ 的统一 BV，于是 LP9 对完整 smooth 标签成立。

在 c₀X≤|t|≤C₀X 的时间段，若 |ω|≤c₀X/2，则 |t+ω|≈X≥cJ，
LP9 可用。若 |ω|>c₀X/2（包括 t+ω≈0），改用平凡 J，并注意
√J/X^(1/6)≪X^(1/3)≪(1+|ω|)^(1/3)。因此统一有
\[
 |L_J(t+\omega)|\ll X^{1/6}\sqrt J(1+|\omega|)^{1/3}.           \tag{LP11}
\]
两标签相乘，J₁J₂≈X，成本为 X^(5/6) 乘 LP8 已付的两频率权。
没有假定每个 Fourier 原子频移有界，也没有漏掉移到零频附近的原子。

## LP5. 原 chirp 的准确 Mellin 分解和共同 EQ 列

在归一化乘积 z=(n/R)(|ρ|/J₁)(|σ|/J₂)/[(e/E)(q/Q)] 的固定紧范围
取 ψ₀≡1，ψ₀∈C_c^∞((0,∞))。准确写
\[
 M_X(t)=\int_0^\infty\psi_0(z)e(\pm Xz)z^{-it}{dz\over z},
 \qquad e(\pm Xz)={1\over2\pi}\int_\mathbb R M_X(t)z^{it}dt.
                                                               \tag{LP12}
\]
符号是 ρσ 的符号。log z 相位导数是 ±2πXz−t。X 大时，驻相只
可能在匹配符号的 c₀X≤|t|≤C₀X；该段 |M_X|≪X^−1/2。
|t|<c₀X 时任意阶 IBP 给 O_J(X^−J)，|t|>C₀X 时给 O_J(|t|^−J)。
X 有界时 M_X 是统一 Schwartz。不能把这个 T 级 chirp 放进 A₃₀。

每个共同原子的五个多项式是
\[
       N(t)E(-t)Q(-t)L_{J_1}(t+\omega_\rho)L_{J_2}(t+\omega_\sigma).
                                                               \tag{LP13}
\]
归一化常数只贡献模长1。N 含原 μ(n)，E、Q 含原素数系数与 μ。
把 E(−t)Q(−t) 合成长度 O(S) 的同一个整数产品列，其系数是
Σ_(eq=m)α_eβ_q；平方能量≪S T^ε，τ₂界已足够，N 能量≪R。
特别是此后不能再乘 e 个数。两列允许满足上述能量界的共同复系数；
不需要 μ 消去，不能把任意 amplified 系数的范数费用免费删掉。
普通 Dirichlet 多项式时间均值和一次 Cauchy 给，W≥1 时
\[
 \int_{-W}^W|N(t)(EQ)(-t)|dt
 \ll_\epsilon T^\epsilon\sqrt{RS(R+W)(S+W)}.           \tag{LP14}
\]
三个 n/e/q 原子频移都已吸收在系数里，故常数对它们一致。
这里没有角色大筛，也没有在固定 e 之后再次对 e 求和。

LP8、LP11–LP14 在驻相段给每个对偶块的界（暂未乘2T/(RS)）
\[
 A_{30}T^\epsilon {UV\over QE}X^{1/3}
 \sqrt{RS(R+X)(S+X)}\prod_i(1+\lambda_i)^{-8}.         \tag{LP15}
\]
1/3=5/6−1/2，最后的 −1/2 是真实 Mellin 驻相幅度；不能漏掉
时间段长度，它已经包含在 LP14 的 R+W、S+W 中。

## LP6. 大小对偶、两个时间尾和换序依据

|t|<c₀X 用 M_X≪X^−J 和平凡标签积 O(J₁J₂)=O(X)，再用 LP14。
因此成本的 X 幂为 X^(1−J)，J≥3 时被 LP15 主项覆盖。
外时间环 W≈2^jX 用 M_X≪W^−J；LP14 相对 W=X 至多增长2^j，
所有环的成本不超过 X^(1−J)Σ_j2^(−j(J−1))。原子频移任意，
因为这些尾部只用标签的平凡界，不引入新的频移损失。

若 X 在固定有界范围，则 J_i≥1/2、X≈J₁J₂ 使两个 J_i 均有界。
非空整数对偶只涉及固定有限个块。统一 Schwartz M_X 和 LP14 给
物理预算 O(A₃₀T UV/(QE))，在 LP1 下为 A₃₀T^(3−2η)。
没有在趋零标签上虚增一个不可和的 +1。

自然尺度 X=ν 的 LP15 预算是
\[
 A_{30}T^\epsilon{UV\over QE}\nu^{1/3}
           \sqrt{RS(R+\nu)(S+\nu)}.                 \tag{LP16}
\]
一般 X=νθ 相对它的增长至多 θ^(1/3)max(1,θ)，因为
(R+νθ)(S+νθ)≤max(1,θ)²(R+ν)(S+ν)。因此与
∏(1+λ_i)^−8 相乘后，对每个 λ_i 的小、大 dyadic 方向都绝对可和。
这里的 log 和证明无 ε 损失；若引用带 ε 的一般指数对定义，只须额外
保留 max(1,θ)^(2ε)，取2ε<1，同一衰减仍足够，不能将无限 X 全当T幂。
产品 EQ 长度 O(S) 始终固定，因此其除数能量的 T^ε 没有隐藏无限变量。

所有恒等式先在有限频率/原子截断上作；LP8、LP15 和以上可和正
majorant 给绝对控制，允许 Fubini 及截断极限。这支付的是本固定包
内部的 Fourier/Mellin 全尾，不等于跨 AFE 或全 H/L 的外层求和。

## LP7. 主角色、完整同包及真实新覆盖

恢复原外权，R≈S≈T³、ν≈T，LP16 的物理指数为
1+(5−2η)−3+1/3=10/3−2η。结合 LP4–LP6、短 X 项，得到
\[
 |P|\ll_\epsilon A_{30}T^\epsilon
 [T^{10/3-2\eta}+T^{4-3\eta}+T^{13/2-8\eta}+T^{3-2\eta}]
 \ll_\epsilon A_{30}T^{10/3-2\eta+\epsilon}.          \tag{LP17}
\]
最后一步适用于1≤η≤5/4。η=6/5 给14/15，相对 RH20 的11/10
预算改善1/6；这不是实际下界的改善或 principal 恒等为零。

同一精确 C= P+N_rec+O_q+B_e−B_n(old)−B_q 中，RH19 和 RH8
其余部分均已在 A₃₀T 预算内。故本篇主结论是
\[
 \boxed{|C|\ll_\epsilon A_{30}T^{1+\epsilon}
                  \qquad(7/6\le\eta\le5/4).}        \tag{LP18}
\]
这里 Bₙ(old) 指 RH7 的 n=qj，与本篇 e|n 的 Bₙ 不同；不得混减。
η=6/5 时，整个原双素数 smooth 包由旧11/10预算降到1，净改善1/10，
不是把主/非主两项的 saving 相乘。η<7/6 本法尚不给完整包的T界。

RH8 的无限非空族可原样使用：Bertrand 取 e≈Y⁶、q≈Y⁹，S=R=eq，
T=(8S)^(1/3)、N=8S、M_z=K_z=√T、H=L=S/√T，素数 n∈(S,2S)，
u=v=ceil(H/e)<q。n,s≤N/4，原 h/δ 支持和正 y 的 AFE 支持非空。
有限 dyadic 取整只变比较常数；不声称任意给定积分非零或正密度。

本篇只支付 LP1 指定完整 centered 子族；合数 e/q、其他 canonical/q₀、
全局显式主项、跨 AFE 标签尾及 EE*、EC*、CE*、CC* 四项仍不得删除。
没有将原 μ(n) 估计自动迁移给 actual amplified 系数、非SF扩展子和
或全h/δ对象。本篇不证明 coupled-kernel gate、完整 twisted moment 或零点定理。

## LP8. 有限形式化交付与验证边界

可直接形式化的有限命题包括 LP4 完整复权减回、LP5 倍数数目及外权、
LP7 尺度恒等式、LP10 各段有理幂账、EQ 系数卷积、LP6 尾比及 LP17
的指数比较。附脚本保留实际 μ、非分离复权和负标签，并对漏掩码、
重复交叠、漏1/E、漏驻相因子等错误提供回归守卫。
有限测试不替代二阶导数法、Poisson、时间均值或无限换序证明；本篇
没有新增 Lean 公理或伪完成接口，源验证也不等于最终 main 验收。
