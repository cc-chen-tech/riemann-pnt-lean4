# 任意平方自由 e：保留非单位双频的高导子估计

白话结论：e 含小素因子时，不能靠 Fourier 尾把非单位双频删掉。
本篇保留它们，通过广义 Gauss 和精确降模，支付一个真实的新频谱区域：
在 E≈T^(6/5) 时，新模 e 的 primitive conductor ℓ≥T^(1/5) 的
全部部分为 O(A₃₀T^(1+ε))。e 可以有任意小素因子，不再限于素数或
平衡半素数；q 仍为素数，且原 fixed H/L smooth 包不变。

这不是整个 centered 和的上界。低导子（包括 principal）、合数 q、
其他 canonical/q₀、外层尾和共同能量交叉项仍完整留下。

## GH1. 固定上游及原始完整线性对象

唯一 Git 父版本是 #551 的 **3e9ba80a92171b65aa5536089badbc6f373b123b**。
原式取 #545 冻结56e0bbd1的
[RH1–RH5](2026-08-31-physical-prime-pair-reciprocal-hybrid.md)，
但本篇重新证明允许任意平方自由 e 的步骤，不直接套其 prime-e 结论。
smooth 来源仍是 #514
[DP1–DP4 冻结版本](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/7cc9646c8b8a8589b920e24652c86bd063f4b1d7/docs/research/2026-08-31-physical-centered-character-poisson.md)。
不回溯认证旧一般硬 H/L 包。

固定 q₀=a₀=b₀=1，e∈[E,2E) 平方自由，q∈[Q,2Q) 为素数，2E<Q。
原 r=n、s=eq、h=eu、δ=ev，完整和为
\[
 C_{\rm sf}={2T\over RS}\sum_{e,q}\mu(e)\mu(q)
 \sum_{(n,eq)=1}\mu(n)p_N(n)p_N(eq)
 \sum_{u,v\ne0\atop(uv,q)=1}
 \Psi_{\rm sm}(n/R,eq/S,ev/L,eu/H)
               \{e_q(-euv\bar n)+1/(q-1)\}.                 \tag{GH1}
\]
两 taper 按式显式保留；包含它们的联合光滑权总阶≤30预算为 A₃₀。
整包支持 n,eq≤N/2，无新联合硬截断。取固定比较常数下
\[
 R\asymp S\asymp EQ\asymp T^3,\quad H\asymp L\asymp T^{5/2},
 \quad E\asymp T^\eta,\quad Q\asymp T^{3-\eta},\quad1\le\eta\le5/4.
                                                               \tag{GH2}
\]
记 U=H/E、V=L/E、D₁=Q/U、D₂=Q/V、ν=RD₁D₂/(EQ)≈T。
唯一物理外权一直是2T/(RS)。

q 是素数，所以原双 DFT 与 q⁻² Poisson 仍给 UV/q。两个对偶整数
ρ、σ 都非零；这次不分出、不删除 gcd(e,ρσ)>1 的部分。
先保留 q-unit dual 行，扩 (n,q)=1 并减 B_nq；再扩 q-unit dual，
在全部 n,e-unit 行减 B_qd。旧常数 O_q 保留原两组 q-unit 掩码。
于是准确有
\[
                    C_{\rm sf}=F+O_q-B_{nq}-B_{qd}.            \tag{GH3}
\]
F 的原外 μ(e)μ(q)μ(n)、共同 Φ、UV/q 与 (n,e)=1 都保留；其相位为
\[
             e_e(-n\rho\sigma\bar q)e(n\rho\sigma/(eq)).      \tag{GH4}
\]
不再有 q-dual 或 n-q 交叉掩码。RH7 的 floor(2R/q) 及 O(E) 个
有界 e 行仍给 B_nq≪A₃₀T；O_q≪A₃₀T。六阶 q 倍数尾给
B_qd≪A₃₀T^(−23/2+5η)。这些不需 e 素数，也不借全局 principal。

## GH2. 广义 Gauss：右侧必须是 primitive 角色

写 e=cℓ、(c,ℓ)=1，χ 为模 ℓ 的 primitive 角色，χ_ind 为它诱导至
模 e 的角色。对任意整数 a（无需与 e 互素），CRT 给
\[
 \tau_e(\overline{\chi_{\rm ind}};a)
 =c_c(a)\bar\chi(c)\chi(a)\tau_\ell(\bar\chi).                \tag{GH5}
\]
左侧按模 e 的单位求和；右側 χ 都是模 ℓ 的 primitive 零延拓，
只在 (a,ℓ)>1 时置零。模 c 的 CRT 部分是 c_c(a)，模 ℓ 的部分是
χ(a)barχ(c)τℓ(barχ)。ℓ=1 时 χ(a)=1 对所有整数成立，包括 a=0。
例如 e=15、ℓ=3、c=5、a=5 的右侧非零；误用 χ_ind(5) 会删掉它。

平方自由 c 满足 μ(c)c_c(a)=Σ_(d|(c,a))μ(d)d。因此对 (n,e)=1，
\[
 \mu(e)e_e(-an\bar q)=
 \sum_{\ell\mid e}\sum_{\chi\bmod\ell}^{*}
 {\mu(\ell)\tau_\ell(\bar\chi)\over\varphi(c)\varphi(\ell)}
 \chi(-n)\bar\chi(q)\bar\chi(c)\chi(a)
                         \sum_{d\mid(c,a)}\mu(d)d.             \tag{GH6}
\]
所有 c/ℓ/χ/d 层均保留。主角色 ℓ=1 为
φ(e)⁻¹Σ_(d|(e,a))μ(d)d，非单位 a 时不是1/φ(e)。

给定1≤Z≤E，在 GH6 中取 ℓ≥max(2,Z) 定义 F_hi(Z)，其余为 F_lo(Z)。
这个投影仅作用于 GH4 的周期因子；共同 chirp、Φ、全部系数不变。
准确 F=F_hi+F_lo。Z=1 仍排除 principal；不是能量正交或正性声明。

## GH3. d|ρσ 的唯一分配与共同掩码

对 d|c、d|ρσ，取 j=gcd(d,ρ)、k=d/j。平方自由性给逐项双射
\[
       \rho=jr,\quad\sigma=ks,\quad(r,k)=1,\quad jk=d.        \tag{GH7}
\]
反向也唯一。不能再加(r,j)=1、(s,j)=1或(s,k)=1；正负整数均保留。
χ(d)barχ(c)=barχ(c/d)，所以固定 c,d,j 后的精确角色系数为
\[
 {\mu(\ell)\mu(d)d\tau_\ell(\bar\chi)\bar\chi(c/d)\chi(-1)
       \over\varphi(c)\varphi(\ell)}
                         \chi(n)\bar\chi(q)\chi(r)\chi(s).    \tag{GH8}
\]
再乘原 μ(q)μ(n) 与已含两 taper 的联合 Φ。n 列的额外掩码是(n,c)=1，
r 列是(r,k)=1；它们对变化的 ℓ 共同。ℓ-unit 由 χ 零延拓实现。
不补回 n-q 掩码，不因子化原 μ(n)。共因子相位不能删掉。

## GH4. 原核、短频率端点与一次 hybrid 大筛

选完整光滑 dyadic 分解，支撑 J₁/2≤|ρ|≤2J₁、J₂/2≤|σ|≤2J₂，
J_i≥1/2。记 λ_i=J_i/D_i、θ=λ₁λ₂、X=νθ、K=QJ₁J₂。
分配后 r,s 尺度为 J₁/j、J₂/k；若无非零整数直接为0。
非空时两尺度均≥1/2，故 K/d≥Q/4，不产生额外 +1 能量项。

固定 c,d,j 后，e/E=ℓ/(E/c)、ρ/J₁=r/(J₁/j)、σ/J₂=s/(J₂/k)。
五维 log 共同分离仍有 RH12 的 A₃₀∏(1+λ_i)⁻⁸ 预算，不对掩码求导。
实际 chirp 是 e(d nrs/(cℓq))，其参数仍为 X，不是 X/d 或 X/c。
归一化 c,d 的 Mellin 相位模长1。只在取模后共轭两个标签值，
得到共同整数产品 q|rs|，长度 O(K/d)、系数受 τ₃ 控制。
\[
 \|a_N\|_2^2\ll R,\qquad
 \|a_{qrs}\|_2^2\ll_\epsilon (K/d)T^\epsilon
                                      \prod_i(1+\lambda_i)^\epsilon. \tag{GH9}
\]
无限产品长度的 λ_i^ε 不隐藏进 T^ε；不要求新角色系数乘法性。

有效导子尺度记作 L_c=E/c。平方自由、(c,ℓ)=1及原 e 壳只是模数
行系数，在正 Cauchy/大筛量中才扩模数。采用
[CIS (1.6) 的普通 hybrid primitive 大筛](https://arxiv.org/pdf/1105.1176)，
不是该文 asymptotic 或特殊 mollifier 输入。Gauss 准确模长
√ℓ/φ(ℓ)≪T^ε/√L_c；RH13 的 Mellin 幅度是(1+X)⁻¹/²、时间宽1+X。
一次共同 (ℓ,χ,t) Cauchy 给每块、未乘原外权的界
\[
 {UV\over Q}{A_{30}T^\epsilon d\over\varphi(c)\sqrt{L_c(1+X)}}
 \sqrt{R(K/d)(R+L_c^2(1+X))(K/d+L_c^2(1+X))}
                           \prod_i(1+\lambda_i)^{-8+\epsilon}. \tag{GH10}
\]
高投影 c≤2E/Z；ℓ≥2 保证 L_c≥1/2，常数端点以 max(1,L_c) 吸收。
不能再乘模数或角色个数。取 K₀=QD₁D₂、X=ν，根号展开的四项是
\[
 {RK_0\over\varphi(c)\sqrt{L_c\nu}},\quad
 {R\sqrt{K_0L_cd}\over\varphi(c)},\quad
 {K_0\sqrt{RL_c}\over\varphi(c)},\quad
 {L_c^{3/2}\sqrt{RK_0\nu d}\over\varphi(c)}.                   \tag{GH11}
\]
d 幂依次为0、1/2、0、1/2；不存在遗漏的再一次 d 行数。

## GH5. 全部 c/d/j、双无限频率及时间尾

每个 d 有 τ(d) 个 j。初等有限界
\[
 \sum_{d\mid c}\tau(d)\le\tau(c)^2,\qquad
 \sum_{d\mid c}\tau(d)\sqrt d\le\sqrt c\,\tau(c)^2             \tag{GH12}
\]
和 φ(c)⁻¹≪T^ε/c 给四个总费用：
\[
 \sum_{c\le2E/Z}\sum_{d\mid c,j\mid d}
 {1\over\varphi(c)\sqrt{E/c}}\ll {T^\epsilon\over\sqrt Z},
\]
\[
 \sum_{c\le2E/Z}\sum_{d\mid c,j\mid d}
 {\sqrt{E/c}\sqrt d\over\varphi(c)}\ll T^\epsilon\sqrt E,
 \qquad
 \sum_{c\le2E/Z}\sum_{d\mid c,j\mid d}
 {\sqrt{E/c}\over\varphi(c)}\ll T^\epsilon\sqrt E,
\]
\[
 \sum_{c\le2E/Z}\sum_{d\mid c,j\mid d}
 {(E/c)^{3/2}\sqrt d\over\varphi(c)}\ll T^\epsilon E^{3/2}.   \tag{GH13}
\]
第一项用 Σ_(c≤2E/Z)c⁻¹/²≪√(E/Z)；第二项是调和和，log E 明确
吸收入 T^ε，不称为无条件常数收敛；末两项的 c⁻³/²、c⁻² 可和。
所有 c≤2E 处在固定 T 幂内，以上算术除数费用没有无限变量。

对每个固定 c,d,j，GH10 平方在去公共系数后准确是
\[
 {R^2K^2\over\varphi(c)^2L_c(1+X)}
 +{dL_cR^2K\over\varphi(c)^2}
 +{L_cRK^2\over\varphi(c)^2}
 +{dL_c^3RK(1+X)\over\varphi(c)^2}.                          \tag{GH14}
\]
代 K=K₀θ、X=νθ、ν≥1，相对 GH11 四项平方和至多2max(θ,θ²)。
因此一般块只多 O(√θ+θ)，与∏(1+λ_i)^(-8+ε)在两标签的大小方向
均可和。空整数支撑已先置0；求上界时放开 d/j 限制只扩大正 majorant。
外 Mellin 环 |t|≈2^h(1+X) 中大筛成本至多增2^h，幅度衰减2⁻⁶ʰ。
这些一致 majorant 支持全部原子、Fourier、Mellin 截断极限及换序；
不是把无限 dual 全当固定 T 幂，也不是跨全部原 H/L 或 AFE 外层求和。

## GH6. 新支付区域及保留的真正余项

恢复原2T/(RS)，得到
\[
 |F_{\rm hi}(Z)|\ll_\epsilon {A_{30}T^{1+\epsilon}\over RS}{UV\over Q}
 \left\{{RK_0\over\sqrt{\nu Z}}+\sqrt E R\sqrt{K_0}
          +\sqrt E K_0\sqrt R+E^{3/2}\sqrt{RK_0\nu}\right\}.   \tag{GH15}
\]
若 Z=T^z，四个物理指数是
\[
          7/2-2\eta-z/2,\quad2-\eta,\quad5/2-3\eta/2,\quad1. \tag{GH16}
\]
1≤η≤5/4 可选 z=max(0,5−4η)≤η。特别是 η=6/5、Z=T^(1/5)
时四项为1、4/5、7/10、1，高导子整个有符号投影≤A₃₀T^(1+ε)。
用于比较的是本证明 Z=1 的同一广义 Gauss 预算11/10，再在高投影
重跑 c 的截断和得到1，净省1/10；不是从 signed 全和界直接删行。

新的真实部分含非单位 dual 和不平衡小因子 e，例如 e=15、ρσ=3，
导子15项为0而导子5项非零（c₃(3)=2）。无限原支持可取 e=3p、
p≈Y⁶、q≈Y⁹ 为不同素数，R=S=eq、T=(8S)^(1/3)，并沿 RH8 取
n∈(S,2S) 素数、N=8S、H=L=S/√T、u=v=ceil(H/e)、x=3√T/4。
原单位条件和正 AFE 支持非空。dual ρ 可取√T量级的3倍数、σ同阶，
都为 p-unit；导子 p≈E/3 超过T^(1/5)。不声称任意给定积分非零。

GH3 现在只得到 C_sf=F_lo+O(A₃₀T^(1+ε))；F_lo 含所有低导子与
principal，尚无所需 signed 上界。合数 q、其余 canonical/q₀、外层
AFE/H/L、实际 amplified 系数及 EE*、EC*、CE*、CC*没有免费迁移。
本篇不证明完整 coupled-kernel gate、twisted moment 或零点结论。

有限可形式化内容是 GH3、GH5–GH8、GH12、GH14 及端点/指数账；
附脚本保留原 μ、非单位层和有符号交叠的反例。有限检查不替代解析
大筛/Poisson/无限换序证明，源测试不等于 CI 或最终 main 验收。
