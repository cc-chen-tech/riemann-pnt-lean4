# 平衡半素数 e 的完整固定光滑 centered 包

白话结论：#547 只支付 e、q 都为素数的原包。本篇允许 e 是两个大小
相近、互不相同的素数之积，q 仍为素数。新增的两个低导子角色不能省略；
它们可以连同新主角色和所有扩和差一起支付。在 E≈T^(6/5) 时，整个
指定原包由旧 T^(11/10) 预算降到 A₃₀T^(1+ε)，净省1/10次幂。

这不是一般合数模数定理。原核半范数 A₃₀、其他 e/q、canonical/q₀、
跨 AFE/标签尾及共同能量交叉项仍保留；完整 twisted moment 尚未证明。

## BS1. 来源和真正新增的原域

唯一 Git 父版本是 #547 的 **63f15f23a7d06452d9763e2801a32f00de1a72c5**。
原式采用 #545 冻结
[RH1–RH3](2026-08-31-physical-prime-pair-reciprocal-hybrid.md)
56e0bbd1a426b86b1a58d237b9fa8f3d08feaf30；本篇重新验证其素数 e
限制下的每一步，不能直接给合数 e 套用 RH21。
主角色使用 #547 的
[LP3–LP6](2026-08-31-physical-prime-pair-principal-loglabels.md)
共同光滑原子、对数标签和 Mellin 估计。
原 smooth 来源仍是 #514 冻结
[7cc9646c 的 DP1–DP4](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/7cc9646c8b8a8589b920e24652c86bd063f4b1d7/docs/research/2026-08-31-physical-centered-character-poisson.md)，
不回溯赋给一般硬 H/L 包。

固定比较常数 C_b≥2，定义有限集合
\[
 \mathcal B(E)=\{e=p_1p_2\in[E,2E):p_1,p_2\text{ 为不同素数},
                  \sqrt E/C_b\le p_i\le C_b\sqrt E\}.          \tag{BS1}
\]
固定 q₀=a₀=b₀=1、q 为素数且 Q≤q<2Q、2E<Q。原 r=n、s=eq、
h=eu、δ=ev，保留 (n,eq)=(uv,q)=1、u,v≠0 及 μ(e)μ(q)μ(n)。
整包支持保证 n,eq≤N/2，不加新的联合硬截断。两 taper 按(BS2)显式
保留，原 AFE 核及原 F 光滑标签留在 Ψ_sm 内；包含两 taper 的整个
联合光滑权总阶≤30预算记为 A₃₀，不重复乘 taper。
定义的原 centered 和为
\[
 C_{\mathcal B}={2T\over RS}\sum_{e\in\mathcal B(E),\ q\ \mathrm{prime}}
 \mu(e)\mu(q)\sum_{(n,eq)=1}\mu(n)p_N(n)p_N(eq)
 \sum_{u,v\ne0\atop(uv,q)=1}\Psi_{\rm sm}(n/R,eq/S,ev/L,eu/H)
              \{e_q(-euv\bar n)+1/(q-1)\}.             \tag{BS2}
\]
q-primal mean 是 −1/(q−1)；e 的半素数性质不改变这一点。
参数范围为
\[
 R\asymp S\asymp EQ\asymp T^3,\quad H\asymp L\asymp T^{5/2},
 \quad E\asymp T^\eta,\quad Q\asymp T^{3-\eta},\quad
                    7/6\le\eta\le5/4.                 \tag{BS3}
\]
记 U=H/E、V=L/E、D₁=Q/U、D₂=Q/V、ν=RD₁D₂/(EQ)；D_i≈√T、ν≈T。
e 的半素数指示属于算术行，不求导，不声称额外 Möbius 符号消去。

## BS2. q 双完成及三个真实扩和差

q 仍为素数，RH4 有限双 DFT 及 q⁻² Poisson 给原 UV/q 系数，
相位 e_q(nρσ inverse(e)) 与旧常数1/(q−1)。全非零整数 ρ、σ 均保留。
旧常数 O_q 的绝对值由 UV D₁D₂=Q² 和 O(REQ) 个 n/e/q 直接付为
O(A₃₀T)，没有使用全局 principal 预算。

先从 raw 部分分出 B_e：gcd(e,ρσ)>1，仍保留原全部 n/q 单位条件。
余下 dual-unit-e 行扩 n-unit-q，减回 B_nq；μ(qj) 保持原值。
再去 q-dual 掩码，减回 B_qd。得到准确线性账
\[
             C_{\mathcal B}=F+O_q+B_e-B_{nq}-B_{qd}.             \tag{BS4}
\]
F 的 n、ρ、σ 都与 e 互素，但没有 q 相关的交叉掩码。
与 RH7 相同的 floor(2R/q) 计数给 B_nq≪A₃₀T；六阶 q 倍数尾
给 B_qd 的指数 −23/2+5η<0。e 行只是至多 O(E) 个有界系数，
这些两项并不需要 e 为素数。

新增 B_e 不能沿用“e|ρσ”的素数结论。由 BS1，它包含某个 p_i|ρ
或 p_i|σ，p_i≈√E；D_i/p_i→0。对一个标签用16阶 Fourier 衰减，
另一个用可和的2阶衰减，总共18≤30阶原导数。对固定 e，所有非单位
dual 的绝对总量不超过
\[
 A_{30}[(D_1/\sqrt E)^{16}D_2+D_1(D_2/\sqrt E)^{16}].
\]
恢复 UV/q、全部 e/q/n 个数和唯一2T/(RS)，有
\[
 |B_e|\ll A_{30}{T\over RS}(REQ){UV\over Q}
       [(D_1/\sqrt E)^{16}D_2+D_1(D_2/\sqrt E)^{16}]
 \ll A_{30}T^{23/2-9\eta}.                              \tag{BS5}
\]
η=7/6 恰为1，η=6/5 为7/10。有限小 T 可由常数吸收。一般平方自由 e
含小素因子时此论证不成立；这正是没有宣布所有 e 覆盖的原因。

## BS3. 新模 e 的全部三类非主角色与主角色符号

对 F 使用精确 reciprocity
e_q(nρσ inverse(e))=e_e(−nρσ inverse(q))e(nρσ/(eq))。
连续 chirp 参数为 ν≈T，不放进免费光滑权。因为全部 e-unit 保留，
\[
 e_e(x)={\mu(e)\over\varphi(e)}+
       {1\over\varphi(e)}\sum_{\chi\ne\chi_0\bmod e}
                              \tau_e(\bar\chi)\chi(x).          \tag{BS6}
\]
外 μ(e) 与主角色 μ(e) 相乘为1。新 principal P 的系数准确是
\[
       {2T\over RS}{\mu(q)\mu(n)UV\over q\varphi(e)},          \tag{BS7}
\]
乘原 Φ、chirp 和 n/dual 的 e-unit 掩码；不是套用 −μ(e)/(e−1)。

当 e=p₁p₂ 时，非主角色的 primitive conductor 只有三类：e、p₁、p₂。
每个角色只归类一次。记后两类 e=cℓ，c、ℓ 为不同素数；准确有
\[
 \tau_{c\ell}(\bar\chi)=\mu(c)\bar\chi(c)\tau_\ell(\bar\chi),
 \qquad\mu(e)\tau_e(\bar\chi)
           =\mu(\ell)\bar\chi(c)\tau_\ell(\bar\chi).           \tag{BS8}
\]
保留 χ(−1)、barχ(q)、barχ(c) 以及 n、ρ、σ 的 c-unit 条件。
ℓ-unit 条件由角色零延拓给出。导子2没有非主 primitive 角色；不得
虚构它。渐近 BS1 中所有 p_i 都趋于无穷，有限端点仍按该分类处理。

## BS4. 完整 primitive-e 部分

这部分用 RH12–RH17 的同一五维共同分离及 hybrid primitive 大筛。
把1_(e∈B(E))保留在模数行系数里，只在取模/Cauchy 后的正量扩至
所有 primitive 模数 e≤2E。不是从已知 signed 总和界直接删行。
先取模再共轭两个标签，得到共同整数产品 q|ρσ|，保留全部系数及
无界产品长度的除数成本；n 列与它共同，原外权不变。

自然 dual 尺度的四个物理指数与 RH18 一致：
\[
 7/2-5\eta/2,\qquad2-\eta,\qquad5/2-3\eta/2,\qquad1.         \tag{BS9}
\]
η≥1 均≤1。RH17 的短 X 比较和双无限 dual/Mellin 尾在本模数
行限制下仍成立，包含 K 不在固定 T 幂内时的 λ_i^ε 增长。

## BS5. 两个诱导素导子：固定 c 后才作大筛

固定 c≈√E，ℓ∈[E/c,2E/c) 另满足 BS1 的平衡条件且 ℓ≠c。
设导子尺度 L_c≈E/c≈√E。N 列保留(n,c)=1，qρσ产品列保留
(ρσ,c)=1；这些列对变化的 ℓ 共同。q>2E，故 q 与 c、ℓ 自动互素。
在固定 c 的五维原权中，e/E=(cℓ)/E=ℓ/(E/c)，无新的导数损失。

对完整正负 dual 块 J₁、J₂，记 θ=(J₁/D₁)(J₂/D₂)、X=νθ、
K=QJ₁J₂。它们没有再除以 c。由 BS8，Gauss 系数准确模长为
√ℓ/[φ(c)φ(ℓ)]≪1/(φ(c)√L_c)；固定 c 的共同 hybrid Cauchy
给每块未乘外权的界
\[
 {UV\over Q}{A_{30}T^\epsilon\over\varphi(c)\sqrt{L_c(1+X)}}
 \sqrt{RK(R+L_c^2(1+X))(K+L_c^2(1+X))}
                   \prod_i(1+\lambda_i)^{-8+\epsilon}.        \tag{BS10}
\]
c^−it、barχ(c) 均保留在模数标量中，模长1。此后才对固定 c 的
上界取和；平凡计数给 Σ_(c≈√E,prime)1/φ(c)=O_Cb(1)，不需 PNT。
不声称跨 c 的 N 列共同，不再额外乘 e 或角色个数。

取统一可比 L_c≈√E，恢复外权后四个指数是
\[
 7/2-9\eta/4,\quad2-5\eta/4,\quad5/2-7\eta/4,\quad1-3\eta/4.
                                                               \tag{BS11}
\]
在 η=7/6 最大7/8，η=6/5 依次4/5、1/2、2/5、1/10。
短 X 的四项平方展开与 RH17 完全同形，只把 E 换成 L_c；尾部
仍是可和的 O(√θ+θ)∏(1+λ_i)^−8+ε，时间环也保留衰减。
这支付两类诱导角色全部费用，不能只计算 primitive-e 一类。

## BS6. 同一主角色的精确 f 容斥与两列同步缩短

先把 P 的 dual-unit-e 条件去掉，保留 n-unit-e，记扩大后的和 P̄。
减回误差 B_pd 按 BS5 同一非零倍数尾估计，但多1/φ(e)≪_εT^ε/E，
故
\[
                   |B_{pd}|\ll_\epsilon A_{30}T^{23/2-10\eta+\epsilon}.
                                                               \tag{BS12}
\]
这里 BS5 指公式(BS5)，不是诱导角色一节。P=P̄−B_pd。
不再用粗计数删 n-unit-e，而是完整使用
\[
 1_{(n,e)=1}=\sum_{f\mid(n,e)}\mu(f),\qquad n=fm,\quad e=fa.
                                                               \tag{BS13}
\]
固定 f≤2E 后，系数是 μ(f)μ(q)μ(fm)，另有1_(fa∈B(E))。
μ(fm) 不因子化，不额外加(m,a)=1或(m,f)=1；(f,a)=1已由 B(E)保证。
将 (fa)/φ(fa) 留在 a 列的算术系数中，大小≪_εT^ε；1/(fa q)以
1/(EQ)和归一化光滑因子表示。其范数费用只计入最终 T^ε 一次。

共同坐标 m/(R/f)、a/(E/f)、q/Q、|ρ|/J₁、|σ|/J₂ 准确等于原
n/R、e/E、q/Q 和双 dual 坐标。chirp 变成 e(mρσ/(aq))，
X=(R/f)J₁J₂/[(E/f)Q]=RJ₁J₂/(EQ)，仍未改变。
两标签现在完全无算术权，#547 的加权 H⁴、28≤30阶预算、log 标签
及近移位零频处理可以使用；A₃₀ 不再乘第二次。

N_f 的长度是 R/f，保留 μ(fm)；产品 a q 列长度是 S/f，保留
fa∈B(E)、φ 因子、q 素数及共同复系数。平方能量分别≪R/f与
(S/f)T^ε，τ₂即足够。于是每 f、每 dual 块未乘原外权的主界为
\[
 A_{30}T^\epsilon{UV\over QE}X^{1/3}
 \sqrt{{R\over f}{S\over f}(R/f+X)(S/f+X)}
                   \prod_i(1+\lambda_i)^{-8}.                 \tag{BS14}
\]
展开根号上界为
\[
 {RS\over f^2}+{\sqrt X(R\sqrt S+S\sqrt R)\over f^{3/2}}
                       +{X\sqrt{RS}\over f}.                  \tag{BS15}
\]
全部 f≤2E 的前两项绝对可和，末项仅 log(2E)，不增加 E 的幂次。
必须先保留这个全展开再求 f；不能错把所有行都当长度 R、S。
主项自然尺度 X=ν 恢复外权为 A₃₀T^(10/3−2η+ε)。

小 X 时两个非零整数标签都在固定有界尺度，Mellin 是统一 Schwartz；
同一 f 展开给 A₃₀T^(3−2η+ε)。大 X 和时间尾依 #547 LP6，
一般 X=νθ 的额外增长至多 θ^(1/3)max(1,θ)，与每标签8阶衰减
可和。f 求和有限且已有统一调和界，以上正 majorant 允许换序及
全部原子、时间和双 dual 截断极限，不把无限变量偷偷算成固定T幂。
综上
\[
 |P|\ll_\epsilon A_{30}T^\epsilon
   [T^{10/3-2\eta}+T^{3-2\eta}+T^{23/2-10\eta}].               \tag{BS16}
\]

## BS7. 完整新原包与净改善

把 BS4 的真实误差、primitive-e、两个诱导角色和同一个 P 合回，
BS3 范围内所有成本都≤A₃₀T^(1+ε)，所以
\[
 \boxed{|C_{\mathcal B}|\ll_{\epsilon,C_b} A_{30}T^{1+\epsilon}
                         \quad(7/6\le\eta\le5/4).}            \tag{BS17}
\]
η=6/5 时，新主角色14/15、primitive-e最大1、诱导部分4/5、
非单位 e-dual 7/10；旧 q 常数及 n=qj 等费用仍在，不自动消失。

用于比较的旧 DP14 必须在本域重跑：固定其 e/n 容斥 f 后，
1_(fa∈B(E))是 a 共同列的有界指示，qprime使原导子层 c=1。
只在正 Cauchy/大筛和内扩模数，故原证明仍给本 C_B 的11/10预算。
BS17 把这个此前未付的完整平衡半素数e/素数q包降到1，净省1/10，
不是从 signed 总和直接删除其余 e 行，也不与 #547 的 saving 相乘。

本篇不覆盖不平衡半素数e、更多小素因子e、合数q、其余canonical/q₀、
完整显式主项或跨 AFE/H/L 尾。EE*、EC*、CE*、CC*仍须全部保留。
不把原 μ(n) 共同列免费迁移为任意 amplified 系数，不借用其他任务的
full-h/full-δ 结果。本篇不证明完整 coupled-kernel gate 或零点定理。

## BS8. 无限非空族与有限形式化内容

Bertrand 在相邻不交的可比倍长区间取不同素数 p₁≈Y³、p₂≈Y³，
另取 q≈Y⁹。e=p₁p₂≈Y⁶，S=R=eq≈Y¹⁵，T=(8S)^(1/3)≈Y⁵，
N=8S、M_z=K_z=√T、H=L=S/√T。取素数 n∈(S,2S)，
u=v=ceil(H/e)<q。原 μ(e)=1、μ(n)=−1，所有单位条件成立；
n,s≤N/4，x=3√T/4 时 y=(nx+δ)/s 落入正的 AFE 支持。
实际变量可再作有限 dyadic 取整，固定 C_b 及比较常数吸收变化。
这是原整数和核支持非空，不声称任意给定积分非零或正密度。

有限形式化命题包括：BS4完整复权减回、角色导子唯一三分类、BS8
Gauss/μ/共因子相位、BS13 完整容斥和原相位、BS15 全 f 费用、
非空整数支持及所有有理指数。脚本保留合数 e 与原 μ 的反例。
这些有限检查不代替 Poisson、hybrid大筛、log相位或无限换序证明，
不新增 Lean 公理；源测试不等于最终 main 验收。
