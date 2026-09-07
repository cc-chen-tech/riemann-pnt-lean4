# 大素因子模数：全 h/δ 包的全部原除数重组

白话结论：这次不只估计原 d=q 顶项。若模数 q 的每个素因子都至少是
8T/K，所有原 d<q 项可一起处理：单位容斥的最后一项变成更大 gcd
尺度的顶项，其余项在原核中没有驻点。于是内部平衡 FP3 的这类
完整 centered 包，在 E=T^η、687/550≤η≤5/4 时为 O(D200 T^(1+ε))。
这包含合数模数，不只是素数 q；但带小素因子的模数仍未支付。
η 是 gcd 尺度指数，不是 ζ 零点实部。本文不证明 14/17、2/3 或全局 gate。

English summary: a proper-divisor reassembly controls the whole centered
full h/delta packet when every prime factor of q exceeds the native dual
scale. The surviving terms combine before absolute values into marked top
terms at larger gcd scales. Small-prime moduli and global completion remain open.

## RD1. 同一实际原核与精确范围

原定义源为 49cfacd70c60372757280177c7b63fd4f7760817 的
docs/research/2026-08-24-mobius-weighted-off-diagonal.md，(4.4)–(4.5)。
直接依赖 #538 的 f6c23380c481fbfa22874fbc57b88f102c46d452（TD1–TD9）；
其平方／单位容斥修补为 #536 的 b3a758bcc01540aed5855bd3f1b10e4b7b660721。
另使用冻结 #532 FD2–FD6、#529 CH5–CH9 的具体证明，不修改这些来源。

固定 q₀=1、T≥2、N=T³、R,S≍T³、M,K≍√T，KS≍MR、MK≪T。
固定 e∈[E,2E)，E=T^η；原 F_R(n)、F_S(s) 支持给 n≍R、s≍S，
s=eq。整个包满足 n,s≤N/2，保留原 taper、AFE 截断和 V_t。
e,q 平方自由，(e,q)=(n,eq)=1，q>1。**不另加独立的 q 硬截断**；
q≍S/E 已由 e 与 s 的支持推出。此自然包是原式中明确定义的重组，
不把任意硬 q 盒都算进结论。

令 B=8T/K，称正整数 q 为 B-rough，是指每个素因子 p|q 都满足 p≥B；
约定 1 为 rough，但原和排除 q=1。定义原连续核
\[
 A_m(v)=\frac{F_M(m)F_K(y)}{\sqrt{my}}
  \int W(t/T)V_t(my)(sy/(nm))^{it}dt,
 \qquad y=(nm+ev)/s.                                  \tag{RD1}
\]
在 m,y>0 外平滑延零，B₀=p_N(n)p_N(s)F_R(n)F_S(s)。m 是正整数，
y 不补成整数。完整 h/δ 分割在固定本 AFE 层合法重组，理由是 FD2
的 δ 整数有限及 h Fourier 绝对收敛；不是固定 H/L 包的界。

本文估计的整个原 centered 和为
\[
 \mathscr C_{E,B}=2\sum_{e,q,n,m}
 \frac{\mu(e)\mu(n)B_0}{\sqrt{ns}\,s}
 \sum_{(v,q)=1} A_m(v)
 \left\{\sum_{d\mid(q,nm+ev)}\mu(d)d
                      -\frac{c_q(m)}{\varphi(q)}\right\},       \tag{RD2}
\]
外和限制 q 为 B-rough，保留上述全部条件。括号正是 μ(q)C_q；
没有漏掉外 μ(q)，也没有将其改成 μ²(q)。

## RD2. 一般原除数的单位条件和完整 Fourier

写 q=d l。对 d|(nm+ev)，由于 n,e 为 d-unit，(v,d)=1 当且仅当
(m,d)=1。若后者不成立，这个原除数项为零；不要求 (m,l)=1。
在 (m,d)=1 时，v≡v₀=−nm\bar e mod d，并仍有 (v,l)=1。
CRT 精确给
\[
 \sum_{\substack{v\bmod q\\v\equiv v_0\ (d),\ (v,l)=1}}e_q(jv)
 =c_l(j)e_d(jv_0\bar l).                              \tag{RD3}
\]
定义
\[
 J_j=\frac{F_M(m)}{\sqrt m}\int W(t/T)(s/(nm))^{it}
       \int F_K(y)y^{-1/2+it}V_t(my)e(-jy)\,dy\,dt.
\]
换元 dv=qdy 得 Ahat(j/q)=q e(jnm/(eq))J_j。互反恒等式
\[
 e_d(-jnm\overline{el})e(jnm/(edl))
       =e_{el}(jnm\bar d)                              \tag{RD4}
\]
消去连续相位，但剩下 c_l(j)；不能因此把一般除数项直接叫作无权顶项。
下面在物理整数变量中做完整单位容斥来处理它。

## RD3. 最后一项的精确原核适配

对 l=q/d 作 (v,l)=1 容斥，v=bw：
\[
 \sum_{\substack{(v,q)=1\\d\mid nm+ev}}A_m(v)
 =1_{(m,d)=1}\sum_{b\mid l}\mu(b)
       \sum_{d\mid nm+ebw}A_m(bw).                    \tag{RD5}
\]
因 (b,d)=1，在显示同余下 (w,d)=1 自动满足。
当 b=l，令 e'=el、q'=d；那么 s=e'q'=eq、
y=(nm+e'w)/s，且 μ(e)μ(l)=μ(e')。因此包括唯一外权的该项精确等于
新参数 e',q' 的 TD2 顶项，**不另出现 1/l 因子**。
原 n、s、m、y 权与相位全部相同；这是线性展开项的重组，
不是宣称旧 e 元组和新 e' 元组是同一个原整数子族。

## RD4. 其他单位容斥项的全部频率与尾

若 b<l 且 l 的所有素因子≥B，记 x=l/b，则 x≥B。
内层 w 在模 d 的一个仿射格上。Poisson 的 Jacobian 为
q/(bd)=x，y 频率为 xj，j∈Z；所有仿射相位模长为1。

在 y=Kz、z∈[1/2,2] 上，非零频相位为
t log z−2πKxjz。t∈[T,2T] 且 Kx≥8T，故其导数在全部支集
远离零，尺度为 Kx|j|。原权的十二阶 y 导数统一受 D200 控制，
十二次非驻相积分得
\[
 |J_{xj}|\ll\mathcal D_{200}T\sqrt{K/M}(Kx|j|)^{-12},\quad j\ne0.
                                                               \tag{RD6}
\]
负频也包含在此界中。j=0 不删除：用 t log y 的十二次积分给
|J₀|≪D200 T√(K/M)T^(−12)。W 和 F_K 在边界平坦，原 V_t
混合导数条件来自 FD3；这里不要求新的解析输入。

非零频绝对和收敛，因此对每个 b<l，
\[
 \left|\sum_{d\mid nm+ebw}A_m(bw)\right|
 \ll\mathcal D_{200}xT\sqrt{K/M}\,T^{-12}.           \tag{RD7}
\]
不能把这一步搬到固定 L 包；旧 F(|sy−nm|/L) 会改变导数成本。
一般小素因子也不适用：例如 T=64、K=8、x=2、j=1 的驻点
y=T/(4π) 在 (K/2,2K) 内。这只反驳本非驻相套用，不是原问题 no-go。

## RD5. 全部物理误差，而非单行误差

原外系数含 d，RD7 中 d x=q/b≤q。对 d|q、b|q/d 求和只有
除数 ε 费；n,m,e,q 的行数至多 O(R),O(M),O(E),O(Q)，Q≍S/E。
保留所有掩码到取上界时再放宽，并用 EQ=S、KS≍MR，得到
\[
 |\mathscr E|\ll\mathcal D_{200}T^{1+\epsilon}
     \sqrt{MK R/S}\,Q T^{-12}
 \ll\mathcal D_{200}T^{9/2-\eta-12+\epsilon}.         \tag{RD8}
\]
没有缺失 b 或 d 的行数，也没有在 Poisson 后补虚构的 +1。
原实际支持使全部有限参数在 T 的固定幂内。此误差已包含所有 b<l
及其完整无限频率尾；零频单独支付后才作绝对求和。

## RD6. 带任意 e' 行权的顶项引理

这一步需重跑证明，不能由一个有符号总和的界推出其子和的界。
在自然 dyadic E',Q'=S/E' 层，给顶项插入 β(e')ω(q')，
其中 |β|,|ω|≪εT^ε，且不依赖 n,m、native t；q'>1。
若 E'≥cT^(5/4)，则
\[
 |S_{\rm top}[\beta,\omega;E']|
       \ll_\epsilon\mathcal D_{200}T^{1+\epsilon}.    \tag{RD9}
\]
β 可以是非光滑算术行权，不要求它满足对数相位消去。

取导子分界 Λ=2。低部只有 principal；TD3/RP8 的完整修补后容斥
把 β(hdflC) 留在 C 列，ω(ljY) 留在共同 Y 列。
此时用 reciprocal-φ 质量及 |β|≪T^ε，**不用 TD8 的指数对界**。
TD10 的所有 h/d/f/l/j 求和与时间均值四项给
\[
 \mathcal D_{200}T^\epsilon
 \frac{\sqrt{RQ'M/K}\sqrt T}{(E')^{3/2}}
 \left(1+\sqrt{T/Q'}+\sqrt{T/R}+T/\sqrt{RQ'}\right). \tag{RD10}
\]
若 E'=T^(η')，四项指数依次为
7/2−2η'、5/2−3η'/2、5/2−2η'、3/2−3η'/2。
Q'<T 的两项没有删除；零频另给 T^(9/2−η'−12)。

高导子中 β(hcℓ) 仅是模数行乘子，取模后可在一次 Cauchy／普通
primitive hybrid 大筛前用其上界；ω 在容斥后仍是共同 q' 列系数。
TD7 的同一原 AFE 剖面及 CH5–CH9 完整证明给四项
T、T^(2−η')、T^(5/2−3η'/2)、T^(7/2−2η')。
全部指数在 5/4≤η'≤3 不超过1，故 RD9 成立。
原权仍只用一份 D200；算术 β 不参与光滑求导，也不新增剖面平方。

同样，TD3 的低列指数对及高部证明允许任意有界 ω(q)，因为它在
每次容斥后都是共同 q 列系数；因此 TD3 可用于 rough q 的原顶项。
这是共同系数核查后的证明复用，不是直接截取已估计的有符号和。

## RD7. 在绝对值之前合并所有 proper 主项

取 d>1、l=q/d>1。RD3 的 b=l 项全部合并为 RD9，其中
\[
 \beta_E(e')=\sum_{\substack{l\mid e',\ l>1,\ l\ B\text{-rough}\\
                               E\le e'/l<2E}}1,
 \qquad \omega(q')=1_{q'>1,\ q'\ B\text{-rough}}.     \tag{RD11}
\]
因为原 s 平方自由，(e',q')=1、(n,e'q')=1 与原掩码完全一致；
(m,q')=1 由同余强迫，不添加 (m,l)=1。
β_E≤τ(e')，且每个非空项 e'≥EB。这是先合并再用 RD9，
不是对每个 d 或每个 l 分别估计后漏掉行数。

原 e 的硬壳只进入 β_E。这里不另加 q 硬盒十分重要：
若另有 1_[Q,2Q)(q)=1_[Q,2Q)(q'l)，β 就可能同时依赖 e',q'，
上述共同列论证不再自动成立。该补充限制不在本文结论范围内。

对本文 η 区间，EB≍T^(η+1/2)≫T^(5/4)。按 e' 插入非负 dyadic
分割，仅 O(log T) 个非空层，每层由 RD9 支付。原 F_S(e'q') 和
其余 native 权不变，所有 proper d>1 的合计为 O(D200 T^(1+ε))。

## RD8. 整个 centered 包及尚未解决部分

原 d=1 项由 FD13 的 |Σ_(v,q)=1 A_m(v)|≪D12(T/√(MK))τ(q)
及完整 FD14 外层计数直接给 O(D200 T^(1+ε))；这里没有 d 的大权重。
原 correction 是 FD14 本身，其逐点上界也允许 rough q。
原 d=q 顶项用 RD6 说明的共同 rough q 系数重跑 TD3。
由公式 (RD8) 的误差与公式 (RD11) 的主项重组，最终
\[
 |\mathscr C_{E,B}|\ll_\epsilon\mathcal D_{200}T^{1+\epsilon},
 \qquad 687/550\le\eta\le5/4,\quad B=8T/K.           \tag{RD12}
\]
有界 T 的阈值差由固定常数吸收；该命题仍是非显式渐近估计。

这里只是完整 full h/δ 的 rough-q 自然 FP3 包，不是任意固定 H/L 包，
也不是所有模数。含素因子 p<8T/K 的 q、其他 canonical 分配、q₀ 外和、
非内部与跨 AFE 尾及最终 signed gate 均保留。与 #533/#535 的频率投影
不作无证明的节省相乘；不能登记 Reρ≤14/17 或 Reρ≤2/3 已完成。

## RD9. 真实合数原支持及有限检查边界

取 Y→∞，先由 Bertrand 定理选素数 p≍Y^481、r≍Y^482，
再令 X=(8pr)^(229/321)，选素数 X<e<2X。令 s=epr、R=S=s、
N=8s、T=N^(1/3)≍Y^550、M=K=√T。此时 E=T^(687/550)，
且 e/E=(e/X)^(321/550)∈(1,2^(321/550))⊂(1,2)，严格落在原硬 E 壳。
三个素数对大 Y 互异；取 n 为 (s,2s) 内素数。则 q=pr 为 rough 合数。
取原 h=δ=e、u=v=1、H=L=e，且 x=3√T/4。
y=(nx+e)/s 在 (K/2,2K)，(n,s)=1，n,s≤N/2，HL≤RS/T，
gcd(s,h,δ)=gcd(s,hδ)=e；因此是无限实际内部 FP3 支持，非空性
不是只画出一组连续指数。不声称任意所选权的积分一定非零。

有限脚本保留 T=10^6、M=K=1000、e=32000011、p=50021、r=50101、
s=80195295439123331、n=80195295439123489、x=750 的精确整数例。
q 的两个素因子都大于 B=8000，所有原 core、gcd、mollifier 支持及
T^687≤e^550<2^550 T^687 均经整数／有理核对；最后一项就是 E≤e<2E。

这些 Fourier、原式容斥、系数重组、错误扩张反例和支持测试不能代替
RD4–RD8 的解析尾项、共同列和大筛证明；本文没有新增 Lean 定理。
