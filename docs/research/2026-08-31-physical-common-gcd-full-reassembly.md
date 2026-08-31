# 共同 gcd 层：完整 h/δ 的全部 canonical 分配

白话结论：在 #546 的同一个内部自然 AFE 尺度，把只整除 h、只整除 δ
的素因子分配全部合起来，可以去掉 a₀=b₀=1 的限制。对于共同因子
e=gcd(s,h,δ)∈[E,2E)、E=T^η、687/550≤η≤5/4，整个这一层的
原中心化和为 O(D200 T^(1+ε))。这里不是降低 E 门槛，也不是逐个
固定 a₀/b₀ 硬子壳的界；η 不是零点实部。其余 e、q₀、AFE 外尾和
最终 14/17、2/3 零点排除仍开放。

English summary: summing all canonical allocations at a fixed shared-gcd
scale converts the full h/delta centered packet into a signed-mark
unmasked top term and a different, explicit Ramanujan correction.
The old-shell mark is retained through the low-conductor argument.
Both coordinate axes are restored before splitting the centered kernel.
This is a local analytic result, not a Lean or global zero-free theorem.

## CG1. 冻结来源与精确交付范围

定义源为 49cfacd70c60372757280177c7b63fd4f7760817 的
docs/research/2026-08-24-mobius-weighted-off-diagonal.md (4.4)–(4.5)。
直接父版本是 #546 的 298fa7178a23e6dbfa33fa5c054aa918341d30f0，
使用其 AM1 的 native 核及 AM5–AM10 的辅助顶项证明；不直接把 AM3
的 centered 总和界赋给本文的新子项。另一解析来源为 #532 的
08f7b664b294cb9649d76223188ed1da7f95eb83，FD8–FD13 的一致格界。

固定 q₀=1、T≥2、N=T³，R,S≍T³、M,K≍√T、KS≍MR、MK≪T。
所有比较常数固定。n≍R、s≍S 的整个平滑包保证 n,s≤N/2；
不在后来的联合光滑权中另插硬截断。保留
B₀=p_N(n)p_N(s)F_R(n)F_S(s) 及全部实际 W、V、F_M、F_K。
下文的全 h/δ 不保留额外 H/L 因子或 a₀/b₀/q 的独立硬子壳。

令 e=gcd(s,h,δ)∈[E,2E)，s=eq、h=eu、δ=ev。原 μ(s) 非零部分给
e,q 平方自由，(e,q)=(n,eq)=1。精确条件是
\[
 \gcd(q,u,v)=1,                                      \tag{CG1}
\]
不是 (uv,q)=1。事实上 a₀=(q,u)、b₀=(q,v) 两两互素，剩余模数
q/(a₀b₀) 与 u,v 均互素；这唯一包含全部 canonical 分配。
原 n-unit 平均满足
\[
 \frac{c_s(h\delta)}{\varphi(s)}
 =\frac{c_q(uv)}{\varphi(q)}
 =\frac{\mu(q/(a_0b_0))}{\varphi(q/(a_0b_0))}.         \tag{CG2}
\]
等式使用 (e,q)=1 与平方自由性。保留真实外符号 μ(e)μ(q)μ(n)。

对固定 v 定义紧支撑 x 核
\[
 A_x^{e,s}(v)=\frac{F_M(x)F_K(y)}{\sqrt{xy}}
  \int W(t/T)V_t(xy)(sy/(nx))^{it}\,dt,\qquad
 y=(nx+ev)/s.                                        \tag{CG3}
\]
在正 x,y 支持外按原光滑权延零；y 一直是连续变量。
记 \(\widehat A_v(\xi)=\int A_x^{e,s}(v)e(-x\xi)\,dx\)。
本文对象是原 global centered 和的以下线性限制：
\[
 \mathscr C_E^{\rm common}
 =2\sum_{e,q,n}\frac{\mu(e)\mu(q)\mu(n)B_0}{\sqrt{ns}\,s}
 \sum_{\substack{u,v\in\mathbb Z\\(q,u,v)=1}}
 \left[e_q(-euv\bar n)-\frac{c_q(uv)}{\varphi(q)}\right]
 \widehat A_v(u/q).                                  \tag{CG4}
\]
q=1 的整括号为零，故以下原 q>1。u=0 或 v=0 时括号也逐点为零。
所以可以先在完整 centered 差中补回两轴，再进行 raw/principal 拆分。
本文估计的是这个补轴后的同一分解两项，**不宣称未补轴原 raw 与
principal 各自已付**。不可拆开后单独删去它们非零的轴项。

固定本 AFE 层，δ=sy−nx 在有限整数区间；对每个 δ，紧支光滑 x 核
的 h Fourier 和绝对收敛。故从原重叠 H/L 光滑分割合回 CG4 合法，
不由此宣称跨 AFE 层的统一换序或尾界。

范数 \(\mathcal D_{200}\) 同 AM1：固定缩放因子的 C^200 范数加1
按其出现次数取乘积，再乘
\[
 1+\max_{j+k\le200}\sup_{\substack{x>0\\T\le t\le2T}}
 (1+x/T)^{200}x^jT^k|\partial_x^j\partial_t^kV_t(x)|.
\]
以下始终只付一份这个原核预算。

## CG2. 全 h 的有限 CRT：新的真实校正

固定 v，设 g=(v,q)、l=q/g。条件 CG1 变成 (u,g)=1；
v/g 是 l-unit，但不要求它是 g-unit。有限 Fourier 系数恰为
\[
 \begin{split}
 \sum_{\substack{u\bmod q\\(u,g)=1}}
 e_q[-u(m+ev\bar n)]&=
       l\,c_g(m)\,1_{l\mid nm+ev},\\
 \sum_{\substack{u\bmod q\\(u,g)=1}}
 \frac{c_q(uv)}{\varphi(q)}e_q(-um)&=
       \frac l{\varphi(l)}c_g(m)\,1_{(m,l)=1}.
 \end{split}                                         \tag{CG5}
\]
证明：CRT 的 g 分量给 c_g(m)，因 g|v；l 分量中 v 是单位。
raw 的完整 u mod l 求和给 l 倍同余指标；principal 中
c_q(uv)/φ(q)=c_l(u)/φ(l)，Ramanujan 和的完整 DFT 给
l·1_(m,l)=1。有限 Fourier 与全 h Poisson 因而给 CG4 中每个正整数
m 的系数为 CG5 两行之差，乘同一个 \(A_m^{e,s}(v)\)。

l=1 时两行完全相等，仍须整体保留。m 不是新的 Möbius 整数，
也不要求 (m,q)=1。例如 q=15、e=n=1、v=3、m=9 时差为 −5/2：
非单位且非平方自由的 m 确实不能删除。

## CG3. raw 的完整共同 gcd 容斥

对补轴后的 raw 使用精确恒等式
\[
 1_{(q,u,v)=1}=\sum_{d\mid q,\ d\mid u,\ d\mid v}\mu(d).
\]
置 u=dU、v=dV、e'=ed、q'=q/d，s=e'q' 不变。原相位、h Fourier
频率分别变成 \(e_{q'}(-e'UV\bar n)\)、U/q'。
现在没有 U-unit 掩码，全 U 求和给 \(q'1_{q'\mid nm+e'V}\)。
同时
\[
 \mu(e)\mu(q)\mu(d)=\mu(e')\mu(q')\mu(d).
\]
在取绝对值前，合计原 e 壳产生**有符号**标记
\[
 \beta^\mu_{E,q'}(e')=
 \sum_{\substack{d\mid e'\\E\le e'/d<2E\\dq'>1}}\mu(d). \tag{CG6}
\]
精确 raw 重组是
\[
 \mathscr R_E=
 2\sum_{e',q',n,m}
 \frac{\beta^\mu_{E,q'}(e')\mu(e')\mu(q')\mu(n)q'B_0}
      {\sqrt{ns}\,s}
 \sum_{q'\mid nm+e'V}A_m^{e',s}(V).                   \tag{CG7}
\]
e',q' 平方自由，(e',q')=(n,e'q')=1；不加 (V,q') 或 (m,q')。
原有限 q>1 对应 dq'>1。若 q'>1 它自动满足；q'=1 时 e'=s≍S≫E，
渐近本域 d=1 不在标记中。有界 T 可合入固定常数，但精确有限等式
继续保留该条件。不能把 β^μ 换成 AM4 的无符号 β。

CG7 恰是 AM8 取颜色 a=b=1 的 unmasked 顶项，带新的实际标记；
不是 AM2 的 centered 原包。没有额外 a₀/b₀ 行数要再估：它们已在
CG1–CG7 的完整容斥前合计。不从一个固定子盒的界推出该等式。

## CG4. 有符号标记的低／高导子适配

高部使用 AM5 的真实完整单位层：h=(e',m)、e'=hA₀、m=hZ，
只对 (n,q')=1 作 n=fx、q'=fy 的容斥。保留
(x,fhA₀)=(y,fhA₀)=1、(Z,A₀)=1 等原条件，不新增 (Z,f)=1。
β^μ 只在高部作为模数行乘子，用 |β^μ|≤τ(e')。
长 x 列和 yZr 产品列的共同系数与 AM5 完全一致。
这里用 [Conrey–Iwaniec–Soundararajan (1.6)](https://arxiv.org/pdf/1105.1176)
所述普通 primitive hybrid large sieve，不使用渐近大筛定理。

低部按 AM6 固定 F₀=hℓdfl，使 e'=F₀C、(F₀,C)=1。
原 j、X、Y 的共同列以及平方自由 C 列的禁因子 D₀=flhkZℓ 均保留。
其中 (Z,fl)=1 由 e'/h 强迫，不因 unmasked 改写而删去；
不能补入 (C,j)、(C,X) 或 (C,Y)。
每个标记除数唯一写成 d_mark=d₁d₂，d₁|F₀、d₂|C；
再令 C=d₂X₀，保留 (d₂,X₀)=1。于是
\[
 E\le F_0X_0/d_1<2E,\qquad
 \mu(d_{\rm mark})=\mu(d_1)\mu(d_2).                 \tag{CG8}
\]
新增两个符号都在固定 split 外，不产生 μ(X₀)。
原 C 列仍由 μ²(X₀)/φ(X₀) 和原字符／时间因子组成，
φ(C)=φ(d₂)φ(X₀)。原 E 壳与 dyadic 支持的交集只是单个 X₀ 区间，
其单变量 BV 可作分部求和；不是未支付的联合硬边缘。

AM7 的实际对数相位指数对 (κ,λ)=(1/62,57/62)、δ=3/31 因而仍适用；
其解析输入参见 [Robert §5.1–5.2 (20)](https://perso.univ-st-etienne.fr/rool6510/robert-2015-indag.pdf)。
先保留平方除数 u 的 (u,D₀d₂ℓ)=1，再做单位容斥和重叠 lcm，
不用错误的乘积或截断平方除数。令 H₀=max(1,E'/E)，则
\[
 \sum_{d_2\lesssim H_0}\frac{d_2^\delta}{\varphi(d_2)}
 \ll_\epsilon H_0^{\delta+\epsilon},\qquad
 \sum_{d_2\lesssim H_0}\frac1{\varphi(d_2)}
 \ll_\epsilon H_0^\epsilon.                          \tag{CG9}
\]
d₁ 仅有除数函数个数；取模后的 μ(d₁)μ(d₂) 不改变这些费用。
先付 H₀^δ，再用 \( (T/E')^\delta H_0^\delta\asymp(T/E)^\delta\)；
不可提前把 E' 换 E 而漏掉标记费用。

具体地，对 E'≥E 的一个自然壳，Q'=S/E'，高部四项为
\[
 \mathcal D_{200}T^\epsilon
 [T+T^2/E'+T^{5/2}/(E')^{3/2}
                  +T^{7/2}/((E')^2\sqrt\Lambda)].    \tag{CG10}
\]
低部为
\[
 \mathcal D_{200}T^\epsilon
 [T^{7/2}/(E')^2+T^{5/2}/(E')^{3/2}
       +T^{5/2}/(E')^2+T^{3/2}/(E')^{3/2}]
 [T^{1/62}(T/E)^{3/31}\Lambda^{3/2+6/31}
                         +T^{-1}\Lambda^{3/2}].     \tag{CG11}
\]
这保留了 Q'<T 的时间均值项。低 ℓ<Λ 与高 ℓ≥Λ 是同一完整角色
展开的严格互补；principal ℓ=1、非单位频率和全部 Gauss 标量均在。

AM8 的无限环证明原样适用于 a=b=1：非零 reciprocal 频率
|k|≍vT/K，真实非空行只计 O(vT/(Kd))，不补 +1；
十二次 y-IBP 付 v^−12，除数与行数的增长 v^(1+δ+ε) 可和。
高部 Mellin 环 (1+τ/T)^−12 与双对偶端的 s₀^−10 或
log⁸(1/s₀)，支付四大筛项至多一次幂及除数 ε 幂的增长。
先保留无界频率中的禁因子 ε 幂再求和。实际剖面的68阶导数和
低部／尾部所需导数均由同一 D200 支付，不把范数重复相乘。

## CG5. 零频、轴与模1的单独核对

CG7 是单独的 unmasked 顶项。它的原 v-Poisson 零频 k=0
**没有** AM5 完整三色乘子的 q'|m 限制，所以不能照抄 AM18 的
稀疏性。保留全部正 m，由
\[
 |J_0|\ll\mathcal D_{200}T\sqrt{K/M}\,T^{-12}
\]
及 R·E'·Q'·M 行数、唯一外顶系数 Q'，得到
\[
 \mathcal D_{200}T^{3/2+\epsilon}Q'T^{-12}
 \ll\mathcal D_{200}T^{9/2-12+\epsilon}.              \tag{CG12}
\]
这里用 Q'≤N，不隐去一个模数；负／正非零频的全尾在 CG4。

反之，辅助原格 V=0 时同余确实迫使 q'|m，且原顶系数 q'
恰抵消 m 的稀疏性，AM19 的 a=b=1 费用为 T^(1+ε)，不是 T/q'。
它已在 CG7 全格中，不再减去。低部 principal 的内部 reciprocal
零 r=0 是第三种零项，费用 D200 T^(9/2-12+ε)/E'；ℓ>1 的该项
由 primitive 零延拓为零。q'=1 整个无约束格也不为空，
用 FD12 模1界和完整外层计数为 O(D200 T^(1+ε))。
这些分别核对的项不与全式重复相加或删除。

取 \(\Lambda=\max(2,T^{5-4\eta})\)。CG10–CG11 在 E'=E 最大，
最坏低指数为 \(749/62-(275/31)\eta\le1\)，等价于
η≥687/550。左端高四项为 (1,413/550,689/1100,1)，低部第二项
为2/275；CG12 及其余边项在预算内。E' 仅有 O(log T) 个自然壳，
因此补轴后的 raw 满足
\[
 |\mathscr R_E|\ll_\epsilon\mathcal D_{200}T^{1+\epsilon}
       \quad(687/550\le\eta\le5/4).                  \tag{CG13}
\]

## CG6. 实际 principal 的 Ramanujan 标记与正 m 质量

CG5 第二行必须独立恢复，不能把旧 FD6 只改变量名。
置 v=g w、e'=eg、l=q/g，则 (w,l)=1、s=e'l；
不添加 (w,g)=1。μ(e)μ(q)=μ(e')μ(l)。
定义含原 q>1 条件的真实标记
\[
 \mathfrak c_{E,l}(e';m)
 =\sum_{\substack{g\mid e'\\E\le e'/g<2E\\gl>1}}c_g(m).
\]
补轴后、以被减的符号定义的 principal 正是
\[
 \mathscr P_E=
 2\sum_{e',l,n,m}
 \frac{\mu(e')\mu(l)\mu(n)B_0}{\sqrt{ns}\,s}
 \frac l{\varphi(l)}1_{(m,l)=1}\mathfrak c_{E,l}(e';m)
 \sum_{(w,l)=1}A_m^{e',s}(w).                        \tag{CG14}
\]
保持 (e',l)=(n,e'l)=1 与 m>0；原完整 centered 为
\(\mathscr C_E^{\rm common}=\mathscr R_E-\mathscr P_E\)。

FD8–FD13 的 actual 格界对每个固定 e',l,n,m 一致：
\[
 \left|\sum_{(w,l)=1}A_m^{e',s}(w)\right|
 \ll\mathcal D_{200}\frac T{\sqrt{MK}}\tau(l).        \tag{CG15}
\]
它来自先用真实核非驻相付连续零频，再对任意整数格 Poisson，
最后完整单位容斥。包括 l=1、很短／很长的 w 尺度以及每格 w=0；
不在容斥前删零点。由于 e'≤s≤N、K≲T，FD 的固定阶零频界一致。

对每个正整数 g，包括 g>M，Ramanujan 除数恒等式给
\[
 \sum_{1\le m\le2M}|c_g(m)|
 \le\sum_{d\mid g}d\lfloor2M/d\rfloor
 \le2M\tau(g).                                      \tag{CG16}
\]
这是正整数倍数计数，没有虚构 +1；若加入 m=0，该理由不成立。
先对每个 m 用一致 CG15，再对 m 和 g 求和，得到
\(\sum_{g\mid e'}\sum_m|c_g(m)|\ll_\epsilon MT^\epsilon\)。
原 (m,l)=1 只在这个绝对上界中放宽，未在等式中删除。

一个 E'、L'=S/E' 壳的全部费用于是为
\[
 \mathcal D_{200}T^\epsilon
 \frac{R E'L'M}{\sqrt{RS}\,S}\frac T{\sqrt{MK}}
 =\mathcal D_{200}T^{1+\epsilon}\sqrt{\frac{RM}{SK}}
 \ll\mathcal D_{200}T^{1+\epsilon}.                  \tag{CG17}
\]
l/φ(l) 及其余因子只有除数函数费用。全部 E' 自然壳再付 log T；
此 principal 估计本身无需 η 下限。它没有借用全局 PT 主项，
也不是另一条 fixed H/L 互反后的新主角色。

## CG7. 合成结论、真实新增支持与未付范围

CG13 与 CG17 合在**同一精确** CG4 中证明
\[
 |\mathscr C_E^{\rm common}|
 \ll_\epsilon\mathcal D_{200}T^{1+\epsilon},
 \qquad 687/550\le\eta\le5/4.                        \tag{CG18}
\]
包含全部只整除 h／只整除 δ 的 canonical 分配，不再限于 FP3。
新增来自它们在平方前完整重组；不是逐 allocation 用旧界再少算行数。
不由 CG18 推出任意固定 a₀/b₀/q/H/L 子盒同界。

给出无限的原整数支持，而不声称任意权积分非零。令 Y→∞，
选互异素数 a₀≍Y^50、b₀≍Y^50（使用分离的倍长区间）、q_c≍Y^863，
设 X=(8a₀b₀q_c)^(229/321)，取素数 X<e<2X。
置 s=a₀b₀eq_c、R=S=s、N=8s、T=N^(1/3)≍Y^550，
M=K=√T、E=T^(687/550)。精确有
\[
 e/E=(e/X)^{321/550}\in(1,2).
\]
取 n 为 (s,2s) 内素数，原 h=a₀e、δ=b₀e、x=3√T/4。
大 Y 时原正 x/y、内部 mollifier、gcd、HL≤RS/T 支持成立；
gcd(s,h,δ)=e，gcd(s,hδ)=a₀b₀e，两个额外 allocation 都增长。
这严格超出 #546 的 a₀=b₀=1。

有限例：T=10^6、M=K=1000、e=32000011、a₀=2、b₀=3，
q_c=10007·10009、s=19230738706564158、n=19230738706564183，
h=2e、δ=3e、x=750。脚本精确验证这些整数的原 gcd、素数性、
E 壳及正 x/y、N/2 内部支持。

交付仅限 q₀=1、内部平衡尺度、这个 e 区间的完整 h/δ 包。
更小或更大的 e、本域之外的尺度、q₀ 外壳、AFE 尾和全 signed gate
均未在本文合计；没有证明任何固定零点自由半平面。辅助有限回归
不替代解析指数对、大筛和统一尾证明；没有新增 Lean。
