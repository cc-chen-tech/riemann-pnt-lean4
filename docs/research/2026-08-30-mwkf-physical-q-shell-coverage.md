# 恢复物理尺度：一般尺度转移与 q 壳内的指定区域

白话结论：上一轮一般 q 的局部公式没有错误，但给出的
q=T^χ、χ>0 且 R=S=T³ 的例子不满足原 N=T³ 问题的
qR,qS≲N，不能算原参数多面体的非空覆盖。本节明确更正
这个范围，并把 R,S 随 q 缩小以及原来的 1/q 外权一起恢复。
在三个具体的原问题内部区域，包含整个 q 壳的指定 κ/B
子 packet 总贡献确实为 O(T^{1+ε})。其中一例仍有 B>T。
**这不是整个 q 壳的全部 off-diagonal，也未控制 canonical
zero Gram、两个 reflection mixed 项或完整 signed operator。**

推导沿用 [GQ](2026-08-30-mwkf-all-e-general-q-coverage.md)
的全 e 单位掩码、[GP](2026-08-30-mwkf-variable-kappa-coverage.md)
的完整 j 族和 [JT](2026-08-30-mwkf-joint-type-ii-density.md)
的精确 symbol。这里没有新增通用 Möbius 相关性假设。

## 1. 一般尺度与不能省略的两个长度

先限于 R≥S 这一取向，记
\[
 \alpha=R/S,\quad X=R/K,\quad P=K_{\min}K_{\max},\quad
 Z=RP/S,\quad J=Z/K,\quad F=ZX/S=\alpha J,
 \quad C=HL/R,\quad \rho=HLP/S^2.                 \tag{PQ1}
\]
本节 F 是 n 频率长度，截断窗口另记 F_cut；L 仍是原 δ 尺度。
所有尺度为 T 的固定幂；Kmin≥1、Kmax≥Kmin，X≥1、J≳1，
且 Z≥T^δ、K/α≥T^δ，δ>0 固定。自然非零双 Fourier 区域给
ρ≲T^ε。核满足 PT3/JT4 的统一光滑导数条件，保留原 hδ 耦合，
不能以此假定原硬截断或独立 AFE 尾也已处理。

恢复所有 e/A/b 分片，仍令 M=Ae、B=eb、e=(M,B)。GQ1 的
双射不变：M,B 平方自由，(B,q₀)=1，q₀=rad(q)。置
g=(M,q₀)、v=q₀/g、模数 \(\mathcal L=Mv\)。固定 g 后才改变 M。
幅度为
\[
 \frac{w(t)}x\widetilde G(tKM/R,x,kH/(Sx),lL/(Sx))\chi(Sx/B).
\]
M≈X、e≲X 给 d≈S/e≳K/α，故 d=1 在充分大 T 时为空；
K>2 也排除 κ=e=1。这里不能把 GP 中的 d≳K 原样用于 R>S。
U=1 时正整数没有 Type 过渡项。原 B<2S 支撑继续保留。

全除数重组后的载波仍为 e(−nkl/(jBv))，系数仍为
\(C\mu(B)\mu(v)\kappa_{\mathcal L}(n)/(BMv|j|)\)。但精确参数是
\[
 z_0=KMkl/S,\quad
 \eta=\frac jJ\frac XM\frac P{kl},\qquad
 \sigma=\frac n{BFv}\left(\frac XM\right)^2\frac P{kl}.
                                                               \tag{PQ2}
\]
因此 |j|≈J 而 |n|≈BFv；**除非 R=S，不能用 J 代替 F。**
完整 Ψ_{M,B,j,k,l}(n/(BFv)) 的支撑满足 c≤|n/(BFv)|≤C₁，
c>0 固定，Ψ(0)=0。Λ=|z₀|≈Z；M/l 的归一化微分仍分别为
Λ∂Λ−η∂η−2σ∂σ 与 Λ∂Λ−η∂η−σ∂σ，加实际核坐标的导数。
JT4 的精确坐标变换因而继续给统一混合导数；没有丢弃驻相误差。

## 2. 密度及联合 B/斜率采样的全尺度界

在每个 M∈[X′,2X′]、X′≈X 的光滑支持片上，仅对
g|q₀、g≤2X′ 的活跃层令 M=gm。平方自由均值长度 X′/g≥1/2，
单位模数仍是 q₀，不是 q₀B。GQ7 的式子只将 n/(BJv)
替换为 n/(BFv)。GU6 支付整数端点、过渡与大除数连续延伸，
不向空 g 层人为添加均值。GQ8 的两项质量仍是
\[
 \sum_{0<|n|\le N_1}|\kappa_{q_0}(n)|\delta_{q_0}(n)
 \ll q_0T^\varepsilon,\qquad
 \sum_{0<|n|\le N_1}|\kappa_{q_0}(n)|D_{q_0}(n)
 \ll N_1^{3/2}T^\varepsilon.                       \tag{PQ3}
\]
第二式保留 D_{q₀}(n) 中的 (d,q₀)=1，不能附加大模数 +1。
完整 n/B/j 与 g 除数成本给算术密度
\[
 |\mathcal M_{K,q}(Y)|\ll CP T^\varepsilon
       =\rho S/\alpha\ T^\varepsilon\ll S T^\varepsilon.
                                                               \tag{PQ4}
\]
ε 在最后一步按通常方式重命名；该密度不是原 canonical zero Gram。

对同一个均值误差先完成 l。由于 |n/(jv)|≈FY/J=αY，单调
B 采样现在为
\[
 \sum_{Y\le B<2Y}\sum_{\omega\in\mathbb Z}
 (1+K_{\max}|\omega+nk/(jBv)|)^{-L_0}
 \ll_{L_0}Y/K_{\max}+\alpha K_{\min}.              \tag{PQ5}
\]
证明：近 ω 共 O(αKmin) 个；每个单峰积分为
O(Y/(αKminKmax))，另付一个整数端点 O(1)。远 ω 尾由
Y/Kmax 支付。αKmin≥1，critical 的正下界不能删去。
相位在固定 g 上与 m 无关，混合 m/l 导数保持所需 Fourier 衰减。

采样后才扩大 n 到 0<|n|≲FYv，用 PQ3；剩余 g 因子仍为
\(\sqrt g\,v^{3/2}/q_0=\sqrt{q_0}/g\)。故
\[
 |\mathcal E_{K,q}(Y)|\ll CPX^{-1/2}F^{3/2}\sqrt{q_0}T^\varepsilon
 \min\{Y^{3/2},\ Y^{3/2}/K_{\max}+\alpha K_{\min}Y^{1/2}\}.
                                                               \tag{PQ6}
\]
两种估计针对同一个误差，不能相乘 saving。这里是恢复所有 e
后的联合和，不是固定 e 子和；全 B 单位限制仅在非负上界中删除。

## 3. Primitive 共振与有限非零补集

全 n 完成的 Jacobian 是 **Fv**。它与外面的 1/v 消去后，得到
\[
 C\sum_M\frac{\mu(M)}M
 \sum_{B\approx Y\atop(B,q_0)=1}\mu(B)
 \sum_{k,l}\sum_{|j|\approx J}\frac F{|j|}
 \sum_{(h,Mq_0)=1}
 \widehat\Psi_{M,B,j,k,l}\bigl(F(Bh/M+kl/j)\bigr).
                                                               \tag{PQ7}
\]
h 是新的 Fourier 标签，不是原 AFE 的 h；Ψ(0)=0 允许加回 n=0。
完整 symbol 保留所有真实支持与符号。

Δ=jBh+Mkl=0 仍由 d=(|j|,M)、M=dM₁、j=dj₁、B=M₁r、
j₁rh=−kl 参数化，另筛选 (B,q₀)=(h,Mq₀)=1，特别是 g|j。
固定 M,k,l，联合 (j,r) 的数量≤τ(M)τ(|kl|)²（critical 固定
j 符号）。PQ7 的 F/|j|≲F/J=α 不可省略。因此
\[
 |\mathcal M_{\rm prim,K,q}|\ll CP\alpha T^\varepsilon
           =\rho S T^\varepsilon.                            \tag{PQ8}
\]
这是所有允许 B/e/j 的共振界，但不等于 PQ4，也未与原零 Gram
或 diagonal 认同。不能把两个不同表示的均值重复减去。

令 F_cut=T^δ₁，δ₁>0。在 PQ7 保留
\(0<|F\Delta/(jM)|\le F_{\rm cut}\) 即为有限 signed 补集。
对应 h 的字面闭端点是
\[
 \left\lceil\frac MB(-F_{\rm cut}/F-kl/j)\right\rceil
 \le h\le
 \left\lfloor\frac MB(F_{\rm cut}/F-kl/j)\right\rfloor .
                                                               \tag{PQ9}
\]
这给一个可直接形式化的有限矩阵，保留 µ(M)µ(B) 及单位掩码。
在 PQ4/PQ6 达到 S 预算的区域，其实际 Möbius 向量对上的
非零补集也由三角不等式达标；**没有证明矩阵零行和/零列和，
没有证明所有向量上的目标算子范数**。

## 4. 变换尾与未包含的物理边界

以下均是 normalized core 的成本；L₀ 为可任意选大的衰减阶。

| 项 | 保守全外层上界，另容许 T^ε |
|---|---|
| JT6 非critical 全 j/ℓ，包括 j=0 | CP X Z^{1−L₀}(K+Z) |
| 原 quotient ℓ=0、全 j | CP K X Z^{−L₀} |
| 新 l-Fourier 窗口外 | CP X F Y q₀ F_cut^{1−L₀} |
| PQ7 新 h-Fourier 窗口外，所有 B | CP(FS+X log(2S))F_cut^{1−L₀} |

第一行由每个 e,A,b 的 C_e/D=HL/(RS)，全部 allocation 数
≪XS，再付 #(k,l)≪P 得出。第二行的 b 调和成本与完整 κ
长度 K 均保留。第三行用 |κ_𝓛(n)|≤𝓛 和 #n≲FYq₀；窗口
|Kmax(ω+nk/(jBv))|≤F_cut 在固定 g 上不依赖 m。
最后一行单行格距是 FB/M，尾为
O((1+M/(FB))F_cut^{1−L₀})；完整 j 的 F/|j| 总质量≪F，
故恢复 B 后恰得 FS+X log(2S)，不是 JS+X log(2S)。

紧支撑光滑 l 分片的零延拓没有硬端点；B 用半开 [Y,2Y)，
Fourier 窗口含等号。上述所有尺度为固定幂且 Z≥T^δ，故取
L₀ 充分大，连同所需的多项式外权也可支付任意幂次小的变换尾。
两个 Fourier 窗口是同一个 core 的不同表示，不重复作主项。
K/α 无正幂余量、d=1、κ=e=1、零斜率及独立 AFE/reflection
物理尾不由本节自动控制。原 B_q 的 r=1 纠正在 R/2>1 时为空；
若不满足，必须保留该精确纠正。

## 5. 原 N=T³ 中非空的内部 q 壳

原问题的平方自由 q∈[Q,2Q)，Q 为正整数，Q≈T^γ。取
\[
 R=S=N/(8Q)\asymp T^{3-\gamma},\quad
 M_z=K_z\asymp T^u,\quad
 H\asymp S/T^u,\quad L\asymp RT^{u-1},\qquad 0\le u\le1/2.
                                                               \tag{PQ10}
\]
M_z,K_z 是原 AFE 尺度，不能与 M=Ae、κ 尺度 K 混同。
此时 K_zM_z≲T，K_zS/(M_zR)≈1，原 (5.8)/(5.12b) 给
HL≈RS/T，双 Fourier 尺度 Kmin≈T^u、Kmax≈T^{1−u}，P≈Z≈T。
常数可缩小以满足保留区间的端点；指数可行性另须
3−γ−u≥0、2−γ+u≥0。所列覆盖例子中 H,L 均为正幂。

对所有 q<2Q 和 r,s≤2R，有 qr,qs≤N/2。因此原
p_N(qr)p_N(qs) 在整片支持上光滑，可并入实际 G，其每个
正阶归一化导数 O(1/log N)，零阶 O(1)。q 的变化不会破坏
统一范数。这里**只覆盖原 mollifier 内部**，没有把 n=N 的
截断角点假定为 C∞。原精确核 (5.13b) 的参数在这些箱中满足
Tλ₀≈1、ω₀≈1、χ₀≈T^{2u−1}≲1，故 (5.14) 的导数界适用。

再令 K≈T^ν、0<ν≤min(1,3−γ)，Y≈T^β、0≤β≤3−γ。
q₀=q≈Q。PQ6 的三个绝对 normalized 指数恰为
\[
 e_0=3-\nu+3\beta/2,\qquad
 e_{\rm int}=2+u-\nu+3\beta/2,\qquad
 e_{\rm lattice}=3+u-\nu+\beta/2.               \tag{PQ11}
\]
γ 在它们的前因子中抵消，但**目标降为 s=3−γ**，不能仍用3。
密度与共振都为 O(T^{s+ε})。因此整个指定子 packet 的充分区域是
\[
 \boxed{\quad \beta\le\frac{2(\nu-\gamma)}3
 \quad\text{或}\quad
 \left[\beta\le\frac{2(1+\nu-u-\gamma)}3\quad\text{且}\quad
       \beta\le2(\nu-u-\gamma)\right].\quad}                  \tag{PQ12}
\]
在这些区域，实际 q 壳求和使用原 (5.15)，不另添 Q 个等大项：
\[
 \sum_{Q\le q<2Q}\mu^2(q)\,
   \left|\frac{2T}{qS}\mathcal P_{K,q}(Y)\right|
 \ll T^{1+\varepsilon}\sum_{Q\le q<2Q}\frac{\mu^2(q)}q
 \ll T^{1+\varepsilon}.                                      \tag{PQ13}
\]
最后的常数已吸收前面的隐常数；有限不等式
Σ_{Q≤q<2Q}µ²(q)/q≤1 因恰有 Q 个整数且每项≤1/Q。
这证明该 q 壳中**已覆盖 κ/B 子族**的总成本，不是该 q 壳所有
off-diagonal 的成本。随后只可对已覆盖的对数多个 dyadic 块相加。

| γ | ν | u | β | 目标 s | e₀ | e_int | e_lattice | q 壳误差指数 |
|---|---|---|---|---|---|---|---|---|
| 1/5 | 1 | 1/2 | 3/5 | 14/5 | 29/10 | 12/5 | 14/5 | 1 |
| 1/5 | 1 | 0 | 6/5 | 14/5 | 19/5 | 14/5 | 13/5 | 1 |
| 1/2 | 1 | 0 | 1 | 5/2 | 7/2 | 5/2 | 5/2 | 1 |
| 1/5 | 1 | 1/2 | 4/5 | 14/5 | 16/5 | 27/10 | 29/10 | 11/10 |

前三行是原参数多面体中非空尺度的覆盖；第二行有 B>T。
最后一行是仍未覆盖的实际尺度见证：当前界只到 T^{11/10+ε}，
不是余项有这么大的下界，也不能据此断言原命题失败。

## 6. 有限命题、验证范围与剩余目标

配套有限接口不输出全问题 coverage 标志：

1. `all_scale_critical_parameters` 用有理数返回 PQ1/PQ2，检查
   F=αJ 及两项紧支撑比率，保留一般 R/S、n/v 和非零符号。
2. `all_scale_error_exponents` 的一般账本：这里 r,s,hl,ν,u,v,β,χ
   分别为 R,S,HL,K,Kmin,Kmax,Y,q₀ 的 log_T 指数（此项的 v
   是斜率指数，不是整数 q₀/g）。令
   c=hl+u+v−r、x=r−ν、f=2r+u+v−2s−ν，
   A=c−x/2+3f/2+χ/2，则三误差为
   A+3β/2、A+3β/2−v、A+r−s+u+β/2；密度 c，共振 c+r−s。
   域条件 r≥s、r−s<ν≤min(r,r+u+v−s)、hl+u+v≤2s 等
   显式检查，不把端点失败悄悄推广为定理。
3. `physical_q_shell_exponents` 返回原独立多面体检查器的
   (r,s,m,k,ell,h,kappa)=(3−γ,3−γ,u,u,2−γ+u,3−γ−u,γ)，
   以及 PQ11 和物理指数 1+min(e₀,max(e_int,e_lattice))−s。
4. PQ9 的闭窗口、primitive 单位条件和 Δ 枚举是有限和命题；
   测试还单独验证一个 F≠J 的 Schwartz 完成，其 Jacobian 为F。

这些计算守卫检验代数、指数、支撑和归一化，不证明解析尾或
原 signed operator 的范数。GQ 正幂 q、R=S=T³ 的旧例子被
明确降为独立光滑 core 的尺度例子；本节没有撤销 GQ 的局部
恒等式，而是纠正其物理适用范围并补出 PQ10–PQ13 的实际转移。

剩余问题仍包括 PQ12 外的双 Möbius 补集、K/α 边界、其他
原尺度与硬 mollifier 边界，以及回到同一个含 canonical zero
Gram、非零频补集、两个 reflection mixed 项和独立物理尾的
signed operator。**完整 coupled-kernel gate 与 twisted moment
的无条件目标均未证明。**
