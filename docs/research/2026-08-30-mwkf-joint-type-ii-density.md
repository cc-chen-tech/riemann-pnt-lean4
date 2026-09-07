# Type-II 的全除数重组：精确相位、算术密度与短 b 覆盖

白话结论：先完成 κ 和无符号 quotient，再把全部互素除数 v
重组，确实能提取一个显式、可控的算术密度。平衡顶层、e=q=1、
U 为固定对数幂时，剩余平方自由误差也足以覆盖整个
b≲T^{2/3} 的 Type-II 分片，不必逐条估计 Möbius 相关。
**长 b、其他 e,q、原 canonical zero Gram 与统一 signed operator
仍有独立义务；完整 coupled-kernel gate 和 twisted moment 未证明。**

本节的密度是实际 Type-II 光滑 bulk 的算术均值，不是原 AFE
零频项或 canonical zero Gram 的新名称。它的显式部分达标，
不意味着整个原零频主项已求值。所有物理归一化沿用
[PT/IC](2026-08-30-mwkf-inverse-c-signed-roundtrip.md) 和
[JQ](2026-08-30-mwkf-joint-kappa-type-i.md)；不把 saving 相乘。

## 1. 真实 Type-II 的平滑化与完整过渡边界

令 χ 为固定光滑函数，χ(t)=0 对 t≤1，χ(t)=1 对 t≥2。
保留 SK 的 c_U(a)=Σ_{c|a,c≤U}µ(c) 及正整数 U,V。
因为 U<a≤2U 的所有真因子都≤U，有 c_U(a)=−µ(a)。
对每个正整数 n，精确地

\[
\begin{split}
 \mathrm{II}(n)
 &:=-\sum_{\substack{ab=n\\a>U,\ b>V}}c_U(a)\mu(b)\\
 &=-\sum_{\substack{cbm=n\\c\le U,\ b>V}}
       \mu(c)\mu(b)\chi(cm/U)
   +\sum_{\substack{ab=n\\U<a<2U,\ b>V}}
       \mu(a)\mu(b)[1-\chi(a/U)] .
 \tag{JT1}
\end{split}
\]

第一项称 smooth bulk，第二项称 transition boundary。边界是
正号；a=U 不出现，a=2U 的补偿为零。可在两侧同时乘
1_{(n,Q)=1}。展开后保留 (bc,Q)=1、(m,Q)=1，不给 m 添加
µ²(m)，也不假设 (b,c)=1。非平方自由父项的抵消仍属于精确和。

对实际 d≈D 权重，χ(cm/U)=χ(Dx/(bU))。其任意固定阶归一化
x,b 导数一致有界：导数非零时 Dx/(bU) 在固定紧区间，否则
χ 为常数。故它可直接并入 JQ2 的实际幅度 𝔞(t,x)，包括已有
1/x 因子及 b 的光滑 dyadic 权。bulk 支撑给 b<2D/U。
原 sharp b>V 不被删去；它不妨碍对 A 的分部求和。

IC2 的外系数是 −Cµ(A)，C=HL/(Re)。所以 JT1 的 bulk
物理系数为 +Cµ(A)µ(c)µ(b)，boundary 系数为负。
κ=e=1 的 IC/SK 独立纠正项照旧保留；K>2 的分片上它为零。
只在下文明确验证支撑时才删除 transition boundary。

## 2. 联合变换的精确相位与统一幅度

暂保留一般 e,q，置

\[
 B=bc,\quad Q=Aeq,\quad M_v={D\over Bv},\quad
 z_0={KAkl\over D},\quad \Lambda=|z_0|\asymp Z\ge1.
\]

原 (e,Aq)=1、(B,Q)=1 不动。JQ5 对每个 c,b 给出
KΣ_{v|Q}µ(v)/(Bv)Σ_{j,ℓ} I_{j,ℓ}，其中

\[
 I_{j,\ell}=\iint \mathfrak a(t,x)
   e\{z_0(t/x-\eta t-\sigma x)\}\,dt\,dx,\qquad
 \eta={jK\over z_0},\quad \sigma={\ell M_v\over z_0}.
 \tag{JT2}
\]

幅度光滑支撑于 t∈(1/2,3)、x∈(1,2)，并保留实际耦合核。
驻点条件为 x_0=1/η、t_0=−σ/η²；因此 η>0、σ<0，
j 与 z_0 同号，ℓ 与 z_0 异号。取固定光滑 critical cutoff
θ(η,t_0)，在实际驻点集合邻域等于1，支撑在
η∈(1/4,2)、t_0∈(1/4,4)。η≤0 等其余位置定义 θ=0。

在 θ 的支撑上作精确换元

\[
 y={1\over x}-\eta,\qquad
 w=t+{\sigma\over\eta(\eta+y)}.
 \quad
 {t\over x}-\eta t-\sigma x=-{\sigma\over\eta}+yw,\qquad
 \left|{\partial(t,x)\over\partial(w,y)}\right|
       ={1\over(\eta+y)^2}.
 \tag{JT3}
\]

令
\[
 \mathfrak A(w,y)=
 {\,\mathfrak a(w-\sigma/[\eta(\eta+y)],\,1/(\eta+y))\over(\eta+y)^2}.
\]
原 x 支撑保证 η+y∈[1/2,1]；先在其固定邻域乘平滑 cutoff
再零延拓，避免在极点处书写未定义表达式。所有所需参数
导数仍为 O(T^ε)，w,y 支撑一致紧。

采用负号 Fourier 约定，记只对 w 的变换为
\(\widehat{\mathfrak A}_w(\xi,y)\)。不截断任何渐近展开，精确有

\[
 I_{j,\ell}={e(-z_0\sigma/\eta)\over\Lambda}\mathcal W_0,\qquad
 \mathcal W_0=\int_{\mathbb R}
   \widehat{\mathfrak A}_w(-\operatorname{sgn}(z_0)u,u/\Lambda)\,du.
 \tag{JT4}
\]

证明：先完成 w 积分，再置 u=Λy。变换在第一个变量上
一致 Schwartz；对 η,σ 及 Λ∂_Λ 反复微分，积分仍绝对收敛，
各固定阶导数为 O(T^ε)。这给出的是精确 symbol，不只是
stationary-phase leading term。可比较一般参数统一的
[Kıral–Petrow–Young 方法](https://doi.org/10.5802/jtnb.1072)，
但本节的有理换元与导数证明自包含，不调用其渐近误差。

置 𝒲=θη𝒲_0，由 η=|j|K/Λ 得 critical 项恰为

\[
 {K\mu(v)\over Bv}\theta I_{j,\ell}
  ={\mu(v)\over Bv|j|}\mathcal W
       e\!\left(-{\ell Akl\over jBv}\right).
 \tag{JT5}
\]

即使需要 leading term，它也只是
𝒲_0=𝔞(t_0,x_0)/η²+O(T^ε/Λ)；本文不删除该误差，
所以没有恢复物理外层后漏乘数量的问题。

### 所有非驻点、零模与频率截断

ℓ=0 的全部 j 是 JQ6 连续密度，大小
O_J(T^ε K B^{-1}(1+Z)^{-J})，不是 canonical zero Gram。
对 ℓ≠0，1−θ 所在区域的相位梯度满足固定下界，分部积分给

\[
 |(1-\theta)I_{j,\ell}|
 \ll_L T^\varepsilon\Lambda^{-L}
  \left(1+{|j|K\over\Lambda}
           +{|\ell|M_v\over\Lambda}\right)^{-L}.
 \tag{JT6}
\]

这里包含 j=0 以及所有远 j,ℓ。L>2 时完整双采样至多
(1+Λ/K)Λ/M_v；ℓ≠0 的采样没有整数 +1。因此固定 v 乘上
K/(Bv) 后的总成本为
O_L(T^ε Λ^{1-L}(K+Λ)/D)。对所有 v 使用除数界，再付实际
A,b,c,k,l 等有限外层。只要 Z≥T^ζ、ζ>0 固定，且全部尺度为
T 的固定幂，选择足够大的 L 即可使总非驻相余项任意幂次小。
本节新增覆盖均满足这些条件；Z≈1 时不宣称 rapid。

θ 部分已经具有有限 j,ℓ 支撑：
|j|≈Z/K、0<|ℓ|≈ZBv/D；小于1的整数区间可能为空。
若仍选择矩形截断，必须使用 JQ14 的尾；若用下文共同 n
截断，则须把它按 n=(A/v)ℓ 提升到每个 v，不能套用同一个
ℓ 截断后宣称全除数恒等式精确。连续密度、JT6 和过渡边界
共同组成 critical 项的完整补集。

## 3. 全 v 先重组，不能停在独立 v-shell

以下限定 e=q=1，所以 Q=A、D=S，µ(A) 令 A 平方自由。
取实际 A 分片支撑 A∈[X,2X]，X≈R/K；其他固定倍数支撑可用
固定个数的分片覆盖。**先恢复全部 v|A**，若先前分了 v-shell，
也须先把分片权重加回1。记

\[
 a_0=A/v,\quad n=a_0\ell\ne0,\quad g=(A,|n|).
\]

关键是 ξ=ℓD/(Bv)=nD/(BA)，且
z_0=KAkl/D、η=jD/(Akl)、σ=nD²/(KB A²kl)。
JT4 的精确 symbol 因而只依赖 A,n,b,c,j,k,l，完全不依赖
v 的分配；cutoff θ 及 χ(Dx/(bU)) 也如此。固定 n 时
A 的归一化微分作用为
Λ∂_Λ−η∂_η−2σ∂_σ，加上实际幅度 A/X 的有界导数。
所以 A↦𝒲 在 [X,2X] 上的归一化 BV 范数为 O(T^ε)。

由 µ(A)µ(v)=µ(A/v)，全除数系数精确变为

\[
 \mu(A)\sum_{\substack{v\mid A\\ A/v\mid n}}{\mu(v)\over v}
  ={1\over A}\sum_{d\mid(A,n)}\mu(d)d
  ={\mu(g)\varphi(g)\over A}.
 \tag{JT7}
\]

它也等于 µ(A)c_A(n)/A，但不等于其绝对值或一个恒零系数。
记 P=K_1K_2、C=HL/R，则一个完整 critical smooth bulk 为

\[
 \mathcal B_{\rm crit}^{II}
 =C\sum_{\substack{c\le U\\b>V}}\mu(c)\mu(b)
    \sum_{k,l}\sum_{j\ne0}\sum_{n\ne0}
 {e(-nkl/(jbc))\over bc|j|}
 \sum_{\substack{A\ge1\\(A,bc)=1}}
   {\mu^2(A)\over A}\!
    \sum_{d\mid(A,n)}\mu(d)d\,
           \mathcal W_{b,c,j,k,l,n}(A/X).
 \tag{JT8}
\]

原 hδ 信息仍在 𝒲 中，没有把 k,l 的实际核换成独立任意系数。
每个和在 critical 支撑下有限；统一取
0<|n|≲ZbcX/D、|j|≈Z/K 即可。µ(b)µ(c)、单位条件
(A,bc)=1 和物理 C/(bc|j|) 全部保留。

## 4. 带全部单位条件的平方自由均值

对任意非零整数 n、正整数 B 和支撑于 [1,2] 的 C¹ 函数 W，
设 \(\mathcal N(W)=\|W\|_\infty+\|W'\|_\infty\)，并定义

\[
 c(B)={1\over\zeta(2)}\prod_{p\mid B}{p\over p+1},
 \qquad
 \delta_B(n)=\prod_{\substack{p\mid n\\p\nmid B}}{1\over p+1}.
\]

X≥1、B,|n|≤T^{C_0} 时，初等地

\[
\begin{split}
 &\sum_{\substack{A\ge1\\(A,B)=1}}{\mu^2(A)\over A}
          \sum_{d\mid(A,n)}\mu(d)d\,W(A/X)\\
 &\quad=c(B)\delta_B(n)\int_1^2 W(x){dx\over x}
 +O_{\varepsilon,C_0}\left(
  T^\varepsilon\mathcal N(W)X^{-1/2}
       \sum_{d\mid |n|}\sqrt d\right).
 \tag{JT9}
\end{split}
\]

证明分三步，所有边界均保留。

1. 交换有限除数和，A=du，平方自由性给精确恒等式
   \[
    \sum_{\substack{d\mid n\\(d,B)=1}}\mu(d)
       \sum_{\substack{u\ge1\\(u,dB)=1}}
                {\mu^2(u)\over u}W(du/X).       \tag{JT10}
   \]
   µ(d)=0 的项自动为零；其余 (d,u)=1 不能省略。

2. 由 µ²(u)=Σ_{r²|u}µ(r) 及单位整数的 floor 计数，对 Y≥1
   \[
    \sum_{\substack{u\le Y\\(u,Q)=1}}\mu^2(u)
      =c(Q)Y+O(\tau(Q)\sqrt Y).
   \]
   内层单位计数是 Yφ(Q)/(Qr²)+O(τ(Q))，延伸 r 和的尾为
   O(√Y)。对 W(du/X)/u 分部求和，若 X/d≥1/2，误差为
   O(τ(dB)𝒩(W)√(d/X))。若 d>2X，离散段为空，减去其
   连续主项的大小≤𝒩(W)，也由同一界支付。特别地
   X<d<2X 可能还有 u=1，不能把这个过渡区称为空段。
   由于 dB 为 T 的固定幂，除数函数可吸收进 T^ε。

3. 其主系数完全因子化：
   \[
    \sum_{\substack{d\mid n\\(d,B)=1}}\mu(d)c(dB)
       =c(B)\prod_{\substack{p\mid n\\p\nmid B}}
             \left(1-{p\over p+1}\right)
       =c(B)\delta_B(n).
   \]
   这包含 d>X 的主项及其已付误差，未把有限截断误当作完整
   Euler product。

这是带显式误差的均值定理，不仅是 IC 的形式往返。
不对 n=0 使用 JT9：此处 n≠0 来自已经独立结账的 ℓ≠0。

### 密度在整个 n 轴上只有亚幂次总质量

对任意固定 C_0 和 ε>0，B,M≤T^{C_0} 一致有

\[
                  \sum_{1\le |n|\le M}\delta_B(n)
                       \ll_{\varepsilon,C_0}T^\varepsilon .
 \tag{JT11}
\]

证明：取足够小的固定 s>0。正项 Dirichlet 级数的 Euler
product 在 p∤B 处的局部因子是
1+p^{-s}/[(p+1)(1-p^{-s})]，其完整乘积收敛；p|B 的因子
至多 (1-p^{-s})^{-1}。该有限乘积≪_{s,η}B^η：
先分离有限个小素数，其余逐个用
−log(1-p^{-s})≤ηlog p。Rankin 界给
O_s(M^s B^η)，再按 ε,C_0 选择 s,η，负 n 仅乘2。
不能删去 p|B 的单位修正后声称相同的精确密度。

## 5. 显式密度达标，平方自由误差新增顶层覆盖

将 JT9 代入 JT8，定义精确分解
\(\mathcal B_{\rm crit}^{II}=\mathcal M_{\rm sf}^{II}
+\mathcal E_{\rm sf}^{II}\)：第一项使用 JT9 的显式积分，
第二项是原 A 有限和减去该积分。依索引的实际 𝒲 仍在，
这个操作没有宣称矩阵自动具有零行和、零列和。

对 \(\mathcal M_{\rm sf}^{II}\) 使用 JT11 和统一幅度范数，
c,b 的 1/(bc) 和及非零 j 的 1/|j| 和只花对数，故

\[
 |\mathcal M_{\rm sf}^{II}|
           \ll_\varepsilon T^\varepsilon C P
           =T^\varepsilon {HL P\over R}.
 \tag{JT12}
\]

这已经包括全部允许 b、c 和全部 v 分配。平衡
R=S=T³、HL≈T⁵、P=T^p、0<p≤1 时，它是
O(T^{2+p+ε})，不超过 S=T³ 的预算。不能从复权积分及外层
µ(b)µ(c) 推出此项为正或不与其他项抵消。

接着固定 b∈[B_0,2B_0]，考虑顶层 K≈P≈Z≈T，
X≈T²、D≈T³、CP≈T³。此时 n 支撑为 0<|n|≲cb。
由有限除数交换与整数计数
\[
 \sum_{1\le n\le M}\sum_{d\mid n}\sqrt d
  =\sum_{d\le M}\sqrt d\,\lfloor M/d\rfloor
  \ll M^{3/2}.
\]
所以连同完整 b,c,j,k,l 物理外层，

\[
 |\mathcal E_{\rm sf}^{II}(B_0)|
  \ll T^\varepsilon CP X^{-1/2}
      \sum_{c\le U}{1\over c}
      \sum_{b\asymp B_0}{(cb)^{3/2}\over b}
  \ll T^{2+\varepsilon}(UB_0)^{3/2}.
 \tag{JT13}
\]

这里已经支付整个 b-shell；没有留下隐藏的 v 数量或 n 数量。
若 4UB_0<D，则过渡边界 U<a<2U、b≤2B_0 给 ab<D，
不可能碰到 d∈[D,2D]。K>2 也排除了 κ=e=1 纠正。
结合 ℓ=0 的 rapid 密度、JT6 的全部非驻相尾，得到：

> **指定分片的无条件覆盖。** 在上述实际光滑非零 k,l 核、
> e=q=1、平衡顶层上，取 U,V 为任意固定对数幂，完整
> b≈B_0>V、B_0≲T^{2/3} 的 Type-II 部分满足
> \[
>       |\mathcal B^{II}(B_0)|\ll_\varepsilon T^{3+\varepsilon}.
>       \tag{JT14}
> \]
> 这是整个 v 家族的结论；并非一个 v 行的预算。

对数多个这种 b-shell 可求和。端点 B_0=T^{2/3} 的对数损失
吸入 ε，且大 T 时 4UB_0<D 自动成立；有界 T 用调整常数处理。
此前 JQ13 逐 b 付费只给 T^{3+ε}UB_0；JT13 是新的节省。
当 b 更长，这个初等误差仍过大，本文没有关闭该区域。

## 6. 另一条可用的局部输入，以及不能直接套用的谱相位

为了核对已发表估计的覆盖，暂保留一个 v≈V_0 的 shell，
A=va_0。JT5 的载波为
\[
             e\!\left(-{\ell a_0kl\over jbc}\right),\qquad
 \mu(A)\mu(v)=\mu(a_0).
 \tag{JT15}
\]
仍有 µ²(v)、(v,bc)=1、(a_0,vbc)=1；v 不能任意取值。
固定 v,ℓ 时 a_0 的导数是
Λ∂_Λ−η∂_η−σ∂_σ，加上实际幅度的导数，故权为统一 BV。
这与固定 n 的 −2σ∂_σ 不同。

令 A_0=X/V_0，j≈Z/K、|ℓ|≈ZcB_0V_0/D；
线性频率满足 |α|A_0≈Z。若 A_0=T^a、Z=T^p、a>p>0
有固定余量，[IC7 的带单位线性行定理](2026-08-30-mwkf-inverse-c-signed-roundtrip.md)
适用。其输入是
[Basak–Robles–Zaharescu, Theorem 1.4](https://arxiv.org/html/2312.17435v2)；
互素 mask 的转移已在 IC7 证明，不将它当作免费的密度。
由于 vbc 为 T 的固定幂，符合 IC7 的多项式模数条件。

取 δ=min(a/5,(a−p)/2,p/2)，支付完整 v-shell、整数 j,ℓ
数量及其系数，得到 smooth critical bulk 的成本
\[
       T^{-\delta+\varepsilon}{\rho DZUB_0\over K}.
 \tag{JT16}
\]
a_0 长度的 1/V_0 正好抵消 V_0 个 v，不能再多记一个
v 平均 saving。在平衡 K=T^ν,V_0=T^ω,B_0=T^u 上，
a=3−ν−ω，成本指数 2+2p+u−ν−δ（U 为对数幂）；
驻相支撑另要求 u≥3−p−ω。例 p=ν=1/4、
ω=39/20、a=u=4/5 时 δ=1/8，指数117/40<3。
这只覆盖该指定 v-shell 的 smooth critical bulk。
顶层 p=ν=1 时 u≥a>1、δ≤a/5，成本严格大于3，
故该线性行估计不能替代全局 signed Type-II 工作。

另一方面，[Bettin–Chandee](https://arxiv.org/abs/1502.00769)
以及 [Wright, Theorem 2.1](https://arxiv.org/html/2604.25177v1)
处理的是带模逆的 Kloosterman fraction 及相应分离系数。
JT15 是普通线性分数，没有模逆。令 a_0 的逆为新变量时，
原来并无 (a_0,j)=1；即使另取单位部分，µ(a_0) 及区间条件
也随模数 jbc 改变，不能直接成为独立于 b 的一轴系数。
这些论文不是当前和式的现成覆盖；仍需证明新的转移或联合估计。

## 7. 有限命题、验证范围与剩余义务

可直接形式化的有限命题是 JT1、JT3、JT7、JT10，以及
有限 Euler 系数
Σ_{d|n,(d,B)=1}µ(d)c(dB)=c(B)δ_B(n)。
其中 JT7 可乘任意共同 A,n 权，逐项求和，完全不需要渐近理论。
JT9 的解析误差另有本节给出的初等证明。Poisson 完成则由
JQ5/JQ14 和 JT6 负责，不能称为无误差的有限 Fourier 等式。

测试文件 test_mwkf_joint_type_ii.py 检查正边界、非平方自由
quotient、双相位 Jacobian、共同 n 截断的全部 v 提升、
符号 gcd 因子、单位/平方自由掩码、有限除数交换、Euler
密度以及 v-shell 幂次账本。它不证明统一 symbol 界或完整 gate。

| 部分 | 本节结论 | 未覆盖的边界 |
|---|---|---|
| 精确 Type-II smooth bulk | 真实 χ、单位条件与相位均保留 | transition boundary 通常仍需另算 |
| e=q=1 的全部 v 算术密度 | JT12，平衡 p≤1 达到自身预算 | 不是原 canonical zero Gram |
| 顶层短 b Type-II | JT14，b≲T^{2/3}、U,V 对数幂 | 更长 b；e,q 不为1的完整重组 |
| 已发表线性 Möbius 输入 | JT16 的指定低频 v-shell | 顶层不足；不与 JT13 相乘 |
| 全部 AFE/reflection/零非零 signed operator | 原 PA 恒等式继续保留 | 目标范数、各独立端点与 tails 仍未全证 |

因此下一条解析义务是对长 b 的平方自由 discrepancy 与
剩余 µ(b)µ(c)、j,k,l 同时作 signed 重组，或找到保持完整
物理权的另一估计。不能把 JT9 的均值相减称为零行和/零列和
算子，也不能将 JT12 的显式算术密度当作完整零频结账。
