# 一般 q 的全 e 重组：单位掩码、共振与局部光滑核覆盖

白话结论：不再逐 e 估计时，一般 q 的原单位条件可以完整保留，
并在 primitive 频率表示中只留下 B、h 的两个单位限制。
整个精确共振子项没有额外的 q 幂次成本；平方自由均值误差只
增加 √rad(q)，而不是整个 e-shell 的数量。这把上一轮 q=1
的局部 all-e 光滑核估计扩展到一般 q，包括模型的部分长 B 区域。
**范围更正：本节固定 R=S=T³，故 q=T^χ、χ>0 的例子不满足
原 N=T³ 问题的 qR,qS≲N，不能算原非空物理箱覆盖。**
[PQ1–PQ13](2026-08-30-mwkf-physical-q-shell-coverage.md) 恢复随 q
缩小的 R,S 与原 1/q 外权，给出真正的内部 q 壳子域覆盖。
本节局部恒等式和估计仍成立；canonical zero Gram 与完整
twisted moment 没有因此得到证明。

沿用 [GP1–GP13](2026-08-30-mwkf-variable-kappa-coverage.md)
的 R=S=T³ 尺度与完整 symbol，使用
[GU6–GU8](2026-08-30-mwkf-general-unit-type-ii.md) 的带单位均值。
本节保持原 hδ 因子结构在实际核内，不假设新的 Möbius 相关界。

## 1. 全 e 双射与一般 q 的实际频率

固定 C₀>0、1≤q≤T^{C₀}，记 q₀=rad(q)。保留
\[
 R=S=T^3,\quad HL\asymp T^5,\quad P=K_{\min}K_{\max}\asymp T,
 \quad K\asymp T^\nu,\quad 0<\nu\le1,\quad X=R/K,\quad J=P/K.
\]
ν 固定；M≈X、B<2S。核的所有所需归一化导数与 q 一致为
O(T^ε)，这是本节指定 smooth core 的前提，不能据此吞并独立
AFE/reflection 尾。U=1 的 µ(d) 分解仍精确，所有整数端点如 GP。

从 IC2 的实际条件 (e,Aq)=1、(b,Aeq)=1 出发，置
\[
 M=Ae,\quad B=eb,\quad e=(M,B),\quad
 g=(M,q_0),\quad v=q_0/g,\quad L=[M,q_0]=Mv.       \tag{GQ1}
\]
非零项的原 (A,e,b) 与 **平方自由 M,B 且 (B,q₀)=1** 一一对应。
证明：正向由单位条件立得；反向令 e=(M,B)，平方自由性给
(A,e)=(b,Ae)=1，而 (B,q₀)=1 给 (e,q)=(b,q)=1。
不要求 (A,q)=1 或 (M,B)=1。q 的高素数幂只通过 q₀ 起作用。

完成 quotient 单位条件后，全部除数 ξ|L 先恢复，再置
n=(L/ξ)ℓ≠0。系数与载波精确为
\[
 \frac{C\mu(B)\mu(v)\kappa_L(n)}{BMv|j|},\quad
 e\left(-\frac{nkl}{jBv}\right),\qquad C=HL/R,
 \quad \kappa_L(n)=\sum_{d\mid(L,n)}\mu(d)d.        \tag{GQ2}
\]
这里 ξ 是求和除数，v=q₀/g 是固定的补素因子，二者不可混同。
核验 GQ2：原逐 ξ 系数是 Cµ(A)µ(b)µ(ξ)/(Bξ|j|)；
Σ_{ξ|L,L/ξ|n}µ(ξ)/ξ=µ(L)κ_L(n)/L，且
µ(A)µ(b)µ(L)=µ(B)µ(v)，因为 (M,v)=1。

实际幅度仍是 GE4（容许原核以 q 为参数）；z₀=KMkl/R。
精确 GP2 现在成为
\[
 \eta=\frac jJ\frac XM\frac P{kl},\qquad
 \sigma=\frac n{BJv}\left(\frac XM\right)^2\frac P{kl}.
                                                               \tag{GQ3}
\]
所以同一个 Ψ_{M,B,j,k,l}(u) 取 u=n/(BJv)，对 e/ξ 分配无依赖。
critical 支撑给 |j|≈J、cBJv≤|n|≤CBJv，c>0 固定，Ψ(0)=0。
连续改变 M 时须先固定 g，不能对不连续的 gcd 作微分。
在固定 g 上，GP 的 M/l 混合归一化导数证明仍适用。

## 2. 完整 primitive 表示只增加两个单位掩码

因 L 平方自由，κ_L(n)=µ(L)c_L(n)。采用负号 Fourier 约定，
完整 n-Poisson 给
\[
 \frac1B\sum_n\kappa_L(n)\Psi(n/(BJv))e(-nkl/(jBv))
  =Jv\mu(L)\sum_{(h,L)=1}
           \widehat\Psi\bigl(J(Bh/M+kl/j)\bigr).                \tag{GQ4}
\]
n=0 由 Ψ(0)=0 精确加入；h 是新增 Fourier 标签而不是原 AFE h。
Jacobian **Jv** 与 GQ2 的外部 1/v 消去，µ(v)µ(L)=µ(M)。因此
\[
 \mathcal P_{K,q,\rm crit}(Y)=C
 \sum_M\frac{\mu(M)}M
 \sum_{\substack{Y\le B<2Y\\(B,q_0)=1}}\mu(B)
 \sum_{k,l}\sum_{|j|\approx J}\frac J{|j|}
 \sum_{\substack{(h,M)=1\\(h,q_0)=1}}
 \widehat\Psi_{M,B,j,k,l}\bigl(J(Bh/M+kl/j)\bigr).              \tag{GQ5}
\]
所有真实支持仍在 symbol 内。q₀ 不出现在相位的分母中，
但两个单位条件绝不可以删掉；M 与 q₀ 仍可共有素因子。

精确共振 Δ=jBh+Mkl=0 是 GP11 除数族的子集。除原条件外，
要求 (B,q₀)=(h,q₀)=1，并由 g|M、g|q₀ 得到必要条件 **g|j**。
这是因为 jBh≡0 mod g 且 Bh 在模 g 上可逆。
保持原符号与真实支持，GP11 的联合 j/r 计数直接给
\[
                |\mathcal M_{\rm prim,K,q}|\ll_{\varepsilon,C_0}
                       CP T^\varepsilon\asymp T^{3+\varepsilon}.
                                                               \tag{GQ6}
\]
此式可包含全部允许 B/e，而不仅是一个 B-shell。q 的单位
限制只减小用于上界的解集，不需要乘 q 或 e 的数量。
此 primitive 共振仍不等于 canonical zero Gram 或 AFE diagonal。

## 3. 在活跃 g 层上求平方自由均值

将固定倍数的 M 支撑分成固定个数的 [X′,2X′]，X′≈X。
固定其中一片。置 M=gm，则 (m,q₀)=1，L=mq₀。
只有 **g|q₀ 且 g≤2X′** 的层可非空，其均值长度 X′/g≥1/2。
下面只对这些活跃层定义密度和误差；不向空层添加连续主项。

GQ2 的 m 和精确写成
\[
 \begin{split}
 C\sum_{g\mid q_0\atop g\le2X'}\frac{\mu(v)}{q_0}
 \sum_{B\approx Y\atop(B,q_0)=1}\frac{\mu(B)}B
 \sum_{k,l}\sum_{j\ne0}\frac1{|j|}\sum_{n\ne0}\kappa_{q_0}(n)
     e(-nkl/(jBv))\\
 {}\times\sum_{(m,q_0)=1}\frac{\mu^2(m)\kappa_m(n)}m
                   \Psi_{gm,B,j,k,l}(n/(BJv)).
 \end{split}                                                   \tag{GQ7}
\]
注意这里单位模数是 **q₀ 而不是 q₀B**；这是恢复全部 e 的收益。
固定 e 的 GU4 中相应的 B 单位掩码不能这样移除。

对 m 使用 GU6，以 c(q₀)δ_{q₀}(n) 为主系数，误差为
T^ε(g/X)^{1/2}D_{q₀}(n)||W||_{C¹}，其中
D_{q₀}(n)=Σ_{d| |n|,(d,q₀)=1}√d。所有长度在 [1/2,1] 的
端点和 d>X′/g 的连续延伸由 GU6 的误差支付。

所需完整 n 质量有
\[
 \sum_{0<|n|\le N}|\kappa_{q_0}(n)|\delta_{q_0}(n)
       \ll q_0T^\varepsilon,\qquad
 \sum_{0<|n|\le N}|\kappa_{q_0}(n)|D_{q_0}(n)
       \ll T^\varepsilon N^{3/2}.                \tag{GQ8}
\]
N 为 T 的固定幂。第一式为 GU7a：Rankin 与局部 Euler 因子
给 q₀T^ε。第二式必须保持 (d,q₀)=1；置 n=du 后
|κ_{q₀}(du)|=|κ_{q₀}(u)|，而
Σ_{1≤u≤Z}|κ_{q₀}(u)|≤Σ_{r|q₀}φ(r)⌊Z/r⌋≤Zτ(q₀)。
因此 Σ_{d≤N}√d·(N/d)τ(q₀)≪T^εN^{3/2}，没有大模数 +1。

GQ7 的密度用第一式支付全部 n、B、j 和除数多个 g，得到
\( |\mathcal M_{K,q}(Y)|\ll CP T^\varepsilon \)。它是这个线性
分解的算术均值，不是已被再次求值的原零 Gram。

误差先完成 l。载波 nk/(jBv) 与 m 无关；critical 支撑给
|n/(jv)|≈Y，所以整个 B 采样仍是 Y/Kmax+Kmin，包括整数 +1。
此时可把 (B,q₀)=1 删去作非负 majorant，但不能在 GQ7 等式中删。
用 N≈JYv 与 GQ8，固定 g 的额外算术因子精确为
\[
             \frac1{q_0}\sqrt g\,v^{3/2}
                     =\frac{\sqrt{q_0}}g .
\]
Σ_{g|q₀}1/g≪T^ε，仅用于上界，不给空层添加密度。因此
\[
 \begin{split}
 |\mathcal E_{K,q}(Y)|\ll T^\varepsilon CP X^{-1/2}J^{3/2}\sqrt{q_0}
   \min\left\{Y^{3/2},\ Y^{3/2}/K_{\max}+K_{\min}Y^{1/2}\right\}.
 \end{split}                                                   \tag{GQ9}
\]
两项是同一个误差的两种估计，不相乘 saving。没有漏掉 e-shell
成本：e 已由 gcd(M,B) 唯一恢复，整个 e 家族参与同一个和。

## 4. 一般 q 的局部核覆盖及物理范围限制

令 Kmin=T^a、Y=T^β、q₀=T^χ（容许固定倍数），0≤a≤1/2。
GP7 的三个误差指数全部增加 χ/2；密度指数仍为3。所以一个
给定 all-e 光滑 core 的充分覆盖条件为
\[
 \boxed{\quad\beta\le(2\nu-\chi)/3\quad\text{或}\quad
 [\,\beta\le2(1+\nu-a-\chi/2)/3\ \text{且}\quad
                 \beta\le2(\nu-a-\chi/2)\,].\quad}             \tag{GQ10}
\]
负右端不能解释为自动覆盖。两个具体例子：

| ν | a | χ | β | 未完成 l | 完成后积分项 | 整数项 |
|---|---|---|---|---|---|---|
| 1 | 1/2 | 1/5 | 4/5 | 33/10 | 14/5 | 3 |
| 1 | 0 | 1/2 | 7/6 | 4 | 3 | 17/6 |

两行整个指定光滑 all-e core 都为 O(T^{3+ε})，后一行允许 B>T；
原 GP 只覆盖 q=1。但 χ>0 与 R=S=T³ 联用违反原 (5.3) 的
qR,qS≲N，它们仅是独立光滑模型的尺度例子，不是原参数多面体
的非空箱。原先将其称为“实际覆盖”的表述在此更正。
PQ10–PQ13 用 R=S=N/(8Q)、q≈Q 恢复真实内部箱，同时将
normalized 目标改为 S≈T^{3−γ}；不能沿用本表的目标指数3。
GQ6 对全部 B 的共振界也只是每个指定 q、给定光滑核的统一界，
不证明固定 e 子和或自动给出原 q 外层估计。

## 5. 有限补集及完整边界成本

在 GQ5 中减去 Δ=0，并保留 |JΔ/(jM)|≤F=T^δ 的闭窗口，
便得到 GP13 加上 **(B,q₀)=(h,q₀)=1** 的有限 signed 核。
它与 GQ6 加下列独立误差精确还原同一个 core。没有证明此
矩阵零行和/零列和或全体向量上的目标算子范数。

- 原 d=1 与 κ=e=1 端点仍由 d≳K、固定 ν>0 和 K>2 排除；
  U=1 没有过渡整数。原 AFE 的其他边界不在这个论断内。
- 原 JT6 非critical 全 j/ℓ 成本只多 τ(Aeq)≪T^ε，仍为
  O(T^{8−ν−L₀+ε})。原 ℓ=0 全 j 成本仍为 O(T^{6−L₀+ε})。
  q≤T^{C₀} 保证除数成本一致；这里 L₀ 是衰减阶数，不是 GQ1
  的整数 L。
- 新 l-Fourier 窗口若需截成字面有限和，用 |κ_L(n)|≤L、
  n≲JYv≤JYq₀ 支付全部外层，保守尾为
  O(T^ε C P X JY q₀ F^{1−L₀})。在每个固定 g 层窗口与 m
  无关，故不损害 GU6 所需的 C¹ 范数。
- GQ5 的新增 h-Fourier 尾与 GP 完全同尺度：删除单位限制后
  非负 majorant 是 O(T^ε C P(JS+X log(2S))F^{1−L₀})。
  q 的幂次因子已在 GQ4 精确抵消，不需重新添加。h 端点是
  ceil[(M/B)(−F/J−kl/j)] 与 floor[(M/B)(F/J−kl/j)]，包含等号。
- B 半开 dyadic 端点、m 均值过渡和大除数连续项均已支付。
  活跃 g 层必须先选定；不能因为原 M 和为空，就把人工添加的
  连续密度也视为零。不同 Fourier 表示的尾不重复当成主项扣除。

选择 L₀ 充分大后上述变换尾任意幂次小。这里仍不包含原 AFE
的独立物理尾、canonical zero Gram 或两个 reflection mixed 项。

## 6. 长 B 文献输入的本轮审计

在 q=1 的 primitive 核中，固定 M,j,k,l,h，主频窗口的 B 宽度
约为 Y/P：因为 h≈R/Y、J≈P/K、M≈R/K，频率对 B 的导数
J|h|/M≈P/Y。平衡 P≈T、Y=T^β 时，该宽度是 T^{β−1}。
[Matomäki–Teräväinen, Theorem 1.1](https://ems.press/content/serial-article-files/32826)
对长度至少 x^θ、θ>0.55 的所有短区间给 Möbius 均值的对数
节省；这里连其长度条件都要 β>20/9 才满足。它不提供固定
幂次节省，因此即使完成相应实际权重的分部求和，也不能把
ν=1 时 T⁵ 的逐项外层账本降到 T³。其 Theorem 1.5 的统一线性
twist 亦是对数节省，而不是本问题所缺的 T²。

这项核验不否定全局 dispersion；它排除的是逐个短窗口套用
该已发表结果后直接宣布达标。GQ10 的新覆盖来自实际全 e
单位结构及联合 B/斜率采样，不来自把该短区间输入夸大。

有限回归核验原 (A,e,b,ξ) 和 GQ2 的 signed 系数、共享素因子、
分数 n/v、GQ4 的 Jacobian、两个单位掩码及共振 g|j。它们不
证明解析范数；完整 coupled-kernel gate 与 twisted moment 仍开放。
