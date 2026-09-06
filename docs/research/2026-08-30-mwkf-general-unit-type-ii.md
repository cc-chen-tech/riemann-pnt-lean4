# Type-II 的一般单位重组：全部 e 的密度与真实分片成本

白话结论：上一轮 e=q=1 的全除数重组可以推广到实际 e,q
单位条件。显式算术密度对全部 e 求和只花对数；误差却没有
逐 e 的幂次衰减，必须支付整个 e-shell 的数量。平衡顶层的新
覆盖条件是 η+χ/2+3β/2≤1，其中 E=T^η、rad(q)=T^χ、
UB₀=T^β。**这是固定 q、指定实际光滑分片的结果，不是完整
coupled-kernel gate 或 twisted moment 的证明。**

这里扩展 [JT1–JT16](2026-08-30-mwkf-joint-type-ii-density.md)；
实际 hδ 核、Type Möbius 符号、共同截断仍不动。
原 canonical zero Gram、两项 reflection 交叉项及所有独立
物理尾不由本节删除。算术均值相减也不自动产生零行和/零列和。

## 1. 冻结真正的共同素因子

沿用 IC2 和 JT 的记号，固定平方自由 e 且 (e,q)=1。置
\[
 q_0=\operatorname{rad}(q),\quad r=e q_0,\quad
 g=(A,q_0),\quad A=ga,\quad
 L=\operatorname{rad}(Aeq)=ar .
 \tag{GU1}
\]
由于 µ(A)，只需平方自由 A；于是 g|q₀、(a,r)=1。原
(e,Aq)=1、(bc,Aeq)=1 精确成为
(e,q)=1、g|q₀、(a,r)=1、(bc,r)=1、(a,bc)=1。
不能补上 (A,q)=1，因为 g>1 的项一般存在。
q 的高素数幂只通过 q₀ 出现；e 非平方自由的原项为零。

取一个实际 A 分片 A∈[X,2X]，X≈R/(eK)，D=S/e。
只有 g≤2X 的层能非空，所以 a 的长度 X/g≥1/2。
若原支撑在其他固定倍数区间，先用固定个数的 A 分片处理；
有效 e≲R/K。长度在 [1/2,1] 的整数端点照下文保留。

## 2. 全 v 的精确 signed 系数和实际相位

JT5 的单位完成求和原为 v|Aeq，µ(v) 将其限制成 v|L。
先恢复全部 v，再置 n=(L/v)ℓ。定义
\[
 \kappa_r(n)=\sum_{d\mid(r,n)}\mu(d)d
           =\mu((r,n))\varphi((r,n)),\qquad n\ne0 .
\]
因 L=ar 平方自由、(a,r)=1，有限恒等式给
\[
\begin{split}
 \mu(A)\sum_{\substack{v\mid L\\L/v\mid n}}{\mu(v)\over v}
 &= {\mu(A)\mu(L)\over L}
                  \sum_{d\mid(L,n)}\mu(d)d\\
 &= {\mu(r/g)\over ar}\,\kappa_r(n)
                  \sum_{d\mid(a,n)}\mu(d)d .
 \tag{GU2}
\end{split}
\]
特别是 µ(r/g) 含有 µ(e) 的符号；不能把它换成正密度。

实际变换变量为
\[
 z_0={KAkl\over D},\quad
 \eta={jK\over z_0},\quad
 \xi={nD\over B ar},\quad
 \sigma={\xi\over z_0},\qquad B=bc .
\]
这些量只依赖固定的 e,g 和 A,n,b,c,j,k,l，不依赖 v 的分配。
载波精确为
\[
                    e\!\left(-{ngkl\over jB r}\right).
 \tag{GU3}
\]
固定 n,g,e 后，a 的归一化导数仍为
Λ∂_Λ−η∂_η−2σ∂_σ，加上实际 A/X 幅度的导数。
故 JT4 的完整 symbol 及 critical cutoff 在 a 上具有
统一 O(T^ε) 的所需范数。这里不是只识别 leading term。

因此固定 e 的 critical smooth bulk 等于
\[
\begin{split}
 C_e\sum_{\substack{c\le U,\ b>V\\(bc,r)=1}}\mu(c)\mu(b)
 \sum_{k,l}\sum_{j\ne0}
 \sum_{\substack{g\mid q_0\\g\le2X}}{\mu(r/g)\over r}
 \sum_{n\ne0}{\kappa_r(n)\over bc|j|}
 e\!\left(-{ngkl\over jbc r}\right) \qquad\\[-6pt]
 {}\times
 \sum_{\substack{a\ge1\\(a,rbc)=1}}
   {\mu^2(a)\over a}\sum_{d\mid(a,n)}\mu(d)d\
       W_{e,g,b,c,j,k,l,n}\!\left({a\over X/g}\right),
 \qquad C_e={HL\over Re}.
 \tag{GU4}
\end{split}
\]
全和保留 µ(b)µ(c) 以及真实 hδ 核。对每个 g，critical 支撑给
\[
       |j|\asymp Z/K,\qquad
       0<|n|\ll M_g:={ZbcXr\over Dg}.
 \tag{GU5}
\]
共同 n 截断要提升到各 v；残留的 v-shell 或独立 ℓ 矩形
不能直接使用 GU2。ℓ=0、非critical 尾、JT1 的正边界均按
原账本保留。

## 3. 平方自由均值必须保留 d 的单位掩码

JT9 的证明实际上给出稍强的版本。令 Y≥1/2，Q,|n|≤T^C，
W 光滑支撑于 [1,2]，则
\[
\begin{split}
 &\sum_{(a,Q)=1}{\mu^2(a)\over a}
       \sum_{d\mid(a,n)}\mu(d)d\,W(a/Y)\\
 &=c(Q)\delta_Q(n)\int_1^2 W(x){dx\over x}
 +O\left(T^\varepsilon\mathcal N(W)Y^{-1/2}
          \sum_{\substack{d\mid|n|\\(d,Q)=1}}\sqrt d\right).
 \tag{GU6}
\end{split}
\]
记号 c(Q)、δ_Q(n) 与 JT9 相同。证明仍是 a=du 的有限交换
和平方自由单位整数的 floor 计数；(d,Q)=1 从未消失。
Y/d≥1/2 用分部求和；d>2Y 时支付被补入的连续主项。
Y<1 或 Y<d<2Y 的 u=1 项照旧保留，没有无误差延伸截断。

在 GU4 中取 Q=rbc、Y=X/g。不能为了写成较粗形式而删去
(d,r)=1，因为下面的整个 n 平均正需要它。

### 加权 n 密度和误差的统一平均

一方面，对任何多项式大小的平方自由 r 和正整数 B,M，
\[
 {1\over r}\sum_{1\le|n|\le M}
            |\kappa_r(n)|\delta_{rB}(n)\ll_\varepsilon T^\varepsilon .
 \tag{GU7a}
\]
取小的固定 s>0 做 Rankin。p∤rB 的 Euler product 收敛；
p|B,p∤r 的因子至多 (1-p^{-s})^{-1}；p|r 的因子为
1+(p-1)p^{-s}/(1-p^{-s})≤p/(1-p^{-s})。
乘积中的 r 恰被外面的 1/r 抵消。剩下有限素因子乘积和
M^s 用 JT11 的方法吸入 T^ε。允许 κ_r(n) 带符号，不声称
物理密度为正。

另一方面，对任意 Y≥0 有字面的整数估计
\[
 \sum_{1\le m\le Y}|\kappa_r(m)|
 \le\sum_{h\mid r}\varphi(h)\lfloor Y/h\rfloor
 \le Y\tau(r).
 \tag{GU7b}
\]
第一步用 |\kappa_r(m)|=φ((r,m))≤(r,m) 及 gcd 的 totient
展开。这包括 Y<r，不能逐个 h 加一个未计费的整数 +1。
对 (d,r)=1，κ_r(dm)=κ_r(m)。所以
\[
 \sum_{1\le |n|\le M}|\kappa_r(n)|
       \sum_{\substack{d\mid n\\(d,r)=1}}\sqrt d
 \ll \tau(r) M^{3/2}.
 \tag{GU8}
\]
证明为交换 d,m，再用 GU7b 和
Σ_{d≤M}d^{-1/2}≤2√M；负 n 只乘2。M<1 时左边为空。
这一步允许删除 (d,B)=1 以取上界，却不能删除 (d,r)=1
再错误地沿用 κ_r(dm)=κ_r(m)。

## 4. 全部 e 的密度，和没有 e 衰减的误差

定义 GU4 的精确算术主密度 \(\mathcal M_e\) 为替换 a 和式
为 GU6 中的显式积分；\(\mathcal E_e\) 为其差。对固定原 q，
GU7a、g 的除数个数和 b,c,j 的调和求和给
\[
       |\mathcal M_e|\ll T^\varepsilon {HL P\over Re},
 \qquad
       \sum_{\text{全部有效 }e}|\mathcal M_e|
                       \ll T^\varepsilon {HL P\over R}.
 \tag{GU9}
\]
求和仍限平方自由 e、(e,q)=1。第二式只有调和成本。
这不是原 q 外层的求和结论，也不把算术密度识别为 canonical
zero Gram。

对 b≈B₀，使用 GU6 和 GU8。先固定 g，实际误差账本是
\[
 T^\varepsilon C_eP X^{-1/2}
       (ZX/D)^{3/2}{\sqrt r\over g}
       \sum_{c\le U}\sum_{b\asymp B_0}(cb)^{1/2}.
\]
Σ_{g|q₀}1/g≪T^ε，双和≪(UB₀)^{3/2}，故
\[
\begin{split}
 |\mathcal E_e(B_0)|
 &\ll T^\varepsilon
       {\rho\sqrt{S q_0}\,Z^{3/2}(UB_0)^{3/2}\over K},\\
 \sum_{e\asymp E}|\mathcal E_e(B_0)|
 &\ll T^\varepsilon E\,
       {\rho\sqrt{S q_0}\,Z^{3/2}(UB_0)^{3/2}\over K},
 \qquad \rho={HL P\over S^2}.
 \tag{GU10}
\end{split}
\]
代入 X≈R/(eK)、D=S/e、r=e q₀ 可直接核验：逐 e 的
所有幂次恰好抵消。**整段 e 求和必须另乘 E**；GU9 的
调和成本不能复制给 GU10。

一般写 R=T^r₁、S=T^s、ρ=T^ω、Z=T^ζ、K=T^ν、
UB₀=T^β、E=T^η、q₀=T^χ。显式密度的指数为 ω+2s−r₁，
误差整个 e-shell 的指数为
ω+s/2+χ/2+3ζ/2+3β/2−ν+η。
这两者都须与实际目标 S=T^s 比较；不是相乘的 saving。

在平衡顶层 R=S=T³、HL≈T⁵、P≈K≈Z≈T，得到
\[
 \sum_{e\asymp E}|\mathcal E_e(B_0)|
       \ll T^{2+\varepsilon}E\sqrt{q_0}(UB_0)^{3/2}.
 \quad
                  \eta+{\chi\over2}+{3\beta\over2}\le1 .
 \tag{GU11}
\]
最后一个不等式给出实际 Type-II 分片的预算覆盖，前提是
全部边界都核验。具体取 e∈[E,2E]、b∈[B₀,2B₀]，
若 8EUB₀<S，transition boundary 上的 a<2U 给 ab<4UB₀<D，
故为空。这里 boundary 的 a 是 JT1 中 cm，不是 GU1 的 A/g。
K>2 排除 κ=e=1 纠正。Z≈T 以及多项式参数范围使 JT6 的
全非critical 尾和 ℓ=0 密度在付完整外层后仍 rapid。
因此这些条件下，GU11 加 GU9 覆盖整个 e-shell 的实际
smooth-core Type-II 部分。

例如 q=1，U,V 为固定对数幂：

| 完整 e-shell | b-shell | 误差指数 | 结论 |
|---|---|---|---|
| E≈1 | B₀≈T^{2/3} | 3 | 恢复 JT14 |
| E≈T^{1/2} | B₀≈T^{1/3} | 3 | 新的整个 e 家族覆盖 |
| E≈T | B₀≈T^{2/3} | 4 | 不覆盖；不能漏算 e 数量 |

等号处固定对数幂由 ε 吸收，边界条件对大 T 自动满足；
有界 T 调整常数。原 q 的物理外层、不同非顶层尺度、
剩余更长 b/e 区域、全部 AFE/reflection 范数仍需联合估计。

## 5. 长 b 的 n 完成：非零 determinant 不等于快速衰减

本轮也检查了先对 n 求和的路线。e=q=1，固定 A,B,j,k,l，
将共同 symbol 写成紧支撑光滑函数 Ψ(n/B)；顶层该函数的
归一化导数受控。展开 κ_A(n) 并令 n=dm 后，Poisson 给
\[
 \sum_n\kappa_A(n)\Psi(n/B)e(-nkl/(jB))
    =B\sum_{d\mid A}\mu(d)\sum_{h\in\mathbb Z}
          \widehat\Psi\!\left({Bh\over d}+{kl\over j}\right).
 \tag{GU12}
\]
Ψ 可包含实际 A,n 相关权，固定 A 后操作；n=0 因 critical
cutoff 的支撑而为零。此式含无限 Fourier 和，只有其 Schwartz
尾被付费后才能使用有限截断。
GU12 中 h 是新增的 n-Fourier 指标，不是原 AFE 的 h 标签；
原 hδ 的耦合信息仍由实际 Ψ 承载。

频率是 (jBh+dkl)/(jd)。若 (d,B)=1 且 B>|kl|，精确
determinant=0 不可能；但接近零的频率仍存在。例如
d=101、B=1011、j=1、kl=10、h=−1 给 determinant=−1，
频率=−1/101，且 d、B 都平方自由、互素。这只是有限算术
例子，不声称实际核在该点非零或得到 Selberg 反例。
更一般，d≥B/2 时取最近整数 h 总能使
|jBh+dkl|≤|j|B/2≤|j|d。因此无精确零不能推出整和 rapid，
也不能凭这个条件宣称新的 T² saving。

## 6. 已发表平方自由估计的输入检查

检索到的相关工具处理不同的平均，不能仅因都含 µ² 就直接套用：

| 输入 | 真实适用对象 | 本节核验 |
|---|---|---|
| [Le Boudec, Theorem 1](https://arxiv.org/pdf/1411.2360) | Q≤Y，固定模数所有单位剩余类上的平方自由误差方差，界为 Y^ε(Y^{1/2}Q^{1/2}+YQ^{-1/2}) | 对整个单位总数直接 Cauchy 只给 Y^{1/4}Q^{3/4}+Y^{1/2}Q^{1/4}，不改善本节 O(T^ε√Y)；若 Q>Y，连这一输入范围也不满足 |
| [Mangerel 的 smooth-modulus 定理](https://arxiv.org/abs/2008.11163) | 平方自由、足够光滑的模数，Q≤Y^{196/261−ε} 的单个单位等差数列 | 当前 d·r·bc 不具有这种已验证的光滑性/大小限制，且缺少全 signed 参数族的转移 |

上面的范围判断是对本问题的推导，不是声称论文讨论了当前
coupled kernel。固定模数方差若要用于真正全局 dispersion，
必须先识别保留 µ(b)µ(c)、hδ、原幅度及外层符号的实际范数，
并逐项支付矩阵/参数族大小。本节未证明这个转移。

有限回归检查覆盖 GU2 的共有 q 素因子、e 的符号、q 的素数幂、
全部原始单位掩码、共同 n 截断、GU7b floor 计数、GU10 的
整个 e 成本及 GU12 的近共振例子。它们不是解析 gate 证据。

后续真正缺口仍是 GU10 覆盖外的 signed discrepancy；
尤其不能将 GU9 的全部 e 密度结账误称为全部 Type-II 或原
canonical zero Gram 已估计。完整 twisted moment 保持未证明。
