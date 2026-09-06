# 保留完整 κ 对偶频率族的新覆盖与共振账本

白话结论：当原 κ 尺度降低到 K<T 时，对偶 j 不再只有固定
个数。本节把 j≈T/K 及 n≈BT/K 的完整成本放回实际公式，
仍得到新的 all-e 联合区域覆盖。例如 K≈T^{9/10}、平衡短斜率、
B≈T^{4/5} 的整个指定光滑 core 达到 T^{3+ε}；短斜率不平衡
时还覆盖 K≈T^{4/5}、B≈T^{6/5} 的一块长 B 区域。
完整 j 家族的精确 primitive 共振亦在预算内，但原因是联合
除数约束，不是漏掉 Fourier Jacobian 或 j 的数量。
**一般 q、K≈1、覆盖外 B、canonical zero Gram、两个 reflection
mixed 项及独立 AFE 尾仍未关闭；这不是完整 twisted moment。**

本节延伸 [GE](2026-08-30-mwkf-global-e-primitive-resonance.md)
的实际 all-e 重组和 [GS](2026-08-30-mwkf-global-slope-sampling.md)
的光滑斜率完成。它不引入新的通用相关性假设，也不将两次
saving 相乘。实际核、原 hδ 标签与物理归一化沿用 IC2/GE4。

## 1. 尺度与精确 symbol，不能把有界比值写成1

固定 q=1，并取
\[
 R=S=T^3,\quad HL\asymp T^5,\quad
 P=K_{\min}K_{\max}\asymp Z=RP/S\asymp T,
 \quad K\asymp T^\nu,\quad 0<\nu\le1,\quad
 X=R/K,\quad J=P/K.                                  \tag{GP1}
\]
ν 是固定正数；不外推到 ν=0，也不声称对 ν→0 的端点一致。
K 是原 κ 的尺度，k,l 是非零短斜率。可交换两条斜率及核的
对应坐标，使 |k|≈Kmin、|l|≈Kmax；不假设核对称。分片光滑，
支撑倍数固定。本文的 M≈X 是 M=Ae，不是原来单独的 A。

恢复所有人工 e/A/b 分片后，GE3 给平方自由整数对
M=Ae、B=eb、e=(M,B) 的双射。**没有 (M,B)=1 掩码。**
原 (b,Ae)=1 的条件已经参加该双射，不能重加一次。
幅度仍是 GE4 的
\[
 \frac{w(t)}x\widetilde G(tKM/R,x,kH/(Sx),lL/(Sx))\chi(Sx/B).
\]
其紧支撑给 M≈X、e≲X、d≈S/e≳K；固定 ν>0 和充分大 T
保证 d>1、K>2，故 GE2 的 d=1 与 IC2 的 κ=e=1 纠正均为空。
U=1 时 χ(m)=1_{m>1} 在每个正整数精确成立，没有过渡整数。
所有 B<2S 保留；选取 B∈[Y,2Y) 只限制 B，不限制 e。

JT 的精确参数为
\[
 \begin{split}
 z_0&=KMkl/R,&\quad \Lambda&=|z_0|\asymp P,\\
 \eta&=jK/z_0=\frac jJ\frac XM\frac P{kl},&
 \sigma&=\frac{nR/(BM)}{z_0}
       =\frac n{BJ}\left(\frac XM\right)^2\frac P{kl}.
 \end{split}                                                   \tag{GP2}
\]
X/M、P/(kl) 在固定紧集内，但不能删去。特别是 η 不等于
j/J，σ 不等于 n/(BJ)；它们决定对 M 和 l 的微分。
critical cutoff 给 j 与 kl 同号、|j|≈J、cBJ≤|n|≤CBJ，
其中 c>0 固定。令 Ψ_{M,B,j,k,l}(u) 是 JT4 的完整精确 symbol，
以 u=n/(BJ) 为自变量；它在固定紧集光滑且 Ψ(0)=0。
不能继续用 Ψ(n/B) 并声称其归一化范数对 J 一致。

在固定 n,j 时，M∂M 与 l∂l 分别作用为
Λ∂Λ−η∂η−2σ∂σ 和 Λ∂Λ−η∂η−σ∂σ，另加实际 G 坐标
及光滑分片的归一化导数。因此 JT4 给出所需的统一混合
M/l 导数界；Λ≈T 仍是大参数。未截去 stationary-phase 的
某个渐近误差。有限 critical 主式为
\[
 \mathcal P_{K,\rm crit}(Y)=C
 \sum_{Y\le B<2Y}\frac{\mu(B)}B
 \sum_{k,l}\sum_{j\ne0}\frac1{|j|}\sum_{n\ne0}e(-nkl/(jB))
 \sum_M\frac{\mu^2(M)\kappa_M(n)}M
                 \Psi_{M,B,j,k,l}(n/(BJ)),\qquad C=HL/R.
                                                               \tag{GP3}
\]
物理 B<2S、M≈X 及全部真实支持在 Ψ 内。所有 n,j 均由
critical 支持限制成有限集；该式保留原双 Möbius 信息。

## 2. 全 j/n 成本下的一次光滑斜率完成

用 JT9 的 Q=1 平方自由均值对 GP3 的 M 和作线性分解，得到
\(\mathcal P_{K,\rm crit}(Y)=\mathcal M_K(Y)+\mathcal E_K(Y)\)。
均值系数是 δ₁(n)/ζ(2)，误差不超过
T^ε X^{-1/2}D(n)||W||_{C¹}，其中 \(D(n)=\sum_{d\mid |n|}\sqrt d\)。
JT9 中所有大除数、整数过渡和连续延伸误差继续保留。

密度在原 l 表示中控制。因为
Σ_{0<|n|≤CJY}δ₁(n)≪T^ε、Σ_{|j|≈J}1/|j|≪1，
Σ_{B≈Y}1/B≪1，得到
\[
                         |\mathcal M_K(Y)|\ll CP T^\varepsilon.
                                                               \tag{GP4}
\]
它不是 canonical zero Gram，也不假定为实数或正数。

对同一个误差先完成 l。设
V(u)=Ψ_{M,B,j,k,Kmax u}(n/(BJ))，负号 Fourier 约定给精确等式
\[
 \sum_l\Psi_{M,B,j,k,l}(n/(BJ))e(-nkl/(jB))
   =K_{\max}\sum_{\omega\in\mathbb Z}
        \widehat V\bigl(K_{\max}(\omega+nk/(jB))\bigr).
\]
载波仍与 M 无关，混合 M/l 导数保持 Fourier 衰减。
对于 |j|≈J、cJY≤|n|≤CJY，**有 |n/j|≈Y**。故 GS5 的
单调采样证明原样给出与 J 无关的常数：对任意固定 L>1，
\[
 \sum_{Y\le B<2Y}\sum_\omega
 (1+K_{\max}|\omega+nk/(jB)|)^{-L}
       \ll_L Y/K_{\max}+K_{\min}.                 \tag{GP5}
\]
具体地，每个近 ω 的单峰积分为 O(Y/(Kmin Kmax))，整数
计数另付 O(1)；近 ω 共 O(Kmin) 个。远 ω 的完整尾被
Y/Kmax 吸收。这里用了 |n/j| 的正下界，不能先把 n 扩到零附近。
区间端点按 [Y,2Y) 处理，并未以连续长度替代整数 +1。

完成 GP5 后才扩大 n 为 0<|n|≤CJY。其除数总质量是
ΣD(n)≪(JY)^{3/2}，**不是 Y^{3/2}**。支付 B^{-1}≤Y^{-1}、
#k≪Kmin、Poisson 的 Kmax 和完整 j 的调和质量，得到
\[
 \begin{split}
 |\mathcal E_K(Y)|&\ll T^\varepsilon CP X^{-1/2}J^{3/2}
       \left(Y^{3/2}/K_{\max}+K_{\min}Y^{1/2}\right)=:T^\varepsilon E_1,\\
 |\mathcal E_K(Y)|&\ll T^\varepsilon CP X^{-1/2}J^{3/2}Y^{3/2}
       =:T^\varepsilon E_0.
 \end{split}                                                   \tag{GP6}
\]
第二行是不完成 l 时的同一个均值误差。所以可取 min(E₀,E₁)，
不能将两种 saving 相乘。没有声称平方自由误差在不同 B 上
有未知的 Möbius 符号相关；只使用完整光滑 l 求和与 B 采样。

## 3. 新覆盖多面体及实际例子

写 Kmin=T^a、Kmax=T^{1-a}、0≤a≤1/2、Y=T^β，0≤β≤3。
由 CP≈T³、X≈T^{3−ν}、J≈T^{1−ν}，GP6 的三个指数为
\[
 e_0=3-\nu+3\beta/2,\qquad
 e_{\rm int}=2+a-\nu+3\beta/2,\qquad
 e_{\rm lattice}=3+a-\nu+\beta/2.                 \tag{GP7}
\]
于是完整指定 smooth core 达到 T^{3+ε} 的一个充分区域是
\[
 \boxed{\quad
 \beta\le 2\nu/3
 \quad\text{或}\quad
 \bigl[\,\beta\le 2(1+\nu-a)/3\ \text{且}\ \beta\le2(\nu-a)\,\bigr].
 \quad}                                                        \tag{GP8}
\]
第二个括号来自同时支付积分与整数采样两项。ν≤a 时该分支
可能没有正 β；第一分支仍须保留。ν=1 精确恢复 GS 的指数。
所有等号边界容许固定对数成本，由 ε 统一吸收。

| ν | a | β | e₀ | e_int | e_lattice | 较优误差指数 |
|---|---|---|---|---|---|---|
| 9/10 | 1/2 | 4/5 | 33/10 | 14/5 | 3 | 3 |
| 4/5 | 0 | 6/5 | 4 | 3 | 14/5 | 3 |
| 3/5 | 1/2 | 2/5 | 3 | 5/2 | 31/10 | 3 |

前两行是 K<T 时的新联合覆盖，第二行还包含 B>T；第三行
说明 l 完成不一定更好，必须取两种估计较优者。
这些都是 q=1、R=S=T³、HL≈T⁵、P≈T 的 **all-e 联合和**，
不是固定 e 子和。特别是限制 e=1 会重新引入 (M,B)=1，不能
据 GP8 宣称该子和有独立上界。已覆盖 B dyadic 块可在证明后
相加，只花对数成本；不据此删除覆盖外的 B 或原 q 外层。

## 4. 完整 j 家族的 primitive 共振，不漏 Fourier Jacobian

对固定 M,B,j,k,l 用 κ_M(n)=µ(M)c_M(n)，对全 n 作 Poisson：
\[
 \frac1B\sum_n\kappa_M(n)\Psi(n/(BJ))e(-nkl/(jB))
   =J\mu(M)\sum_{(h,M)=1}\widehat\Psi
                     \bigl(J(Bh/M+kl/j)\bigr).                 \tag{GP9}
\]
这是 GE8 的尺度版，右侧的 **J 不可省略**。Ψ(0)=0 允许将
n=0 精确加回；h 是这个 n 变换的新标签，不是原 AFE 的 hδ。
GP3 遂变为
\[
 C\sum_M\frac{\mu(M)}M\sum_{B\approx Y}\mu(B)
 \sum_{k,l}\sum_{|j|\approx J}\frac J{|j|}
   \sum_{(h,M)=1}\widehat\Psi_{M,B,j,k,l}
                      \bigl(J(Bh/M+kl/j)\bigr).                \tag{GP10}
\]
j 的符号及其他支持仍在 Ψ 中。h 和绝对收敛；下节明确付尾。

精确共振 Δ=jBh+Mkl=0 的解仍由 GE11 给出：
d=(|j|,M)、M=dM₁、j=dj₁、(j₁,M₁)=1，以及
B=M₁r、j₁rh=−kl、(h,M)=1、B 平方自由。
但此处必须**联合计数 j,r**。固定 M,k,l 后，
\[
 d\mid M,\qquad |j_1|\mid |kl|,\qquad
 r\mid |kl/j_1|
 \quad\Longrightarrow\quad
 \#\{(j,B,h):\Delta=0\}\le\tau(M)\tau(|kl|)^2.                \tag{GP11}
\]
critical 已固定 sign(j)=sign(kl)，没有另一个 j 符号；不固定
该符号时右侧可乘2。参数化唯一，必须仍筛选真实 j 区间、
gcd 条件和平方自由 B。只得 M|jB，不是 M|B；允许 M,B 共有
素因子。符号 µ(M)µ(B)=µ(d)µ(r) 仍保留。

在 j≈J 上 J/|j|≪1，Ψhat(0)≪T^ε。付 GP11 的除数成本、
Σ_{M≈X}1/M≪1 和 #(k,l)≪P，整个精确共振子项因此满足
\[
                    |\mathcal M_{\rm prim,K}|\ll CP T^\varepsilon
                          \asymp T^{3+\varepsilon}.            \tag{GP12}
\]
此界包括所有允许 B/e 和完整 j 族，适用于每个固定 0<ν≤1。
若逐 j 使用 GE12 再求和，却省略 GP9 的 J，就会得到错误理由。
这里真正避免 J 数量的是 GP11 的联合除数约束。
该项未被识别为 GP4、canonical zero Gram、AFE diagonal 或
reflection boundary，不能重复扣除这些不同的“密度”。

## 5. 字面有限补集、所有尾项与端点

取 F=T^δ，δ>0 固定。为 GP10 定义有限核
\[
 C_{F,K,Y}(M,B)=\frac{\mathbf1_{Y\le B<2Y}}M
 \sum_{k,l}\sum_{|j|\approx J}\frac J{|j|}
 \sum_{\substack{(h,M)=1\\0<|J(jBh+Mkl)/(jM)|\le F}}
    \widehat\Psi_{M,B,j,k,l}\bigl(J(jBh+Mkl)/(jM)\bigr).
                                                               \tag{GP13}
\]
全部真实支持包含在 symbol；式中省略零共振但不省略近共振。
完整 core 等于相同 B-shell 上的 GP12 子项加
CΣ_{M,B}µ(M)µ(B)C_{F,K,Y}(M,B)，再加下列独立变换尾。
**没有证明这个有限矩阵零行和/零列和，也没有证明其全体向量
的 ℓ²→ℓ² 目标范数。** 在 GP8 内，整个 core 与精确共振分别
达标，故此 Möbius 向量对的非零补集也达标；覆盖外不作此断言。

完整归一化账本（L 可按 δ 和所需 A₀ 选得足够大）：

1. JT6 的非critical 补集，包括 j=0、远 j/ℓ。每个 e,A,b,k,l
   的成本为 C_e T^ε Z^{1−L}(K+Z)/D，C_e=HL/(Re)、D=S/e，
   所以 C_e/D=HL/(RS)≈T^{-1}。恢复全部原 e,A,b 时
   Σ_e #(A≈X/e)#(b<2S/e)≪XS；再付 P，得到
   **O(T^{8−ν−L+ε})**。这里没有把 j 当成固定集合。
2. 原 ℓ=0 的全 j 使用 JQ6，b 的1/b为对数成本。全部 e,A,κ
   成本为 C P K X=C P R≈T⁶，故尾为 **O(T^{6−L+ε})**。
   该 ℓ=0 不是原 canonical zero Gram。
3. l 完成若需有限 ω 窗口，保留
   |Kmax(ω+nk/(jB))|≤F，含等号。移位格尾为
   O(T^ε Kmax(1+1/Kmax)F^{1−L})。用 |κ_M(n)|≤M、#M≪X、
   #n≪JY、Σ_j1/|j|≪1，整个 B-shell 的保守尾为
   **O(T^ε C P X J Y F^{1−L})
   =O(T^{7−2ν+β+ε}F^{1−L})**。窗口不依赖 M，不损害均值所需
   的 M 光滑性。直接证明 GP6 无须截断，这只是有限版本的账本。
4. GP10 的 h 窗口是 |J(Bh/M+kl/j)|≤F；格距为 JB/M，
   单行尾 O(T^ε(1+M/(JB))F^{1−L})。乘 J/|j| 并恢复整段 j，
   得 **O(T^ε C P(JS+X log(2S))F^{1−L})
   ≪O(T^{7−ν+ε}F^{1−L})**。字面整数端点为
   ceil[(M/B)(−F/J−kl/j)]≤h≤floor[(M/B)(F/J−kl/j)]。
   M>1 时 h=0 由单位条件排除；不能据此说原零模为零。
5. l 是紧支撑光滑分片，零延拓不产生硬端点。B-shell 的
   半开端点和 Fourier 窗口的闭端点均已包含。M 均值的大除数
   延伸、u=1 过渡由 JT9 支付；不对 n=0 使用该定理。U=1 的
   整数分解、d=1、κ=e=1 在第1节先处理。有限 T 的剩余范围
   可调常数，但不包含 K≈1 的渐近分片。

取 L 充分大后上述变换尾任意幂次小。第3、4项属于同一 core
的两种精确表示，不是要重复添加的两个主项。**原 AFE 的独立
物理尾没有因这些变换尾快速衰减而自动得到控制。**

## 6. 有限验证与尚未关闭的目标

配套脚本只提供三个有限接口：精确有理参数 GP2；完整频率
成本 GP7（不输出自动 coverage 标志）；GP11 的联合除数枚举。
测试独立穷举 j,B,h 方程核验枚举，保留共享素因子、负斜率、
空区间和所有端点。另以一个在原点为零的 Schwartz 函数检查
GP9 的 J Jacobian；数值检验不证明实际 symbol 或任何解析尾界。

本节是新的可证明参数覆盖，不是把剩余问题另命名为一个新
gate。完整目标仍须处理 GP8 外的联合 µ(M)µ(B) kernel、一般
q 及其他尺度，并回到含 canonical zero Gram、非零补集、
两个 reflection mixed 项与全部物理尾的同一个 signed operator。
仅控制某个 Möbius 向量对弱于控制所有向量的算子范数，二者
不能无条件说成等价。完整 coupled-kernel gate 尚未证明。
