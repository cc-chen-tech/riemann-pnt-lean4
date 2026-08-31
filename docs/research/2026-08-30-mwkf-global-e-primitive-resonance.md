# 全部 e 的双 Möbius 重组与 primitive 精确共振

白话结论：在 q=1 的平衡顶层，先恢复全部 e，再完成共同 n
频率，可以把 µ(e)µ(b) 合并回 µ(B)，并把平方自由 M 的
Ramanujan 系数还原为 µ(M)。新表示中的**整个精确共振子项**
（包括全部 e 和长 b）满足 T^{3+ε} 预算。非零 determinant
补集的绝对值账本仍为 T^{5+ε}，尚差 T²。
**这不覆盖整个 κ 分片，不求值原 canonical zero Gram，也不是
完整 coupled-kernel gate 或 twisted-moment 证明。**

以下 GE1–GE12 以 [IC2](2026-08-30-mwkf-inverse-c-signed-roundtrip.md)、
[JT2–JT6](2026-08-30-mwkf-joint-type-ii-density.md) 和
[GU2–GU4](2026-08-30-mwkf-general-unit-type-ii.md) 为输入。
所有结论针对其中已指定的实际光滑 core，不把独立物理尾并入
一个未经验证的光滑幅度。原 hδ 耦合仍在实际核内。

## 1. 范围与没有过渡余项的整数分解

固定 q=1，一个完整 κ 光滑块 w(κ/K)，以及非零 k,l 分片。
令 P=K₁K₂，X=R/K；本节分析范围为
\[
 R=S=T^3,\quad HL\asymp T^5,\quad K\asymp P\asymp Z=RP/S\asymp T,
 \quad |k|\asymp K_1,\ |l|\asymp K_2.                 \tag{GE1}
\]
常数固定，T 足够大；有界 T 由调整常数处理。实际支撑给
Ae≈X、e≲X、D=S/e≳T，因此 d≈D 的所有整数都大于1。
K>2 也使 κ=e=1 的独立纠正项为空。

只展开 µ(d)，取 U=1 并恢复全部 b（包括原 Type-I 和 Type-II）：
\[
 \mu(d)=\mathbf1_{d=1}-\sum_{\substack{bm=d\\m>1}}\mu(b).
                                                               \tag{GE2}
\]
这是 Σ_{b|d}µ(b)=1_{d=1} 的精确有限恒等式。可同时乘
1_{(d,Ae)=1}，得到 (b,Ae)=(m,Ae)=1；不添加 µ²(m)。
令 χ 是固定光滑函数，χ(t)=0 对 t≤1，χ(t)=1 对 t≥2。
**仅在正整数上**，χ(m)=1_{m>1}，故 GE2 的 m>1 可由 χ(m)
精确替换。不存在整数 1<m<2，没有 transition boundary；
m=1 的值是0、m=2 的值是1。d=1 的端点先保留，再由上面的
实际支撑排除，而不是在 Poisson 之后删去。

这不是宣称 Type-II 消失：其长 b 全部包含在下面的主和中。
若只保留 b>V，必须携带该 sharp mask；本节不这样做。

## 2. 把全部 e 合回两个平方自由整数

非零项有平方自由 A,e,b，且 (A,e)=(b,Ae)=1。置
\[
 M=Ae,\quad B=eb,\qquad e=(M,B),\quad A=M/e,\quad b=B/e.
                                                               \tag{GE3}
\]
这是原三元组与任意平方自由正整数对 (M,B) 之间的双射。
反向互素条件由平方自由性和 e=(M,B) 推出。
特别地，**不能补上 (M,B)=1**；这会删去所有 e>1。
符号满足 µ(e)µ(b)=µ(B)。

先恢复所有人工 e/A/b dyadic partitions，使其总和回到1。
未恢复的截断必须沿 GE3 拉回，不能冒充同一个无掩码 symbol。
保留的是固定原 κ,k,l 光滑分片以及真正的物理权重。
在 JT2 的 t,x 变量中，幅度正好变为
\[
 \mathfrak a_{M,B}(t,x)
 =\frac{w(t)}x\widetilde G\left(\frac{tKM}{R},x,
               \frac{kH}{Sx},\frac{lL}{Sx}\right)\chi(Sx/B),
 \quad t\in(1/2,3),\quad x\in(1,2).                 \tag{GE4}
\]
因此 M≈X、1≤B<2S，幅度不再依赖 e 的分配。χ 的归一化
导数只在 Sx/B 的固定紧区间非零，所以没有大 B 导数损失。

完成 m 的单位掩码后，全部 v|M 用共同 n=(M/v)ℓ 重组。
JT 的参数是
\[
 z_0=KMkl/S,\quad \eta=jK/z_0,\quad
 \xi=nS/(BM),\quad \sigma=\xi/z_0 .                \tag{GE5}
\]
它们以及 JT4 的**精确** symbol 都与 v、e 分配无关。
顶层上 j≈Z/K≈1，critical cutoff 使 n/B 位于固定紧集且离开0；
对 n/B 的每个固定阶导数一致 O(T^ε)。完整 JT symbol 而非
stationary-phase leading term 被记为 Ψ_{M,B,j,k,l}(n/B)。
它含 θ、η、原始核和 GE4 中的 χ，因而 Ψ(0)=0。

原 IC2 的负号与 GE2 的负号相消。GU2 给出的逐 n 系数为
\[
 \frac{HL}{R}\frac{\mu(B)\kappa_M(n)}{MB|j|},\qquad
 \kappa_M(n)=\sum_{d\mid(M,n)}\mu(d)d ,             \tag{GE6}
\]
求和限平方自由 M,B。直接核验：原系数是
HL/R·µ(A)µ(b)µ(v)/(ebv|j|)，而
µ(A)Σ_{v|M,M/v|n}µ(v)/v=µ(e)κ_M(n)/M。
故实际 critical core 等于
\[
 \mathcal P_{\rm crit}=\frac{HL}{R}
 \sum_{\substack{M\asymp X,\ B<2S\\M,B\ {m squarefree}}}
 \frac{\mu(B)}{MB}
 \sum_{k,l}\sum_{j\ne0}\frac1{|j|}
 \sum_{n\ne0}\kappa_M(n)\Psi_{M,B,j,k,l}(n/B)
                       e(-nkl/(jB)).              \tag{GE7}
\]
这是整个 e 家族的一次有限重组，没有额外 e-shell 数量；
但重组本身不提供任何幂次 saving。

## 3. 全 n Fourier 完成后的 primitive 双 Möbius 和

约定 \(\widehat\Psi(y)=\int\Psi(x)e(-xy)dx\)。对平方自由 M，
κ_M(n)=µ(M)c_M(n)，其中 c_M(n)=Σ_{u mod M,(u,M)=1}e(nu/M)。
对每个 u 用 Poisson，再令 h=Mv−u，得到精确恒等式
\[
 \frac1B\sum_{n\in\mathbb Z}\kappa_M(n)\Psi(n/B)e(-nkl/(jB))
 =\mu(M)\sum_{\substack{h\in\mathbb Z\\(h,M)=1}}
              \widehat\Psi(Bh/M+kl/j).            \tag{GE8}
\]
映射 (v,u)↔h 是双射；n=0 因 Ψ(0)=0 可无误差加入。
新 h 是 **n 的 Fourier 指标**，不是原 AFE 的 hδ 标签。
特别地，M>1 时 h=0 不满足单位条件；这不表示原零频消失。

代回后是保留两个 Möbius 符号的统一表达式
\[
 \mathcal P_{\rm crit}=\frac{HL}{R}
 \sum_{M\asymp X}\frac{\mu(M)}M\sum_{1\le B<2S}\mu(B)
 \sum_{k,l}\sum_{j\ne0}\frac1{|j|}
 \sum_{(h,M)=1}\widehat\Psi_{M,B,j,k,l}(Bh/M+kl/j).
                                                               \tag{GE9}
\]
µ 非零时才使用该平方自由 symbol。M,B,j,k,l 都有限，h 和
绝对收敛，但还不是字面有限和。

### 明确支付 Fourier 尾和原变换补集

取固定 0<δ<1，F=T^δ。由统一 Schwartz 界，任意 J>1 有
\[
 \sum_{|Bh/M+kl/j|>F}|\widehat\Psi(Bh/M+kl/j)|
 \ll_J T^\varepsilon(1+M/B)F^{1-J}.               \tag{GE10}
\]
移位格间距为 B/M；其中的整数 +1 必须保留。乘全部外层后，
Σ_{M≈X}1/M≪1，Σ_{B<2S}(1+M/B)≪S+X log(2S)，
j 只有固定个数。因此总代价
\[
 \ll T^\varepsilon\frac{HL P}{R}(S+X\log(2S))F^{1-J}
 \ll T^{6+\varepsilon+\delta(1-J)}.
\]
任给 A₀>0，选择足够大 J 得 O(T^{-A₀})。窗口包含等号端点，
无整数舍入遗漏；字面 h 范围为
ceil[(M/B)(−F−kl/j)]≤h≤floor[(M/B)(F−kl/j)]。

JT6 的整个非critical 部分在本范围也快速衰减。显式粗计费为
每个 e,A,b,k,l 的 C_e·T^ε Z^{1-L}(K+Z)/D，再用
Σ_e #(A≈X/e)#(b<2S/e)≪XS，可得 O(T^{7-L+ε})。
ℓ=0 的全部 j 使用 JQ6，计费 O(T^{6-J+ε})；b 的1/b只花对数。
选择 L,J 足够大即可。两者都不是原 canonical zero Gram。
这些尾仅是 IC2 光滑 core 的变换尾，不能代替原 AFE 尾。

## 4. 整个精确共振子项达到预算

在 GE9 中定义整数
\[
 \Delta=jBh+Mkl,
 \qquad Bh/M+kl/j=\Delta/(jM).
\]
令 \(\mathcal M_{\rm prim}\) 为 Δ=0 的全部项。
因 (h,M)=1，Δ=0 强制 M|jB。置
\[
 d=(|j|,M),\quad M=dM_1,\quad j=dj_1,\quad (j_1,M_1)=1.
\]
所有解唯一参数化为
\[
 B=M_1r,\quad j_1rh=-kl,\quad (h,M)=1,
 \quad r\ge1,\quad B\ {m squarefree},\quad B<2S. \tag{GE11}
\]
若 j₁∤kl，解为空；否则 r| |kl/j₁|。
由于 M,B 平方自由，(d,M₁)=(r,M₁)=1，且
µ(M)µ(B)=µ(d)µ(r)。允许 r 与 d 共有素因子。
注意只得 M|jB，不是一般的 M|B。

因此显式共振项就是 GE9 将 B,h 用 GE11 替换、将变换权置为
\(\widehat\Psi_{M,M_1r,j,k,l}(0)\)、将 µ(M)µ(B) 换为 µ(d)µ(r)
的有限除数和。所有实际支持仍在 Ψ 内，不作正性或抵消假设。

**共振子项定理。** 在 GE1–GE5 的实际 core 假设下，
\[
 |\mathcal M_{\rm prim}|
 \ll_\varepsilon \frac{HL P}{R}T^\varepsilon
 \asymp T^{3+\varepsilon}.                        \tag{GE12}
\]
证明：固定 M,j,k,l，r 的个数至多 τ(|kl|)≪T^ε；
|Ψhat(0)|≤||Ψ||₁≪T^ε。再付 Σ_{M≈X}1/M≪1、
Σ_{j≈1}1/|j|≪1 和 #(k,l)≪P。ε 可事先分配给各有限因子。
证明包含全部 e 与全部允许 B，包括原长 b；没有另乘 e 数量。

此精确共振是**新 Fourier 表示中的一个子项**。
它既不等于 GU9 的平方自由均值，也没有被识别为原 canonical
zero Gram、反射边界或 AFE diagonal；不能把这些不同项相互删除。

## 5. 剩余有限 signed 核与真实成本

保留 GE10 的有限窗口但删除 Δ=0，定义
\[
 C_F(M,B)=\frac1M\sum_{k,l}\sum_{j\ne0}\frac1{|j|}
 \sum_{\substack{(h,M)=1\\0<|jBh+Mkl|\le |j|MF}}
   \widehat\Psi_{M,B,j,k,l}\left(\frac{jBh+Mkl}{jM}\right).
\]
于是光滑 core 的完整分解为
\[
 \mathcal P_K=\mathcal M_{\rm prim}
       +\frac{HL}{R}\sum_{M,B}\mu(M)\mu(B)C_F(M,B)
       +\mathcal E_{\rm freq}+\mathcal E_{\rm noncrit}+\mathcal E_{\ell=0}.
\]
三项误差如上分别计费，整数端点在 GE2 处理。
**没有证明 C_F 零行和/零列和，也没有证明其目标算子范数。**
只对这对 Möbius 向量的双线性界通常弱于全体向量的 ℓ²→ℓ²
范数界，不能无条件称二者“等价”。原统一 signed operator
还包含 canonical zero Gram 和两个 reflection mixed 项。

可以精确看出绝对值为何仍不够：固定 M,j,k,l，按 Δ 求和，
jBh=Δ−Mkl。M>1 时 h=0 被单位条件排除；若 Δ=Mkl 则无解。
其余每个 Δ 的正 B 个数至多 τ(|Δ−Mkl|)。在有限窗口内所有
整数均为 T 的固定幂，且
Σ_Δ(1+|Δ|/(|j|M))^{-J}≪M。因此整个 h,B 的绝对值成本
至多 M T^ε；恢复其余外层后是
\[
 T^\varepsilon\frac{HL P X}{R}=T^{5+\varepsilon}.
\]
这没有偷偷损失额外 e 次幂，但也还没有省去所需的 T²。
非零 Δ 不自动产生振荡消去。例如 M=101,B=1011,j=1,kl=10,
h=−1 有 (h,M)=1、Δ=−1、频率−1/101；它只是算术支撑示例，
不声称实际核在该点非零。

## 6. 谱输入的位置与未解决项

[Bettin–Chandee, Corollary 1](https://arxiv.org/pdf/1502.00769)
确实处理非零 determinant，允许两边算术系数，同时要求另外
两变量具有给定光滑导数界。当前 Δ 中的 kl 是真实带权乘积，
不是一个可直接当作光滑权的新变量；(h,M)=1 与 Ψ 的联合依赖
也须保留。固定 k 后映射为 n₁=kM、n₂=jB，只是候选入口，
仍须处理支撑子格、单位掩码、权重分离以及整个 Δ,k 的成本。
本文没有建立这些步骤，更没有从该 corollary 宣称新覆盖。
其 Theorem 1 的指数相位是模逆 Kloosterman fraction，也不能
直接替代 GE7 中的普通有理载波。

下一项真实任务是估计上述保留 µ(M)µ(B) 的非零 Δ 联合核，
同时继续核验一般 q 与非顶层尺度的转移。现有 GU/JQ 子域覆盖
可以择优使用，但不能将 saving 相乘，也不能与 GE12 重复扣除
未证明相等的密度。完整 coupled-kernel gate 仍未证明。

有限脚本只检验 GE2、GE3/GE6、Ramanujan 符号、GE11 和有限
primitive 窗口的端点；它们不证明解析 symbol、尾界或算子范数。
