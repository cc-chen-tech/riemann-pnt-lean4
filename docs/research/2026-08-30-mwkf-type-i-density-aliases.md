# 真实 Type-I 的连续密度与互素别名

后续 [JQ1–JQ18](2026-08-30-mwkf-joint-kappa-type-i.md) 保留整个
κ 与 quotient 联合变换，将本节 BV 别名成本进一步降为
`ρDUV min(√Z,Z/K)`。平衡顶层 K≈Z≈T、U,V 为固定对数幂
时，这个 Type-I 部分达到 T^{3+ε}；完整 Type-II 与 gate 仍未证明。
下文的较弱 BV 估计保留为独立有效的基线。

白话结论：可以结清一部分连续主项，但不能将其离散补集一并
删除。对 SK 的实际无符号 Type-I 余因子，连续密度没有驻点，
因而快速衰减；互素条件则产生完整的非零别名。本节证明这一个
Type-I 部分的物理上界和一个不平衡区域的快速衰减条件，并保留
精确小端点。**没有证明完整 coupled-kernel gate。**

在平衡顶层 `K≈T,e=1,UV=T^β` 上，Type-I 部分的界为
`T^{4+β+ε}`，例如 β=1/2 给 `T^{9/2+ε}`。SK 的 `T^{5+ε}` 是
整个分片的界；本节较小的界仅适用于这个 Type-I 部分，不能据此
改写整个分片的状态，也不能与其他估计的节省相乘。

## 1. 仅分解真实 µ(d)，保留 µ(A) 和实际核

沿用 [SK1–SK4](2026-08-30-mwkf-smooth-kappa-resonance.md) 的
`X=R/(eK),D=S/e,C=HL/(Re),ρ=HLP/S²,Z=RP/S`。本节取实际
d 方向的**光滑分片**；固定 A,κ,k,l 后写

\[
 Q=Aeq,\quad z={\kappa Akl\over D},\quad
 g(d)={1\over d}a(d/D)e(zD/d),\qquad
 \Psi_z(x)={a(x)\over x}e(z/x).                       \tag{TI1}
\]

这里 `a∈C_c^∞((1,2))` 是实际 `w(κ/K) Gtilde` 连同光滑 d 分片，
不是新任意算术序列。所需归一化导数为 `T^ε`；在对数 Fourier
core 上，`kH/(ed),lL/(ed)` 的链式法则只付已登记的对数成本。
固定符号的非零 k,l 给 `|z|≈Z`。所有参数 Q 等为 T 的固定幂。

原条件 `(e,Aq)=1` 不动，d 的条件为 `(d,Q)=1`。尚未取模的
物理 Type-I 部分是 `−μ²(e)C Σ_{A,κ,k,l} μ(A) I_Q[g]`，其中
`I_Q[g]=Σ_d I_{U,V}(d)1_(d,Q)=1 g(d)`，I 是 SK18 的带负号
Type-I 系数。µ(A)、µ(d) 至此都没有作 Cauchy；原 `hδ` 仍在
同一个 `G` 的双 Fourier 核中。

## 2. 完成无符号 quotient 时必须补回的小端点

对任意有限支撑 g 和正整数 U,V,Q，完全有限地有

\[
 \begin{aligned}
 I_Q[g]={}&-\sum_{\substack{c\le U,b\le V\\(bc,Q)=1}}
       \mu(c)\mu(b)\sum_{\substack{m\ge1\\(m,Q)=1}}g(bcm)
       +E_{V,Q}[g],\\
 E_{V,Q}[g]={}&\sum_{\substack{b\le V\\(b,Q)=1}}\mu(b)g(b).
                                                               \tag{TI2}
 \end{aligned}
\]

证明：在 `I(d)=−Σ_{ab=d,a>U,b≤V}c_U(a)μ(b)` 中，补齐 a≤U。
因为 `c_U(a)=1_{a=1}` 对 a≤U 成立，所补的唯一项是 b=d≤V。
再展开 `c_U(a)=Σ_{c|a,c≤U}μ(c)`、a=cm，即得式子。互素条件
逐因子保留。m 允许非 squarefree；不能添加 `μ²(m)`。

若整个光滑支撑在 d>V，E=0。例如上述 a 支撑 (1,2) 且 D≥V
就足够，**不必假设 D>UV**。若不满足，保留 E；不插入一个
硬 `d>V` 截断后继续使用无边界的光滑估计。SK18 的 small 部分
和其他 Type-II 部分仍按原式登记。

## 3. 零频连续密度的精确系数

置 B=bc。若 (B,Q)=1，有限容斥及 Poisson 给出

\[
 \begin{aligned}
 \sum_{(m,Q)=1}g(Bm)
 &=\sum_{v\mid Q}\mu(v)\sum_{n\ge1}g(Bvn)\\
 &=\sum_{v\mid Q}{\mu(v)\over Bv}
            \sum_{\ell\in\mathbb Z}
                 \widehat\Psi_z\left({\ell D\over Bv}\right)\\
 &={w(Q)\over B}\widehat\Psi_z(0)+\mathcal A_{B,Q}(z),
 \qquad w(Q)={\varphi(Q)\over Q}.                    \tag{TI3}
 \end{aligned}
\]

Fourier 用负号。`g(Bvn)=D^{-1}Ψ_z(Bvn/D)`，所以 Jacobian 恰是
`1/(Bv)`，不是 D/(Bv) 或额外 S^{-1}。右侧 ℓ 和无限且绝对收敛；
`𝒜` 包含全部 ℓ≠0，带 `μ(v)` 符号。

定义 `M_U(Q)=Σ_{c≤U,(c,Q)=1}μ(c)/c`。则 TI2 中的连续部分
**精确**是

\[
              -w(Q)M_U(Q)M_V(Q)\widehat\Psi_z(0).    \tag{TI4}
\]

由于 x 支撑在 (1,2)，相位 z/x 的导数从不为零。任意固定 J
次分部积分给

\[
       |\widehat\Psi_z(0)|\ll_J T^\varepsilon(1+Z)^{-J}.
                                                               \tag{TI5}
\]

这是快速衰减，不是恒等于零。例如 z=1/16、a≥0 非零时积分
实部严格正。若 a 有硬端点，则会留下端点积分项，不能直接用
TI5。TI4 也不是 canonical zero Gram，更不是原完整零频主项。

## 4. 完整别名的无条件 BV 界与物理成本

格点 Euler 求和对每个 v 给
`|Σ_n g(Bvn)−(Bv)^{-1}∫g|≤Var(g)`。缩放不改变总变差，且

\[
 \operatorname{Var}(g)\ll T^\varepsilon{1+Z\over D},
 \qquad
 |\mathcal A_{B,Q}(z)|\ll T^\varepsilon{1+Z\over D}. \tag{TI6}
\]

第二式用了 `Σ_{v|Q}|μ(v)|=2^{ω(Q)}≪T^ε`，没有用互素掩码的
平均来删掉 v。此处误差独立于 B，却不能再省去 c,b 的数量。
因此在 E=0 时，整个一个 Type-I 部分满足

\[
 \begin{aligned}
 |\mathcal B^{I_d}_{e,K}|
 &\ll_J T^\varepsilon\rho
       \{D^2(1+Z)^{-J}+D(1+Z)UV\}.                 \tag{TI7}
 \end{aligned}
\]

证明：TI4 的有限调和和至多对数平方，TI6 对 c,b 至多 UV 对
求和。其余物理外层为
`C·XKP=ρD²`，包含整个 κ 和两短频率、d^{-1} 的尺度。这里才
支付 µ(A) 的绝对值。若 E≠0，须另加其原 signed 物理贡献；
其绝对上界一般可达 `T^ερD²`，本节不宣称它已小。

对整个 `e≈E₀` 相加，有

\[
 \sum_{e\asymp E_0}|\mathcal B^{I_d}_{e,K}|
 \ll_J T^\varepsilon\rho
 \{S^2E_0^{-1}(1+Z)^{-J}+S(1+Z)UV\}.               \tag{TI8}
\]

须对所有 e 满足上述端点/平滑条件。相应成本分别使用
`Σ_{e≈E₀}e^{-2}≪E₀^{-1}` 和 `Σ_{e≈E₀}e^{-1}≪1`。
在平衡 Z≈T、D=T³、UV=T^β 时，TI7 是 `T^{4+β+ε}`；β<1
改善这个 Type-I 部分的直接 T⁵ 预算，仍不达到目标 T³。

## 5. 可覆盖的不平衡短 Type-I 区域

在 TI3 的 ℓ≠0 项中令 `ξ=ℓD/(Bv)`。若 `|ξ|≥2|z|`，则
相位 `z/x−ξx` 的导数大小至少 |ξ|/2；固定阶高导数除以
|ξ| 也一致有界。所以

\[
        |\widehat\Psi_z(\xi)|\ll_J T^\varepsilon|\xi|^{-J}
                    \quad(|\xi|\ge2|z|).           \tag{TI9}
\]

故只要固定 η₀>0 且

\[
    Z\ge T^{\eta_0},\qquad {UV\,Q\,Z\over D}\le T^{-\eta_0},
                                                               \tag{TI10}
\]

全部 ℓ≠0 都落在 TI9 区域。选足够大 J、支付多项式外层后，
TI5 和 TI9 使这个完整 Type-I 部分为任意负幂。Q 本身是充分
上界；可以用 rad(Q) 改进，但本节不依赖该改进。

具体地，对每个 B,v，若截断 `|ℓ|≤L_{Bv}`，并且
`L_{Bv}≥max(1,2|z|Bv/D)`，剩余的单行尾至多

\[
 T^\varepsilon\sum_{v\mid Q}{|\mu(v)|\over Bv}
          \left({Bv\over D}\right)^J L_{Bv}^{1-J}.  \tag{TI11}
\]

再按 TI2 支付全部 c,b 和物理外层即可；没有把无限 Poisson
和说成精确有限和。硬 quotient 端点只在 TI2 的 E 中处理。

将 `R=T^r,S=T^s,e≈T^η,K=T^ν,q=T^χ,Z=T^ζ,UV=T^β` 代入，
由于 `Q=Aeq≪Rq/K`，TI10 的指数条件是

\[
                 \beta+r-\nu+\chi+\zeta<s-\eta,    \tag{TI12}
\]

不等式必须有固定正裕量，ζ>0。在 SK 尚未排除的 ν≤ζ 区域，
平衡 r=s 时没有内点；不能借此宣称平衡门槛关闭。
不平衡例子则有真正覆盖：`R=T²,S=T³,HL=T⁴,P=T²,K=T,e=q=1,
U=V=T^{1/4}`，TI12 左边为 5/2、右边为 3，端点也远离支撑。
这里只覆盖 d-Type-I 部分，不删除同一个原区块的 Type-II。

## 6. 未覆盖的别名有明确驻相与符号结构

若 z>0，驻点只可能来自 ℓ<0，且

\[
       x_0^2=-{zBv\over\ell D}\in[1,4],\qquad v\mid Q.
                                                               \tag{TI13}
\]

z<0 时符号反转。特别是 `Bv≥D/|z|`，驻相别名只来自大除数。
这仍是一整个 signed 和，不是孤立项下界。

平衡 e=q=1 时 Q=A，v|A。因为未分解的 µ(A) 保证 A squarefree，
在 A=va₀ 上精确有 `μ(A)μ(v)=μ(a₀)`；全变量写法还保留
`μ²(v)1_(a₀,v)=1`。因此不能把 µ(A) 的完整长度再次当作独立
Möbius 消去。原整数 quotient 坐标为 d=Bvm，相位变成

\[
                  e\left({\kappa a_0kl\over Bm}\right),
                  \qquad (B,va_0)=1,                \tag{TI14}
\]

但实际幅度、1/(Bvm)、v 的 squarefree 限制及所有原支撑都在。
K≈T 时，驻相条件只允许 `a₀=A/v≪B`（常数取决于固定支持）。
这是下一步应重组的短比率/长共同因子结构；没有在这里证明其
所需的 signed 界。

## 7. 新核对的已发表范围，及完整目标边界

本轮核对 [Srivastav, arXiv:2505.07803v2, Theorem 1](https://arxiv.org/html/2505.07803v2#S1.Thmtheorem1)。
它要求 `α=a/q₀+δ/x`、`q₀≤x^{2/5−h}`、
`|δ|≤x^{1/5+h}/q₀`，其中 `0<h≤1/10`。q₀ 是论文的逼近
分母，不是 TI1 的互素参数 Q 或原 gcd q。

对当前 **e=1 的平衡顶层**剩余 `0≤ν≤1` 的固定 A 行，
`x≈X=T^{3−ν}, |α|≈T^{ν−2}, |α|x≈T`。
对所有允许 q₀，
`|α|q₀≪T^{−4/5+3ν/5−h(3−ν)}=o(1)`。
另一方面论文要求
`|a−q₀α|≤x^{−4/5+h}=o(1)`，强制 a=0、q₀=1。
此时 |δ|≈T，却有
`x^{1/5+h}≪T^{(3−ν)3/10}≤T^{9/10}`，矛盾。
所以**不是仅最近的倒数逼近失败，而是该定理的任何允许逼近
都不覆盖这个原 A 行**。这不否定其他分解后行的可能应用；也不
削弱已成立的 BRZ/IC7，后者接受另一种分母范围。

| 输入 | 实际覆盖 | 未证明部分 |
|---|---|---|
| TI3–TI8，初等容斥/Euler/非驻相 | 连续 Type-I 密度及完整 BV 别名上界，保留端点 | 平衡目标尚差固定幂，Type-II 不被估计 |
| TI9–TI12，完整 quotient Poisson | 指定不平衡短 Type-I 多面体有快速衰减 | 平衡剩余无内点，大 v 驻相别名仍在 |
| Srivastav Theorem 1，上述实际行核查 | 平衡 ν∈[0,1] 原 A 行无覆盖 | 不能以“无对数损失”替代不满足的输入范围 |
| BRZ/IC7 与 SK | 保留各自真实范围；可取已证较好上界 | 不相乘，也不以局部界替代整个 signed operator |

本节完成的是 SK 剩余真实 Type-I 的一部分求值与估计。完整
canonical zero Gram、reflection 两个交叉项和真正中心化算子
仍按 [PA](2026-08-30-mwkf-physical-reflection-adapter.md) 保留；
TI4 不是它们的替代品。物理硬端点、完整剩余 Type-II 及大 v 的
联合 signed saving 均未解决，完整 twisted moment 仍未证明。
