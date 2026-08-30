# 全 κ 区块的联合 Gram：LCM 单位密度平方和与别名频率

白话结论：这次不再逐条固定 `κ,d,k,l` 后估计 Möbius 行，而是把整个
`κ` 区块与两个短乘积频率一起放进同一个 Gram。单位条件产生一个
可以精确对角化的 LCM 密度核，同时留下不能删除的非零别名频率。
下面证明零 determinant 部分、完整密度部分及别名部分的上界，并
恢复真实物理成本。它改善部分区块的上一轮逐行界，但**未改善目前
完整问题的 BBLR 缺口，也未证明 coupled-kernel gate**。

这里的连续密度零模不是原 canonical zero Gram；整数 determinant
为零也不是删除所有其他 Poisson 频率的理由。完整 AFE、reflection
及 mixed 项仍沿用 [PA 账本](2026-08-30-mwkf-physical-reflection-adapter.md)。

## 1. 从实际 IC2 到一次联合 Cauchy

从 [IC2](2026-08-30-mwkf-inverse-c-signed-roundtrip.md) 出发，固定
squarefree `e` 及原共同 gcd `q`，保留整个 `κ≈K`、两个非零频率
`|k|≈K₁,|l|≈K₂` 区块。令

\[
 P=K_1K_2,\quad M=KP,\quad X={R\over eK},\quad D={S\over e},
 \qquad C={HL\over Re}.
 \tag{JG1}
\]

假设 `X,D,M≥1`、全部参数至多为 `T` 的固定幂，归一化核的所需
导数至多为 `T^ε`。取非负 `χ∈C_c^∞((1/2,3))`，其 seminorm
一致有界，作为 `A≈X` 分片。可在有限重叠分片中选择这样的 χ；
原 signed 核仍留在下面 `b` 内，不要求其非负。

**在取模或平方之前**按 `n=κkl` 合并：

\[
 b_{d,n}(u)=\sum_{\substack{\kappa\asymp K,\ |k|\asymp K_1,
                    |l|\asymp K_2\\\kappa kl=n}}
 W_{\kappa,k,l}\,
 \widetilde G\left({\kappa\over K}u,{ed\over S},
                         {kH\over ed},{lL\over ed}\right).
 \tag{JG2}
\]

`W` 表示该分片实际供应的有界权；若还有 `u` 依赖，也须具有同样
导数控制。不将它换成任意算术序列。对每个固定阶数 `j`，
`||∂_u^j b_{d,n}||∞≪T^ε τ₃(|n|)`；因为每个正因子三元组有
至多常数个符号选择，且 `κ/K≈1`。原 `a=hδ` 已经通过原耦合核
的双 Fourier 变换保留，不被新任意系数替换。

先考虑 `κe>1` 的 bulk。`κ=e=1` 的独立端点仍为 IC2 中两个
单位掩码 `d` 与 `dq` 的 signed 差，不能丢弃。bulk 字面为

\[
 \begin{aligned}
 \mathcal S_{e,K}&=-\mu^2(e)C\sum_A\mu(A)\chi(A/X)F_A,\\
 F_A&=\sum_{\substack{d\asymp D\\(d,eq)=1}}{\mu(d)\over d}
    1_{(A,ed)=1}\sum_{|n|\asymp M}b_{d,n}(A/X)e(An/d),\\
 |\mathcal S_{e,K}|^2&\ll C^2X\,\mathcal E,\qquad
 \mathcal E=\sum_A\chi(A/X)|F_A|^2.
 \tag{JG3}
 \end{aligned}
\]

只有最后一行使用 Cauchy：至此 `μ(A),μ(d)` 都未取绝对值。此后
`μ(A)` 被行范数支付，Gram 内仍有 `μ(d₁)μ(d₂)`。所以 (JG3)
是充分上界，不是原 Möbius 标量目标的等价命题。

## 2. 单位完成：连续密度之外还有全部别名

对 `Q≥1`、紧支撑 `f∈C_c^∞`、实数 `α`，设 `w(Q)=φ(Q)/Q`。
约定 Fourier 用 `e(−uξ)`，则

\[
 \begin{aligned}
 K_Q(f,\alpha)&:=\sum_A f(A/X)1_{(A,Q)=1}e(\alpha A)\\
 &=X\sum_{v\mid Q}{\mu(v)\over v}
                  \sum_{m\in\mathbb Z}\widehat f(X(m/v-\alpha))\\
 &=Xw(Q)\widehat f(-X\alpha)+\mathcal A_Q(f,\alpha).
 \tag{JG4}
 \end{aligned}
\]

`𝒜_Q` 是上一行的**全部 `m≠0` 项**。除数和有限，Poisson 和
绝对收敛。有限 cutoff 外的和就是相应尾，未视为零。
另由格点 Euler 求和有一个无频率截断、带明确端点成本的界：

\[
 |\mathcal A_Q(f,\alpha)|
 \le\sum_{v\mid Q}|\mu(v)|\,
       \operatorname{Var}_u\bigl(f(u)e(X\alpha u)\bigr)
 \le\tau(Q)\bigl(\|f'\|_1+2\pi X|\alpha|\|f\|_1\bigr).
 \tag{JG5}
\]

证明：对每个 `v`，格点和 `Σ_j g(vj)` 与 `v^{-1}∫g` 的差
至多为 `Var(g)`，这里 `g(t)=f(t/X)e(αt)`。把所有除数误差
带符号相加即可。若用硬区间 `(a,b]` 而非平滑 f，变差还包括
两端跳跃，给出 `τ(Q)(2+2π|α|(b−a))`，不能删除整数 `+1`。

例如 `Q=6,α=1/6`，在 `(0,6]` 上单位和为 1，连续密度积分为
0；整个值来自非零别名。这只是 BV 有限见证，不把硬区间宣称为
紧支撑光滑核。

展开 (JG3)，每个 pair 的参数为

\[
 Q_{12}=[ed_1,ed_2],\quad
 \alpha_{12}={n_1\over d_1}-{n_2\over d_2},\quad
 f_{12}(u)=\chi(u)b_{d_1,n_1}(u)\overline{b_{d_2,n_2}(u)}.
 \tag{JG6}
\]

于是 `𝓔=𝓔₀+𝓔_alias` 精确成立，其中

\[
 \mathcal E_0=X\int\chi(u)
 \sum_{d_1,d_2}{\mu(d_1)\mu(d_2)\over d_1d_2}
 w([ed_1,ed_2])
 \sum_{n_1,n_2}b_{d_1,n_1}(u)\overline{b_{d_2,n_2}(u)}
                         e(Xu\alpha_{12})\,du.
 \tag{JG7}
\]

所有原 `d` 支持/互素限制仍在。由 (JG5)、`|α₁₂|≪M/D` 及
`Σ_{d≈D}1/d≪1`，有一致的真实上界

\[
                 |\mathcal E_{\rm alias}|
       \ll T^\varepsilon M^2(1+XM/D).
 \tag{JG8}
\]

这已包含 `κ≈K` 的全部计数，不能再把 `M=KP` 写成 `P`。
别名项是 Hermitian signed 误差，不是一个正 Gram。

## 3. LCM 单位密度的完整平方和

对任意正整数 `a,b`，不要求 squarefree，有

\[
 w([a,b])=w(a)w(b){(a,b)\over\varphi((a,b))}
        =w(a)w(b)\sum_{r\mid(a,b)}{\mu^2(r)\over\varphi(r)}.
 \tag{JG9}
\]

逐素数核对即可。因此对任意有限复系数 `z_a`，

\[
 \sum_{a,b}z_a\overline{z_b}w([a,b])
   =\sum_r{\mu^2(r)\over\varphi(r)}
                   \left|\sum_{r\mid a}w(a)z_a\right|^2.
 \tag{JG10}
\]

这也等于对共同周期内整数 `A` 的
`|Σ_a z_a 1_(A,a)=1|²` 的平均。将 (JG10) 用在 (JG7) 得到

\[
 \boxed{\mathcal E_0=X\sum_r{\mu^2(r)\over\varphi(r)}
 \int\chi(u)\left|\sum_{\substack{d\asymp D\\r\mid ed}}
 {\mu(d)w(ed)\over d}\sum_{|n|\asymp M}
                  b_{d,n}(u)e(Xun/d)\right|^2du\ \ge0.}
 \tag{JG11}
\]

这是当前单位密度核的精确 LCM 对角化；不是把原 reciprocal-LCM
主项定理直接套到一个不同核。也未建立它与原 canonical zero
Gram、AFE diagonal 或 reflection 交叉项之间的抵消。

## 4. 零 determinant 的计数与完整密度的大筛界

在 (JG7) 中按整数
`Δ=n₁d₂−n₂d₁` 分成 `𝓔_res+𝓔_off`。前者按相同约分有理数
`n/d=f` 分组，再用 (JG10)，所以非负。不同符号的 `n` 不可能
在此碰撞。同号情形的四整数计数满足

\[
 \#\{n_i\asymp M,d_i\asymp D:n_1d_2=n_2d_1\}
                  \ll MD\log(2+\min(M,D)).
 \tag{JG12}
\]

证明：唯一写成 `n₁=at,n₂=bt,d₁=av,d₂=bv`，`(a,b)=1`。
记 `h=max(a,b)`。有效时 `a,b≈h` 且 `h≪min(M,D)`；这一层
至多 `O(h)` 对 `(a,b)`，每对的正整数 `t,v` 个数分别为
`O(M/h),O(D/h)`。这包括尺度比小于 1 时仍可能出现的整数 1：
有效支持使 `M/h,D/h` 有绝对正常数下界，故两个 `+1` 均可吸收。
对 h 求和得 (JG12)。删去 squarefree 或互素限制只增加此计数。

由于 `w≤1`，可得

\[
                  0\le\mathcal E_{\rm res}
                     \ll T^\varepsilon XM/D.
 \tag{JG13}
\]

完整密度还满足

\[
                  0\le\mathcal E_0
                     \ll T^\varepsilon (X+D^2)M/D.
 \tag{JG14}
\]

这里给出允许**索引相关振幅**的证明。对 (JG11) 每个 r，先按
约分频率 f 合并，并令 `z_{r,f}` 为对应系数及其 0、1、2 阶
导数的正主控和。不同频率间距至少 `cD^{-2}`。两次分部积分
给出的 pair 核至多
`C X z_{r,f}z_{r,g}(1+X|f−g|)^{-2}`，因为 χ 紧支撑而无边界项。
按频率排序，其 Schur 行和为 `O(X+D²)`。最后求 r 和时，
(JG9) 把 `Σ_r μ²(r)/φ(r)` 的交叉权重新合成 `w([ed₁,ed₂])≤1`；
(JG12) 因而给出
`Σ_r μ²(r)/φ(r) Σ_f z_{r,f}² ≪ T^ε M/D`。这证明 (JG14)，
不需要把依赖 `(d,n)` 的振幅先当作同一个固定函数。

**不能推断 `𝓔_res≤𝓔₀`。** 不同 f 在有限 u 区间并不正交。
例如同一 d、相邻 `n₁,n₂`，取 `b₁(u)=1`、
`b₂(u)=−e(Xu(n₁−n₂)/d)`，则完整密度为零，但 res 正且 off
恰为它的负值；当 `X/d≲1` 时这些振幅仍有统一导数界。
因此 (JG13) 只界住 res 这一项，不能把它称为已覆盖原 packet。

## 5. 已支付整个 κ 区块的物理成本

令 `ρ=HL P/S²`。对顶层双频率 box，`ρ≈1`；较低频率 box
满足 `ρ≲1`（对数 core 的额外成本并入 `T^ε`）。准确地有
`C=ρ D²/(MX)`。由 (JG3)，各 Gram 上界的标量成本分别为

\[
 \begin{array}{ll}
 C\sqrt{X\mathcal E_{\rm res}}
       \ll T^\varepsilon\rho D^{3/2}M^{-1/2},
       &\text{仅 res 部分的充分成本};\\
 C\sqrt{X\mathcal E_0}
       \ll T^\varepsilon\rho D^{3/2}
                    \sqrt{(X+D^2)/(XM)},
       &\text{完整密度};\\
 C\sqrt{X|\mathcal E_{\rm alias}|}
       \ll T^\varepsilon\rho D^2X^{-1/2}\sqrt{1+XM/D},
       &\text{别名误差}.
 \end{array}
 \tag{JG15}
\]

这里没有给 res 定义一个新的原始标量和；第一行只是把 (JG13)
放入一次 Cauchy 的成本比较。原标量可由后两行之和上界，或
先保持 `res+off+alias` 的 signed 和再估计。

在 `e=1,R=S=T³,HL≈T⁵` 的顶层双频率 box，令 `K=T^ν`，
`0≤ν≤3`。则 `X=T^{3−ν},M=T^{1+ν},C≈T²`：

| κ 区块指数 ν | res 部分成本 | 完整密度成本 | 别名成本 |
|---:|---:|---:|---:|
| 0 | `T⁴` | `T^{11/2}` | `T⁵` |
| 1 | `T^{7/2}` | `T^{11/2}` | `T^{11/2}` |
| 2 | `T³` | `T^{11/2}` | `T⁶` |
| 3 | `T^{5/2}` | `T^{11/2}` | `T^{13/2}` |

均允许 `T^ε`；整个原区块另有平凡上界 `T^{6+ε}`。所以 res
部分在 `ν≥2` 时满足 `T³` 的这一项预算，但 off 与 aliases 没有
因此解决。`ν=0` 表示有界 K；可取不含被删除整数端点的 `κ=2`
分片，或对 `κ=1` 另作 IC2 的 signed 端点处理。

与上一轮 IC7 在**相同完整 κ 区块**逐行使用的界比较，后者在
`ν<2` 的指数是
`6−min((3−ν)/5,(2−ν)/2,1/2)`。
(JG14)–(JG15) 给出
`min(6,max(11/2,5+ν/2))`，在 `1/2<ν<4/3` 有严格改善；
例如 `ν=1` 时从 `T^{28/5+ε}` 改为 `T^{11/2+ε}`。
这仍远大于目标 `T^{3+ε}`，不能被描述为改善了完整 BBLR 路线。

## 6. 文献覆盖与下一步不等式

| 输入 | 对当前联合对象的意义 | 尚不能给出的结论 |
|---|---|---|
| [BRZ Theorem 1.4](https://arxiv.org/html/2312.17435v2#S1.Thmtheorem1.4)，经 IC7 的互素转移 | 对真实固定 A 行有效；完整 κ 成本如上 | 行内 saving 不能再乘到联合 Gram 上 |
| [Matomäki–Teräväinen Theorem 1.5](https://arxiv.org/html/1911.09076v2#S1.Thmtheorem1.5) | 无额外掩码的线性相位短和在长度超过 `D^{3/5}` 时有对数节省 | 不是当前带 LCM 密度、乘积行和的固定幂联合估计 |
| [MSTT all-interval uniformity](https://arxiv.org/abs/2204.03754) | `D^{5/8+δ}` 以上的相关短和有任意对数幂节省 | 即使先解决具体算术掩码转移，对数也不能补当前固定幂差距 |
| JG4–JG15 的初等完成/LCM/Schur | 全部 κ 已重组；整数端点、别名及依索引振幅均计费 | 未覆盖完整物理目标，也不估计原 canonical zero Gram |

在平衡 `ν=0` 面，连续主核集中于
`|n₁/d₁−n₂/d₂|≲1/X`；固定其余坐标后，`d₂` 窗口长度约为
`D²/(XM)=T²=D^{2/3}`。这只说明上述短区间结果的**几何长度**
适合；LCM 密度和所有乘积权仍须保留，不能据此声称定理已可直接
应用。固定幂消去仍须来自带 `μ(d₁)μ(d₂)` 的联合近共振和，或
在 (JG3) 之前保留 `μ(A)` 的更有效 Type/dispersion。

本轮不把 `𝓔_off` 或 `𝓔_alias` 改名为已证明的 gate，也不声称
零 determinant、连续密度零模、原 Poisson 零模和 canonical Gram
相互等同。验证脚本只检查有限 LCM 平方和、单位别名、三因子
重组、精确碰撞计数与幂次账本；解析证明在上述正文中。
