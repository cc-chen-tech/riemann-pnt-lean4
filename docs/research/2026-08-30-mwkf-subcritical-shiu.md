# 用 Shiu 除数上界闭合亚临界非零乘积模型

白话结论：上一检查点留下的整数“+1”边界，现在可以在已声明的有界
支持模型中处理掉。关键不是逐条估计 `c`，而是先把 `n,c` 重组成乘积
`t=nc≠0`。区间足够长时用已有的 Shiu 除数上界；区间短时，原物理
尺度已经留下固定幂次节省。两段覆盖全部亚临界箱，不再要求
`a>α+η`，而且允许保留任意有界算术掩码。

**证明边界。** 下文证明的是完整亚临界**非零 complementary-product
有界支持模型**，及已另行控制尾项的模型延伸。没有证明所有原始
(4.5)/Type packet 都满足这里的支持和权重总量条件；没有处理临界
packet 中任意算术掩码与 MRSTT 的兼容性；没有将 `c=0`、原 `m=0`、
AFE diagonal 和 canonical zero Gram 全部求值。因此完整 twisted
moment 仍未证明。与 [RP 检查点](2026-08-30-mwkf-reciprocal-physical-scales.md)
相比，新增的是一个实际可用的上界，不只是改写未证 gate。

**后续物理归一化修正。** [PT5–PT13](2026-08-30-mwkf-physical-type-ramanujan.md)
从原 master 核对出：未作密度平均的物理 cofactor 和外层是 `HL`，
不是下文 (SS7) 定义的 `HL/S`。因此该物理子 packet 是 `S·U_sub`。
(SS8) 作为所定义模型的定理保持有效，但对应物理界须再乘 `S`，
不能据此说整个亚临界物理区域达到 target。这里解除的只是该模型
的整数计数缺口，不是完整 physical gate 的相应区域。

## 1. 文献输入与有限重组

使用 P. Shiu 的 Brun–Titchmarsh 型上界，原文
[J. reine angew. Math. 313 (1980), 161–170](https://doi.org/10.1515/crll.1980.313.161)。
其假设和统一性在 Nair–Tenenbaum 的
[《Short sums of certain arithmetic functions》第 1 页](https://tenenb.perso.math.cnrs.fr/PPP/ShortSums.pdf)
中有精确陈述。取模数 1、函数 `τ` 后，对每个固定 `0<ε<1`、`x≥2`，

\[
 \sum_{x<v\le x+y}\tau(v)\ll_\varepsilon y\log(2x),
 \qquad x\ge y\ge x^\varepsilon.
\tag{SS1}
\]

`τ(p^j)=j+1≤2^j` 及 `τ(n)≪_b n^b` 满足该定理的增长假设。
这是一条**所有**此类区间的正上界，不是 almost-all 估计，不提供
Möbius 消去。以下只使用这个线性、模数 1 的版本，故没有变化模数或
多项式判别式的隐含常数。

固定 `D,r>0,M≥0,Z∈R`，令 `w(n,c)` 是任意有限复权。精确恒等式为

\[
 \begin{aligned}
 &\sum_{\substack{n\ge1,\ D\le rn\le2D\\
                  c\in\mathbb Z\setminus\{0\},\ |rnc-Z|\le M}}
                         {w(n,c)\over rn}\\
 &\qquad=\sum_{\substack{t\in\mathbb Z\setminus\{0\}\\|rt-Z|\le M}}
          \sum_{\substack{n\mid |t|\\D\le rn\le2D}}
                 {w(n,t/n)\over rn}.
 \end{aligned}
\tag{SS2}
\]

证明是双射 `(n,c)↔(t=nc,n)`；负 `t` 对应负 `c`，没有共轭、漏项或
多重计数。原 Möbius 权、gcd 条件和复相位在 `w` 及不受换序影响的
外层系数中原样保留；这里没有给物理 `c` 变量虚构一个 Möbius 权。
只有在这个等式之后，才对 `|w|≤1` 使用

\[
 \left|(\mathrm{SS2})\right|
 \le {1\over D}\sum_{\substack{t\ne0\\|rt-Z|\le M}}\tau(|t|).
\tag{SS3}
\]

所有区间端点均包含。若还要排除原 `m=rnc-Z=0`，只需在两边删去
`rt=Z`；正上界仍成立。`c=0` 却不能加入，因为不存在可用的 `τ(0)`。

## 2. 大宽度：Shiu 同时吸收离散边界

为避免与原高度变量混淆，下文 `t` 只指整数乘积。令 `T` 充分大，假设

\[
 T^{1/2}\le S\le T^3,\qquad
 1\le e\le T^{1/1000},\qquad D=S/e,\qquad
 1\le r\le D^{1/1000},\qquad |Z|+M\le T^{10}.
\tag{SS4}
\]

固定对数因子可以在固定幂上界 `T^10` 内吸收。若 `M≥T^(1/4)`，置
`Y=M/r`，则 `Y≥T^(247/1000)`，而 `|t|≤T^10`。

取 (SS1) 的固定 `ε=1/100`。若 `|Z|/r>4Y+4`，对正、负区间分别
反射到正轴，再将闭端点扩大到长度 `2Y+2` 的区间；其起点 `x` 满足
`x≥2Y+2`，且 `x^(1/100)≤T^(1/10)`。故 Shiu 有固定幂裕量
`247/1000-1/10=147/1000`。若 `|Z|/r≤4Y+4`，则整个区间位于
`|t|≤5Y+4`，直接使用 `Σ_{v≤V}τ(v)≪V log(2V)`。两种情况统一给出

\[
 \sum_{\substack{t\ne0\\|rt-Z|\le M}}\tau(|t|)
       \ll {M\over r}\log T,
 \qquad
 {1\over e^2}|(\mathrm{SS2})|
       \ll {M\over reS}\log T.
\tag{SS5}
\]

因此这里的整数端点确实被控制了；没有把 `+1` 错当作零，也没有
用 `T^ε` 去吸收只有对数宽度的亚临界间隔。

## 3. 小宽度：固定幂节省，不要求 Shiu

若 `M<T^(1/4)`，(SS3) 中至多有 `2M/r+1` 个整数。由
`|t|≤T^10` 和固定点态界 `τ(v)≪v^(1/1000)`，

\[
 {1\over e^2}|(\mathrm{SS2})|
 \ll {T^{1/100}\over eS}\left({M\over r}+1\right).
\tag{SS6}
\]

此处保留了真正的 `+1`。重要的归一化是 `e^(-2)/D=1/(eS)`，
所以外层 `e` 求和只产生调和和，不是 `T^(1/1000)` 个同样大的项。

## 4. 恢复原 outer 系数和双 Möbius 权

以下陈述沿用 (SS4) 的高度、cofactor 范围。固定 `0<R≤S`、`H,L>0`，
并取 `K≥0`；所有求和指标均取整数。每个整数 `A≥1` 的自然宽度
为 `M_A=AS/R`；允许有效支持宽度为 `M_A log^b T`，其中 `b` 固定。
令 `α(A)` 为原 signed Type-allocation 系数，并假设
`|α(A)|≤τ_B(A)`，`B` 是固定正整数。双 Fourier 索引的允许集合可以
依赖外层参数，但统一包含在一个大小至多
`P log^C T` 的集合中，`P=S²/(HL)`。另外对每个允许的
`(A,e,r,k,l)` 明确要求 `|Akl|+M_A log^b T≤T^10`；单有集合大小
不能推出这个高度限制。每个内权 `Ω` 满足：

- `D≤rn≤2D`，`c≠0`，`|rnc-Akl|≤M_A log^b T`；
- 模长至多 `log^C T`，可以带任意额外整数掩码及 `m=0` 删除；
- 有限分离或积分重组的总变差至多固定对数幂。

设 `|σ(A,e,r)|≤1`；它可包含 `r` 的 smooth-support 条件或其他
算术筛选。只取亚临界指标 `eM_A≤S log^(-K)T`。则完整有限 signed 和

\[
 \begin{aligned}
 \mathcal U_{\rm sub}:={HL\over S}
 \sum_{e\le T^{1/1000}}{\mu^2(e)\over e^2}
 \sum_{\substack{A\ge1\\A\le (R/e)\log^{-K}T}}
 {\alpha(A)\over A}
 \sum_{k,l}\sum_{r\le D^{1/1000}}\sigma(A,e,r)
 \sum_n{\mu(n)\over rn}\sum_{c\ne0}
       \Omega_{A,e,r,k,l}(n,c)
 \end{aligned}
\tag{SS7}
\]

对某个仅依赖上述固定指数的 `C₀` 满足

\[
 \boxed{|\mathcal U_{\rm sub}|
       \ll S\bigl(\log^{-K+C_0}T+T^{-1/5}\bigr).}
\tag{SS8}
\]

**证明：大宽度总账。** 将有效支持的 `log^b T` 付入对数损失。
(SS5) 与 `A^(-1)` 的组合为
`M_A/(A reS)=1/(reR)`。并且
`Σ_{A≤Y}τ_B(A)≪_B Y log^(B-1)(2Y)`；若 `Y<1`，该和为空。
因此恢复 `A≤(R/e)log^(-K)T` 后，给出 `log^(-K+C)T/e²`。
`Σ_r1/r≪log T` 对全部 `r≤T^(3/1000)` 都成立，根本不需要用
smooth-support 的点态计数。最后
`(HL/S)P=S`，`Σ_e e^(-2)≪1`，得到第一项。

**证明：小宽度总账。** 此时有效 `M≤T^(1/4)`，(SS6) 给出
`T^(1/100)/(eS)` 乘 `M/r+1`。用
`Σ_A τ_B(A)/A≪log^B(2T)`、`Σ_e1/e≪log T`、
`Σ_r1/r≪log T` 和字面计数 `#r≤T^(3/1000)`，再恢复
`(HL/S)P=S`，总量至多

\[
 T^{1/100}\bigl(T^{1/4}+T^{3/1000}\bigr)\log^C T
 \ll T^{13/50}\log^C T
 \ll S T^{-1/5}.
\]

最后一步使用 `S≥T^(1/2)`，还有固定 `1/25` 的幂裕量吸收对数。
这次甚至不需要上一版的 `B_*=T^o(1)` Rankin 估计。所有 Möbius 权
先在 (SS2)/(SS7) 中保留；(SS8) 使用的是充分强的正上界，没有额外
假设它们发生随机消去。取 `K` 大于 `C₀` 和目标对数幂，即得所需
`O_L(S log^(-L)T)`。

## 5. 覆盖更新及不能据此推出的结论

| 范围/对象 | 输入与结果 | 状态 |
|---|---|---|
| 亚临界、有效 `M≥T^(1/4)` | 乘积重组＋Shiu，(SS5)/(SS8) | 模型界全覆盖；物理界按 PT13 多乘 `S` |
| 亚临界、有效 `M<T^(1/4)` | 点态除数界＋物理尺度，`S T^(-1/5)` | 模型界全覆盖；不是物理 target 覆盖 |
| 旧残余 `u=α=3/5,a=1/5` 的亚临界对数邻域 | 属于第一行 | 旧整数边界缺口已解除 |
| 临界 `eM_A>S log^(-K)T` | (RP3)–(RP8) 的 MRSTT 平滑模型引理 | 任意算术掩码转移仍未完成 |
| `c=0` 与原 `m=0`/AFE/canonical Gram 关系 | (RP4)/(RP4a) 只给出确切表达式 | 完整求值及全局配对尚未完成 |

**变化在哪里。** (RP9) 的逐 `c` 有限上界仍然正确，但它不足以证明
全覆盖这一事实已被更强的 (SS3)–(SS8) 解决。因此不应继续将
`u=α=3/5,a=1/5` 称作这个有界支持模型的未证 gate。相反，也不能把
此处对任意有界掩码成立的**亚临界正上界**移植成临界 MRSTT 的任意
掩码消去：两者使用完全不同的定理。

下一步应把临界 packet 的算术层、未受控截断以及所有零项接回
[原 signed operator](2026-08-30-mwkf-physical-reflection-adapter.md)。
在这一物理等式和余项账本被证明以前，本节不宣布完整 coupled-kernel
gate、不宣布 twisted moment 渐近式，也不撤销稠密共同频率补集的
真实双 Möbius 范数问题。
