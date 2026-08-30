# 全 c 逆 Poisson：有限正指标、端点重组与带互素的线性 Möbius 行

白话结论：真实紧支撑核允许把全部 `c` 频率精确变回有限个正指标。
保留全部 Type 与 cofactor 符号后，可以算清其消去，但结果恰好回到
原来的双 Poisson 和，**不是额外的幂次节省**。另一方面，已发表的
线性 Möbius 指数和估计可以无固定幂损失地带上这里的互素限制；
下面给出完整推导和真实外层成本。在平衡非零行上省 `T^{1/2}`，
逐行求和后仍不能达到物理目标，不能与 BBLR 的半次幂缺口相乘。

本节接续 [PT1–PT13](2026-08-30-mwkf-physical-type-ramanujan.md)。
`G` 是其中的实际给定 `C_c^∞` 耦合核，entry 与 modulus 变量支持
于 `[1,2]`。不把完整 AFE/reflection 的所有非平滑端点或尾项自动
视为这个单一 smooth core；其 [PA 账本](2026-08-30-mwkf-physical-reflection-adapter.md)
不变。

## 1. 实际核的第二次 Poisson 只有有限个正指标

定义只对原 `h,δ` 坐标变换的核

\[
 \widetilde G(x,v,\eta,\zeta)
 =\int_{\mathbb R^2}G(x,v,y,z)e(-y\eta-z\zeta)\,dy\,dz.
\]

`\widetilde G_A` 表示对 (PT2) 同样变换，保留 `q,E` 的依赖。
置 `E=R/A`。Poisson 与 Fourier 二次变换给出

\[
 \begin{aligned}
 &\sum_{c\in\mathbb Z}\widehat G_A
       \left({(dc-Akl)E\over ed},v,\eta,\zeta\right)\\
 &\quad={e\over E}\sum_{j\in\mathbb Z}
       \widetilde G_A(-je/E,v,\eta,\zeta)e(-jAkl/d)\\
 &\quad={Ae\over R}\sum_{\substack{\kappa\ge1\\
                    R/(Ae)\le\kappa\le2R/(Ae)}}
       \widetilde G_A(\kappa Ae/R,v,\eta,\zeta)e(\kappa Akl/d).
 \tag{IC1}
 \end{aligned}
\]

证明：对函数 `c↦hat f((E/e)(c−Akl/d))` 取 Fourier，Jacobian 是
`e/E`，平移给出负号相位，二次 Fourier 给出 `f(−je/E)`。
entry 支撑使 `j≥0` 全部为零，令 `κ=−j` 即得最后一行。因此
`κ` 和**精确有限**，没有 κ 截断误差。端点包括在索引中；平滑
紧支撑核在边界的取值自然为零，不靠删除整数端点获得恒等式。

在采样位置，(PT2) 的 `ϑ(Ex)` 变成 `ϑ(κe)`，正整数性说明它
恰为 `1_{κ=e=1}`。把 (IC1) 代入 (PT7)，得到

\[
 \boxed{\begin{aligned}
 {\mathcal F_q[G]-B_q[G]\over R}
 ={}&-{HL\over R}\sum_{A\le2R}\mu(A)
 \sum_{\substack{e\ge1\\(e,Aq)=1}}{\mu^2(e)\over e}
 \sum_{\substack{d\ge1\\(d,Aeq)=1}}{\mu(d)\over d}\\
 &\times\sum_{\kappa\ge1}\sum_{k,l\in\mathbb Z}
 \widetilde G\left({\kappa Ae\over R},{ed\over S},
                        {kH\over ed},{lL\over ed}\right)
 \bigl(1-1_{\kappa=e=1}1_{(A,q)=1}\bigr)e(\kappa Akl/d).
 \end{aligned}}
 \tag{IC2}
\]

`A,e,d,κ` 因支撑均有限；`k,l` 一般无限而绝对收敛。对给定有限
外参数，Poisson 前后的无限和均由 Schwartz 衰减控制，重排合法。
这里的 `HL/R` 来自 (PT7) 的 `HL` 乘 `Ae/R`，并非重新恢复一个
额外 `1/S`。

### 不能混同的零项与 cutoff

`j=0` 为零只是**此轮逆 c Poisson**的支撑事实，不是 canonical
zero Gram 为零，也不意味着原 `m=0`、`c=0`、`k=0` 或 `l=0`
消失。例如删除 `c=0` 时，必须从 (IC1) 右侧减去

\[
 \widehat G_A(-klR/(ed),v,\eta,\zeta).
 \tag{IC3}
\]

原 `m=0` 则是 `dc=Akl` 的独立 trace，不能与 (IC3) 互换。
若保留原频率 cutoff `χ(m)`，全式与截断式的差就是 (PT7) 内
带因子 `1−χ(dc−Akl)` 的完整和。对频率乘 cutoff 后，entry
反变换通常不再紧支撑，故不得直接套用“κ 精确有限”。必须先
恢复全部 dyadic 分片与这个差项，或另证其物理尺度上界。
生成的双频率轴 `kl=0` 同样保留；原 `hδ≠0` 不会自动删除它们。

## 2. 全部 signed allocation 的有限消去与往返恒等式

对任意 `r≥1`、squarefree `s≥1`，有有限恒等式

\[
 J(r,s):=\sum_{e\mid(r,s)}\mu(e)
                 \sum_{\substack{A\mid r/e\\(A,s)=1}}\mu(A)
       =1_{r=1}.
 \tag{IC4}
\]

证明：若 `r` 有一个不整除 `s` 的素因子，它也不整除任何
`e|(r,s)`，故每个内层除数和均为零。若 `r` 的所有素因子都
整除 `s`，则内层只能有 `A=1`，外层为 `Σ_{e|(r,s)}μ(e)`，
仅当 `r=1` 非零。这不要求 `r` squarefree。

在 (IC2) 置 `r=κAe,s=ed`。`s` squarefree 且 `(s,q)=1`，
权重满足 `μ²(e)μ(d)/(ed)=μ(s)μ(e)/s`，余下限制恰为
`e|(r,s)` 与 `(A,s)=1`。`κ=e=1` 的端点要求 `A=r`，
所以固定 `(r,s)` 的完整系数是

\[
 -{\mu(s)\over s}
       \bigl(1_{r=1}-\mu(r)1_{(r,sq)=1}\bigr).
 \tag{IC5}
\]

恢复独立的 `B_q[G]/R` 后，恰好得到原 (PT3) 的双 `h,δ` Poisson：

\[
 {\mathcal F_q[G]\over R}
 ={HL\over R}\sum_{\substack{r,s\ge1\\(r,s)=1}}
 {\mu(r)\mu(s)1_{(rs,q)=1}\over s}
 \sum_{k,l\in\mathbb Z}
 \widetilde G(r/R,s/S,kH/s,lL/s)e(rkl/s).
 \tag{IC6}
\]

这精确说明了全局重组的作用，也说明**整轮 Type/Poisson 再反变换
本身没有产生新估计**。特别是仅取一段 `A`、`e` 或 `κ` 后，(IC4)
不成立。例如 `r=2,s=6` 的两个非零 `(e,A,κ,weight)` 分别为
`(1,1,2,+1)` 与 `(2,1,1,−1)`；只留 `κ>1` 得到 1，而完整 bulk
为零。此前临界条件 `A≥(R/e)log^{-K}T` 在这里对应
`κ≤(r/R)log^K T`，并非可以不计补集的精确局部消去。

## 3. 带任意多项式大小互素参数的线性 Möbius 引理

**命题。** 固定 `C,ε>0`。设 `X≥4`、整数 `1≤Q≤X^C`，
`1≤Z≤X/2`，`α=±Z/X`。若复权 `w` 支撑于 `[1,2]`，并且
`||w||∞+Var(w)≤1`，则无条件有

\[
 \boxed{\left|\sum_{n\ge1}\mu(n)1_{(n,Q)=1}
                 w(n/X)e(\alpha n)\right|
 \ll_{C,\varepsilon}X^{1+\varepsilon}
       \left(X^{-1/5}+(Z/X)^{1/2}+Z^{-1/2}\right).}
 \tag{IC7}
\]

这不是对任意 Möbius 两点相关的声明。其唯一非初等输入是
Basak–Robles–Zaharescu 的
[Theorem 1.4，固定 arXiv v2](https://arxiv.org/html/2312.17435v2)：
若 `y≥2,(a,b)=1, |β−a/b|≤b^{-2}`，则

\[
 \sum_{n\le y}\mu(n)e(\beta n)
 \ll_\eta y^{4/5+\eta}
        +y b^{-1/2}\log^3 y+(yb)^{1/2}\log^3 y.
 \tag{IC8}
\]

这是该文给出的线性指数和结果；下面的互素转移和物理应用是本节
的推导，不声称该论文已经估计了当前 coupled kernel。

**证明：精确去掩码。** (PT8) 给出

\[
 \sum_n\mu(n)1_{(n,Q)=1}w(n/X)e(\alpha n)
 =\sum_{\substack{t\le2X\\p\mid t\Rightarrow p\mid Q}}
       \sum_u\mu(u)w(tu/X)e(\alpha tu).
 \tag{IC9}
\]

允许 `t` 的所有素数幂；右侧字面有限。置 `U=X/(2Z)≥1`。
对 `t≤U`，令 `y=X/t`、`L_t=y/Z≥2`，取 `b_t` 为最近整数
（半整数时取上方），`a=sign(α)`。于是 `b_t≈y/Z` 且

\[
 |\alpha t-a/b_t|
 ={ |b_t-L_t|\over L_tb_t}\le b_t^{-2}.
 \tag{IC10}
\]

最后一步用 `|b_t−L_t|≤1/2`、`b_t≤L_t+1/2≤2L_t`。
`a=±1` 自动与 `b_t` 互素。对所有前缀 `2≤v≤2y` 使用同一个
`b_t`，(IC8) 右侧在 `v` 上单调，用 `2y` 控制即可；`v<2` 的
至多一项由常数控制。因此 Abel 求和对任意上述 BV 权均给出

\[
 \left|\sum_u\mu(u)w(tu/X)e(\alpha tu)\right|
 \ll_\eta (X/t)^{4/5+\eta}
    +\sqrt{XZ}\,t^{-1/2}\log^3(2X)
    +XZ^{-1/2}t^{-1}\log^3(2X).
 \tag{IC11}
\]

**保留实际 smooth-divisor 权，不取它们的最大值。** 定义

\[
 E_Q:=\prod_{p\mid Q}(1-p^{-1/2})^{-1}
     =\sum_{p\mid t\Rightarrow p\mid Q}t^{-1/2}.
 \tag{IC12}
\]

(IC11) 三项的 `t` 权都至多 `t^{-1/2}`，所以短 `t` 段至多为
`E_Q` 乘去掉 `t` 的三项。长 `t>U` 段不需要振荡：对所有
`t≤2X`，有效正整数个数至多 `2X/t`。此结论在 `t>X` 时仍成立，
因为只能出现整数 1；`t>2X` 时为空。因此长段至多

\[
 2X\sum_{t>U\atop p\mid t\Rightarrow p\mid Q}{1\over t}
 \le 2XU^{-1/2}E_Q=2\sqrt{2XZ}\,E_Q.
 \tag{IC13}
\]

没有丢掉整数 `+1`。最后，`Q≤X^C` 一致地给出
`log E_Q=O_C(√log(2X))`：在 `p≤log X` 与其补集分割，前段用
`Σ_{n≤log X}n^{-1/2}≪√log X`，后段用素因子个数
`≤C log X/log log X`，并用 `p^{-1/2}≤(log X)^{-1/2}`。
有界小 `X` 并入常数。故 `E_Q=X^{o_C(1)}`；分配 `η` 与 Euler
积及对数损失到 `ε` 即得 (IC7)。证毕。

## 4. 在实际行上的覆盖与不得重复使用的消去

固定 (IC2) 的 `e,κ,d,k,l`，`kl≠0`。令

\[
 X={R\over e\kappa},\qquad
 \alpha={\kappa kl\over d},\qquad
 Z=|\alpha|X={R|kl|\over ed}.
 \tag{IC14}
\]

对 `A` 的振幅是 `\widetilde G(A/X,ed/S,kH/(ed),lL/(ed))`，
归一化 BV 由原核控制；额外 dyadic cutoff 的 BV 成本必须计入。
bulk 的互素条件是 `(A,ed)=1`，用 (IC7) 的 `Q=ed`。
`κ=e=1` 的端点是 `Q=d` 与 `Q=dq` 两个受限和之差。
只有核的该 seminorm 已控制、`Q≤X^C` 且 `1≤Z≤X/2` 的行
才属于本命题；实际 `Q≤T^{C_*}` 且 `X≥T^{δ_*}` 可满足前一条件。
`kl=0` 或 `Z>X/2` 不在此非零小线性频率覆盖内。

若 `X=T^x,Z=T^z`，`0<z<x`，(IC7) 的行内 saving 指数为

\[
 \sigma(x,z)=\min\{x/5,(x-z)/2,z/2\}.
 \tag{IC15}
\]

| 行参数 | 受限 Möbius 行上界 | 覆盖性质 |
|---|---|---|
| `x=3,z=1` | `T^{5/2+ε}` | 平衡非零行，省 `T^{1/2}` |
| `x=3,z=3/2` | `T^{12/5+ε}` | 此引理最大行内 saving 为 `T^{3/5}` |
| `x=3,z=5/2` | `T^{11/4+ε}` | 接近大频率边界，saving 降为 `T^{1/4}` |
| `Z≈1` 或 `kl=0` | 前者无固定幂 saving；后者不适用 | 零/奇异部分不被删除 |

一个确实未被端点删除的平衡 packet 取 `q=1,e=1,κ=2`，
`R=S=T³`、`HL≈T⁵`、`|k|≈S/H, |l|≈S/L`。此时
`A≈R/2`，`Z≈T`，(IC7) 可用。不能取 `q=1,e=κ=1` 当作
非零见证，因为其端点 multiplier 恒为零。

即使对上面 `κ=2` packet 的每一行都取得 `T^{1/2}` saving，
再对 `d,k,l` 取绝对值，其成本仍为

\[
 {HL\over R}\cdot {S^2\over HL}
       \cdot\sum_{d\asymp S}{1\over d}\cdot R T^{-1/2+\varepsilon}
 \ll T^{11/2+\varepsilon}.
 \tag{IC16}
\]

这是 `(F−B)/R` 中上述 `e=1,κ=2` 子 packet 的逐行绝对上界，
不是完整物理量的上界。与物理目标 `S T^ε=T^{3+ε}` 比较，
仍差 `T^{5/2}`。因此这里的行定理不改善此前 BBLR 路线的最终
半次幂缺口；两者使用的消去不能未经新联合证明而相乘。

## 5. 验证及下一条真实义务

新增有限检查覆盖 (IC1) 的相位/Jacobian、(IC4)–(IC5) 的所有
allocation、互素与非 squarefree 端点以及 (IC15)–(IC16) 的幂次
账本。连续 (IC1) 用支撑 `[1,2]` 的四个均匀分布卷积作独立
见证，其 Fourier 变换是 `e(−3ξ/2)sinc(ξ/4)^4`；截断 Fourier
尾由显式 `O(C_cut^{-3})` 控制。它只检验变换符号和尺度，
不是用浮点计算证明 (IC7) 或 gate。

下一步仍须在 (IC2) 或等价的 (IC6) 上保留不同 `d,k,l` 行的
符号作一次联合 dispersion；若使用 `TT*`，必须与现有 canonical
zero Gram、非零频补集和两个 mixed 项使用同一个物理归一化。
本节没有估计那个联合范数、完整频率尾或新的次主项；完整
twisted moment 与 coupled-kernel gate 均未证明。

后续 [JG1–JG15](2026-08-30-mwkf-joint-unit-density-gram.md) 已对完整
`κ` 区块实行一次联合 Gram，给出 LCM 单位密度平方和、共振及别名
上界。在部分中间 `κ` 区块优于这里的逐行界，但仍不足物理目标。
