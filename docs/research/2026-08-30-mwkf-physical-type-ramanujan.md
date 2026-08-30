# 物理 Type–Ramanujan 转移：保留整数端点，恢复缺失的 S 因子

白话结论：本节补出一个不隐藏互素条件、不额外插入 squarefree 掩码的
单侧 Type 转移。它保留原双 Möbius 权和 `a=hδ`，并可直接对耦合的
三变量平滑核做 Poisson，不需要先逐个 `h,δ` 取绝对值。

同时，这个物理推导暴露了此前模型接口的一个重要归一化错误：**未作
cofactor 密度平均的外层是 `HL`，不是 `HL/S`。** 因而
[RP 模型](2026-08-30-mwkf-reciprocal-physical-scales.md)和
[SS 模型](2026-08-30-mwkf-subcritical-shiu.md)中的局部恒等式与上界仍然
有效，但不能把它们的 `O(S log^{-L}T)` 当作字面物理量达到目标 `S`。
后者是模型的 `S` 倍。这不是原 signed 目标的反例，更不是完整
twisted-moment 证明；是必须修正的转移账本。

## 1. 从原核开始：单侧 Type 恒等式与整数 1 端点

对所有整数 `n,q≥1`，

\[
 \mu(n)1_{(n,q)=1}
 =1_{n=1}-\sum_{Ab=n}\mu(A)
                  \bigl(1-1_{b=1}1_{(A,q)=1}\bigr).
 \tag{PT1}
\]

证明：`Σ_{A|n}μ(A)=1_{n=1}`；扣除的唯一 `b=1` 项是
`μ(n)1_{(n,q)=1}`。这是有限恒等式，对非 squarefree 的 `n` 也成立。
例如 `n=4,q=3`，两个非零 allocation `(A,b)=(1,4),(2,2)` 的贡献
为 `−1,+1`。若为每个 Type 项重新插入 `μ²(Ab)`，会删除这个应当
相互抵消的展开，并破坏下面“无权 quotient”的用途。

固定 `ϑ∈C_c^∞((1/2,3/2))`，`ϑ(1)=1`。在正整数上可以**精确**用
`ϑ(b)` 替代 `1_{b=1}`，没有平滑逼近误差。设原 entry 为 `r=Ab`，
`r/R∈[1,2]`，`E=R/A`。对一个给定的紧支撑平滑耦合核 `G(x,v,y,z)`，
令

\[
 G_{A,q,E}(x,v,y,z)
  =G(x,v,y,z)\bigl(1-1_{(A,q)=1}\vartheta(Ex)\bigr).
 \tag{PT2}
\]

只需 `A≤2R`，因为 `b≥1`；于是 `E≥1/2`。当 `ϑ(Ex)` 的任意导数
非零且 `x∈[1,2]` 时，`E≤3/2`。因此 (PT2) 的所有归一化混合
seminorm 均由 `G,ϑ` 的对应 seminorm 统一控制，不损失 `R/A` 的幂。
这只处理整数 `b=1` 端点，**不**自动处理原 mollifier 截断处的其他
非平滑端点。

应用于 `(4.5)` 的任意有限核时，先保留
`(r,s)=1 ⇔ (A,s)=(b,s)=1`。`q` 的条件已经全部进入 (PT1)、外层
`(s,q)=1` 及 (PT2)，无需把 `(b,q)=1` 混入 Poisson 振幅。还必须保留
`r=1` 的独立项。将 `A` 分为 `A≤V` 和 `A>V` 给出短 allocation 和
长 allocation 两段；它们的和才是 (PT1)，不是两个各自为 Möbius 的
新系数。只分解这个 entry，另一侧 `μ(s)` 始终不动。

## 2. 同时变换 quotient、h、δ 的精确物理公式

取 `R,S,H,L>0`、整数 `q≥1`，先对一个实际给定的平滑核定义无量纲 master

\[
 \mathcal F_q[G]=
 \sum_{\substack{r,s\ge1\\(r,s)=1}}
 \mu(r)\mu(s)1_{(rs,q)=1}
 \sum_{h,\delta\in\mathbb Z}
 G\!\left({r\over R},{s\over S},{h\over H},{\delta\over L}\right)
 e\!\left(-{h\delta\bar r\over s}\right).
 \tag{PT3}
\]

`G` 在前两变量支持于 `[1,2]`，在后两变量紧支撑；若要与原非零
`h,δ` packet 一致，令相应支撑避开零即可。原始 `a=hδ` 在这里没有
作为任意独立序列替换。除原共同 gcd 的 `μ²(q)` 及外层尺度因子外，
这正是 `(4.5)` 经 `(5.13)–(5.15)` 归一化后的 smooth core 类型。
整个物理核未被断言已经化为一份无尾项的此类单核。

`r=1` 项记作 `B_q[G]`，按 (PT3) 字面设置 `r=1` 定义。对固定第二
变量 `v`，令 `\widehat G_{A,q,E}(ξ,v,η,ζ)` 为 `(x,y,z)` 三变量 Fourier
变换，约定每个变量都用 `e(−xξ)`。有限 complete identity 是

\[
 \sum_{\substack{b\bmod s\\(b,s)=1}}
 \sum_{u,v\bmod s}
 e_s\!\left(mb+ku+lv-uv\overline{Ab}\right)
 =s\,c_s(m+Akl),\qquad(A,s)=1.
 \tag{PT4}
\]

证明：对 `v` 求和强制 `u=lAb mod s`，所得因子是 `s`；剩下的
`b` 和为 Ramanujan 和。此式对复合 `s`、非单位 `hδ`、任意零频
都成立。无需逐 exact-gcd 层重复假设逆元存在。

把 (PT1) 插入 (PT3)，对 `b,h,δ` 作 residue-class Poisson，三次
Jacobian 是 `EHL/s³`；(PT4) 再给出一个 `s`。得到

\[
 \boxed{\begin{aligned}
 {\mathcal F_q[G]-B_q[G]\over R}
 ={}&-HL\sum_{A\le2R}{\mu(A)\over A}
 \sum_{\substack{s\ge1\\(s,Aq)=1}}{\mu(s)\over s^2}
 \sum_{m,k,l\in\mathbb Z}
 c_s(m+Akl)\\[-2pt]
 &\quad\times\widehat G_{A,q,E}
       \!\left({mR\over As},{s\over S},{kH\over s},{lL\over s}\right).
 \end{aligned}}
 \tag{PT5}
\]

`r,s,A` 和是有限的；`m,k,l` 和通常无限，因紧支撑平滑性绝对收敛。
这里没有把“精确 Poisson”写成“有限截断恒等式”。全部生成的零频
均保留；若另行删去 `m=0`，其显式 trace 必须同时登记。有限频率
cutoff `J` 的误差就是 (PT5) 中 cutoff 外的完整和，不能直接当成零；
将它界到物理目标还需真实核的统一 seminorm 及外层成本。

## 3. 未平均的 Ramanujan 展开没有额外 1/S

由于 `μ(s)` 限制 `s` squarefree，

\[
 {\mu(s)c_s(m+Akl)\over s^2}
 =\sum_{\substack{de=s\\d\mid m+Akl}}
       {\mu(d)\over d}{\mu^2(e)\over e^2}.
 \tag{PT6}
\]

`s` squarefree 保证 `(d,e)=1`；恢复所有 `s` 时须把它作为显式条件
保留。于是 (PT5) 等于

\[
 \boxed{\begin{aligned}
 -HL\sum_{A\le2R}{\mu(A)\over A}
 \sum_{\substack{e\ge1\\(e,Aq)=1}}{\mu^2(e)\over e^2}
 \sum_{\substack{d\ge1\\(d,Aeq)=1}}{\mu(d)\over d}
 \sum_{c,k,l\in\mathbb Z}
 \widehat G_{A,q,E}\!\left(
 { (dc-Akl)R\over Aed},{ed\over S},
 {kH\over ed},{lL\over ed}\right).
 \end{aligned}}
 \tag{PT7}
\]

这里仅作 `m=dc−Akl` 双射，无截断误差。它显示两个重要事实：

- 自然宽度仍是 `M_A=AS/R`；前一轮对此尺度的修正有效。
- 外层是 **`HL`**。还保留 `μ(d)/d·μ²(e)/e²` 的时候，不能再多乘
  `1/S`。在字面 MMKLS 写法中，这同样来自 `μ(s)/s` 乘双 Poisson
  的 `HL/s`，再使用 (PT6)。

原核 `(5.13b)` 是 dimensionless；其几何因子在 `(5.14a)` 已精确
化为 `(RS)^{-1}u^{-1/2}v^{-3/2}`，`(5.15)` 的外层因此是
`2T/(qRS)`。没有未登记的 `S^{-1}` 可再放进 (PT7)。

对照候选稿固定版本
[`7cc472d` 的 double-product Poisson 与 cofactor 展开](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/7cc472d45f934f7465a8543273a3bb866ef8da5a/docs/research/2026-08-25-mwkf-alternative-routes-spike.md#L20280)：
其 `(4.845dc_14xq_35p)`、`(35u)` 与 (PT5)–(PT7) 一致。额外 `1/S`
只在长 cofactor **密度主项** `(35v)` 中出现，因为该处把内层 `e`
和换成 `d/S` 乘密度。后来的短 cofactor `(29a1)` 保留完整 `e,d`
和，却使用 `HL/S`，不具备这个替换依据。

### 两个独立归一化见证

有限 residue 模型取 `s=S=3,q=1`，原 entry 只在 `r=2` 有权 1，
`h=δ=1`。直接值是

`μ(2)μ(3)e(−2/3)=−1/2+i√3/2`。

逐项 Type、quotient Fourier、双 Fourier、Ramanujan 除数展开均重构
此值；在完整除数展开前误加 `1/S` 则得到它的三分之一。该有限模型
验证代数归一化，不把 cyclic 零 residue 当成孤立连续 Poisson 零模。

连续 Fourier 的独立检查取 `s=S=5,A=2,m=3,H=2.1,L=1.7`，
`u(x)=v(x)=x exp(−πx²)`，故原 `h=0` 或 `δ=0` 项**严格为零**。
其 Fourier 变换是 `−iξ exp(−πξ²)`。字面 Kloosterman 和
`μ(s)/s·Σ_{h,δ}u(h/H)v(δ/L)S(A⁻¹m,−hδ;s)` 为
`0.06575795602712471`。用 `HL` 乘 (PT6) 重构到 `10^{-13}` 内；用
`HL/S` 恰少五倍。高斯尾以几何比值控制，所用 primal cutoff 20、
dual cutoff 40 的尾远小于此容差。这是回归见证，不是有限浮点测试
替代 (PT4)–(PT7) 的证明。

## 4. 真正的互素限制可以去除，但不能免费取得所缺 S

在 (PT7) 中令 `Q=Aeq`。它包含原共同 gcd `q`，不能只写 `Ae`。
对任意 `Q≥1`，Euler 因子或素数幂逐点计算给出

\[
 \mu(d)1_{(d,Q)=1}
 =\sum_{vn=d\atop p\mid v\Rightarrow p\mid Q}\mu(n).
 \tag{PT8}
\]

`v` 允许任意素数幂；只取 squarefree `v` 是错误的。例如 `d=8,Q=2`
需要 `v=4,8` 两项 `−1,+1` 抵消。置 `D=S/e`、`X=D/v`，则 (PT7)
中的平滑振幅具有

\[
 \Phi(x,y)=\widehat G_{A,q,E}
  \!\left({y\over x},x,{kH\over Sx},{lL\over Sx}\right),
 \qquad x={n\over X},\quad y={vnc-Akl\over M_A}.
 \tag{PT9}
\]

因此，在 `|k|H/S,|l|L/S` 仅为对数幂的 core 中，(PT2) 的统一
seminorm 给出 RP 所要求的 `Φ` seminorm；没有剩余的 `n` 互素掩码。
这是**原 smooth core 这组具体掩码**的转移，不是任意 masked MRSTT
定理。若曾先插入别的 squarefree 或 exact-gcd 掩码，必须回到
(PT3) 完整重组后才能使用此结论。

以下估计沿用 RP 的参数多面体，特别是 `1≤R≤S≤T³`、`S≥T^{1/2}`，
以及 dual core 的计数 `#(k,l)≪S²/(HL)·log^C T`。后者例如由
`1≤H,L≤S·log^C T` 及归一化频率为对数幂保证。
对于 `e≤T^{1/1000}`、`v≤D^{1/1000}`、`Q≤T^{C_*}`，RP 的三次
reciprocal-window 引理仍适用。其文献输入是
[MRSTT Theorem 1.1(i)](https://arxiv.org/html/2411.05770v2#S1.Thmtheorem1.1)，
它提供任意对数幂、几乎所有窗口的 Möbius–多项式消去；RP 已登记
连续滑窗、异常集合和 Taylor 误差。加入 `q` 只改变 smooth-divisor
支持，不改变该引理的相位或窗口裕量。

长 `v` 在有界支持模型中也有明确而有限强度的上界。对 `D,v>0`，

\[
 \sum_{D\le vn\le2D}{1\over vn}\le {2\over v};
 \quad v>2D\Longrightarrow\text{左边为零}.
 \tag{PT10}
\]

若 `D/v≥1`，有效整数个数至多 `D/v+1≤2D/v`；若 `D/v<1`，区间
只能含整数 1。这证明了所有端点，包括不能忽略的整数 `+1`。
`|vnc−Z|≤M` 对每个 `n` 至多有 `1+2M/D` 个 `c`。因此带模长至多
1 的权、允许删除零项时，长 `v` 的局部正上界为

\[
 {2\over e^2}\left(1+{2M\over D}\right)
 \sum_{v>D^{1/1000}\atop p\mid v\Rightarrow p\mid Q}{1\over v}.
 \tag{PT11}
\]

Rankin 取 `β=1/4` 给出该调和尾

\[
 \le D^{-1/4000}\prod_{p\mid Q}(1-p^{-3/4})^{-1}
 =D^{-1/4000}T^{o(1)}.
 \tag{PT12}
\]

统一性可初等验证：在 `p≤log T` 与 `p>log T` 分割，前段由整数
`Σ_{n≤log T}n^{-3/4}≪(log T)^{1/4}` 控制，后段用
`#\{p|Q:p>log T\}≤C_*log T/log log T`。故 Euler 积的对数为
`O_{C_*}((log T)^{1/4})=o(log T)`。

恢复 `A≤2R`、`|α(A)|≤τ_B(A)`、`M=M_A log^bT` 以及 dual 对数
core 后，`Σ_A τ_B(A)/A·(1+Ae/R)` 是 `O(log^C T(1+e))`，再对
`e≤T^{1/1000}` 乘 `e^{-2}` 求和只损失对数。`D≥T^{499/1000}`，
所以在**旧 `HL/S` 模型归一化**中得到 `O(S T^{-1/20000})`；在真实
(PT7) 中只能据此得到 **`O(S² T^{-1/20000})`**，并未达到 `S`。

## 5. 修正后的覆盖表与下一条真正不等式

定义 `U_model` 为 SS7/RP 的 `HL/S` 归一化和，并使用完全相同的
振幅、索引和删除规则。对它所代表的 (PT7) 子 packet，

\[
 \boxed{\mathcal M_{\rm phys}=S\,U_{\rm model}.}
 \tag{PT13}
\]

`M_phys` 是 `(F_q−B_q)/R` 中相应的那一项，总符号并入 `α`。
原物理 target 是 `O(S log^{-L}T)`，故相应充分目标应为
`U_model≪log^{-L}T`，而不是 `S log^{-L}T`。
若只求原任务的 `O_ε(T^{1+ε})` 上界，则允许物理 target 为
`O_ε(S T^ε)`，相应只需 `U_model≪_εT^ε`；现有带固定幂 `S` 的
模型上界同样不足以推出这个较弱目标。

| 对象 | 已证明的量级或恒等式 | 对物理目标的结论 |
|---|---|---|
| 单侧 Type 与具体互素层 | PT1–PT9，保留 `μ(A)μ(s)`、`a=hδ`、整数 1 端点 | smooth core 的算术转移成立；没有自动 norm saving |
| 短 cofactor、临界 smooth core | RP 模型 `S log^{-L}T` | 物理仅得 `S² log^{-L}T`，仍缺 `S` |
| 亚临界非零乘积有界支持 | SS8 模型 `S(log^{-K+C}T+T^{-1/5})` | 物理多乘 `S`；不能宣称目标覆盖 |
| 长 smooth cofactor 的初等尾 | PT11–PT12 | 物理 `S² T^{-1/20000}`；是有效尾界，不是所需尾界 |
| 长 cofactor 的密度主项 | 此处没有重新证明其带全部物理权的估计 | 其专属 `1/S` 不能复制到其余 packet |
| `r=1,m=0,c=0,k=0,l=0` 与 canonical Gram | 字面保留；不自动互相抵消 | 仍需全局 signed 配对与估计 |

现在应攻击的是 (PT7) 的**全体 signed outer 重组**或直接采用更强且
系数匹配的谱输入，以取得所缺的物理尺度消去。MRSTT 提供的任意
对数幂不能吸收固定幂 `S=T^u,u≥1/2`。此前 BBLR 等路线的独立
`T^{1/2}` 缺口没有被这个较弱模型取代；两种上界也不能未经新证明
相乘。原 mollifier 端点、频率尾、另一个 AFE 方向和 reflected 交叉
项继续保留在完整 signed-operator 账本中，未宣称 gate 完成。
