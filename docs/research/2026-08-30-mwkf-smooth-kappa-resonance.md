# 先求完整光滑 κ 和：非共振覆盖与双 Möbius 整数带

白话结论：上一轮把 `κkl` 当作一般乘积系数作 Gram，漏用了一个
可用但并非免费的结构——实际 IC2 的 κ 没有 Möbius 权，且核在 κ
方向光滑。先对它求和，可把一整片非共振区域压到快速衰减；在
剩余区域，保留 `Akl≈jd` 的整数带，比逐项估计 κ 更强。平衡顶层
`K≈T`、固定 `e=1` 区块的界由 JG 的 `T^{11/2+ε}` 改为
`T^{5+ε}`。**仍不是目标 `T^{3+ε}`，也未改善完整 BBLR 路线的
最终缺口。**

这是实际平滑核的局部估计，不是对 JG 中任意有界
`W_{κ,k,l}` 的估计。没有把新 saving 乘到 IC/JG/BBLR 上，也没有
删去 canonical zero Gram、两个 reflection mixed 项或频率轴。

## 1. 实际无符号 κ 与准确尺度

从 [IC2](2026-08-30-mwkf-inverse-c-signed-roundtrip.md) 出发，固定
squarefree `e` 和原 gcd `q`，令

\[
 X={R\over eK},\quad D={S\over e},\quad P=K_1K_2,
 \quad C={HL\over Re},\quad \rho={HLP\over S^2},
 \quad Z={KXP\over D}={RP\over S},\quad Y={XP\over D}={Z\over K}.
 \tag{SK1}
\]

本节 `X,D,K,K₁,K₂≥1`；全部尺度以及所需平滑 seminorm 为 `T`
的固定幂及 `T^ε`。固定符号箱 `A∈[X,2X]`、`d∈[D,2D]`、
`|k|∈[K₁,2K₁]`、`|l|∈[K₂,2K₂]`；端点可包含。取固定
`w∈C_c^∞((1/2,3))` 作 κ 分片，定义

\[
 V_{A,d,k,l}(t)=w(t)\widetilde G\left({tKAe\over R},
             {ed\over S},{kH\over ed},{lL\over ed}\right).
 \tag{SK2}
\]

其他分片权可留在 V 内，但必须验证 t 导数；不允许乘任意
κ 相关算术权。链式法则中 `KAe/R=A/X∈[1,2]`，所以每个固定
阶 t 导数有统一界。实际 `h,δ` 仍在 `G` 的双 Fourier 变换内，
未替换成任意 `kl` 系数。原单位掩码始终为

\[
             (e,Aq)=1,\qquad(d,Aeq)=1.                 \tag{SK3}
\]

先研究包含所有正 κ 的 completed bulk

\[
 \mathcal B_{e,K}=-\mu^2(e)C\sum_{A,d,k,l}
       {\mu(A)\mu(d)\over d}
       \sum_{\kappa\in\mathbb Z}V_{A,d,k,l}(\kappa/K)
                              e(\kappa Akl/d),          \tag{SK4}
\]

支撑使 κ≤0 为零。IC2 的实际分片等于 (SK4) 加上

\[
 1_{e=1}C\sum_{A,d,k,l}{\mu(A)\mu(d)\over d}
 1_{(A,q)=1}V_{A,d,k,l}(1/K)e(Akl/d),                   \tag{SK5}
\]

仍带 (SK3)。故 `e=1` 且分片遇到 κ=1 时，不能删一个整数后
直接套光滑 Poisson。对 `K>2`，这里的固定支撑使 (SK5) 为零；
有界 K 的端点保留原 IC 账本。本节的改善区间和快速衰减区间
均有 K 为正幂，因而无此问题。

## 2. 完整 κ-Poisson；没有提前 Cauchy

Fourier 约定 `hat V(ξ)=∫V(t)e(−tξ)dt`。精确地

\[
 \sum_\kappa V(\kappa/K)e(\kappa Akl/d)
       =K\sum_{j\in\mathbb Z}\widehat V\left(K(j-Akl/d)\right).
 \tag{SK6}
\]

左边有限，右边绝对收敛。`K` 是真实 Jacobian。对每个固定 B，
紧支撑与分部积分给出

\[
 |\widehat V(\xi)|\ll_B T^\varepsilon(1+|\xi|)^{-B}.   \tag{SK7}
\]

没有端点积分项。至此两边 Möbius、所有 `k,l`、单位掩码和复核
都保持 signed；没有 Cauchy，也没有 κ 外层绝对值。

### j=0 与真正的非共振区

由于 `|Akl/d|≈Y`，j=0 给出的整个物理分片满足

\[
       |\mathcal B^{(0)}_{e,K}|
       \ll_B T^\varepsilon\rho D^2(1+Z)^{-B}.          \tag{SK8}
\]

若 `8Y≤1/2`（上述支持的一个充分常数条件），则对 j≠0，
`|j−Akl/d|≥|j|/2`。因此

\[
 |\mathcal B_{e,K}|
 \ll_B T^\varepsilon\rho D^2\{(1+Z)^{-B}+K^{-B}\}.
 \tag{SK9}
\]

例如 `Z≥T^η`、`K≥16Z` 时，对任意固定 L，选足够大的 B 可得
`O(T^{-L})`，包括多项式数量的其他外层。常数依赖 η、L 和真实
核的相应有限阶 seminorm。单凭 `Y<1` 或 `Z≈1` 不能断言快速
衰减；不能把仅对数间隔说成任意 T 幂节省。

平衡 `R=S=T³,HL≈T⁵,P≈T` 时，Z≈T。故固定 `ν>1` 的
`K=T^ν` 顶层非零频率分片快速衰减。这优于 JG 在这些分片的
通用 Gram 界。较低 P 有不同 Z，必须使用 (SK8)–(SK9) 重新核算；
`kl=0` 不适用，不能由这里的 j=0 衰减删除原频率轴。

## 3. 非零 j 的完整整数带；保留离散 +1

令 `Q=XP`、`Δ=D/K`。在 (SK6) 中记

\[
                  n=Akl,\qquad r=jd-n.
 \tag{SK10}
\]

这里 r 是新整数残差，不是原 entry；j 也不是 canonical zero
Gram 的标签。暂取有限窗口 `|r|≤W`，j≠0。每个 n 的表示
`Akl=n` 至多为常数乘 `τ₃(|n|)`。固定 n,r 后，j,d 的所有解
由正除数 `d\mid|n+r|` 给出，j=(n+r)/d；**必须排除 n+r=0**。
所以有完全有限、无近似的计数式

\[
 \sum_{A,k,l}\sum_{\substack{d\in[D,2D],\ j\ne0\\|jd-Akl|\le W}}1
 =\sum_{A,k,l}\sum_{\substack{r\in\mathbb Z,\ |r|\le W\\Akl+r\ne0}}
             \sum_{\substack{d\mid|Akl+r|\\D\le d\le2D}}1.
 \tag{SK11}
\]

原单位条件和任意复权可逐项拉回，式子仍精确；仅为上界才移除
它们。闭端点含在内，整数 r 数量为 `2 floor W+1`。由初等
`τ_j(m)≪_ε m^ε`，对 W=2^bΔ（b≥0）得

\[
       \#\ \ll_\varepsilon T^\varepsilon Q
                      (1+2^b\Delta)(1+2^b)^\varepsilon.
 \tag{SK12}
\]

这里可在证明中先取更小 ε，以吸收 Q、Δ 的固定多项式大小。
即使 b 无界也有效，不是假设所有 j 在一个未证明的硬 cutoff
之内。j≠0 确保从不对零使用除数界。

`d≤2D` 使 (SK7) 的衰减至少为 `(1+|r|/(2Δ))^{-B}`。
用 (SK12) 对 `|r|≤Δ` 及所有二进环带求和，B>2+ε 足够，得到

\[
 \begin{aligned}
 |\mathcal B^{(\ne0)}_{e,K}|
 &\ll T^\varepsilon {CK\over D}XP(1+D/K)\\
 &=T^\varepsilon\rho(D^2/K+D).
 \end{aligned}                                                   \tag{SK13}
\]

这是整个 κ 分片的正确物理成本，未使用旧 RP/SS 模型的额外
`1/S`。第二项 `ρD` 就是整数 +1 成本；`Δ<1` 时仍可能有精确
整数共振，不能删除。若仅保留 `|r|≤Δ L₀`，`L₀≥1`，同一证明
给出物理尾

\[
 \ll T^\varepsilon\rho(D^2/K+D)L_0^{1+\varepsilon-B}. \tag{SK14}
\]

多项式 L₀ 可给任意固定幂尾；polylog L₀ 只保证相应对数幂尾。
这也给出直接形式化的有限主和加显式截断误差。

若在原互素支持上 `d>|kl|`，则 `jd=Akl` 不可能：由 (A,d)=1
可得 `d|kl`。因此 `D>4P` 时这组整数带没有 r=0 项。**这不意味着
j=0、原 AFE diagonal 或 canonical zero Gram 消失。**

## 4. 外层 e 成本与参数覆盖

对全部 `e∈[E,2E]`，只取绝对值相加，不假设 cofactor 间消去：

\[
 \sum_{e\asymp E}|\mathcal B^{(\ne0)}_{e,K}|
       \ll T^\varepsilon\rho\{S^2/(EK)+S\}.          \tag{SK15}
\]

e 的整数边界只改变常数，需 `X≥1,D≥1` 的实际支持。第一项
相对于目标 S 的比为 `ρ S/(EK)`。写
`R=T^r,S=T^s,E=T^η,K=T^ν,ρ=T^ω`，则非零 j 的完整 e-shell
成本指数为

\[
             \omega+\max(2s-\eta-\nu,s).             \tag{SK16}
\]

在 `ρ≤T^ε` 下，`η+ν≥s+ω` 是这个正上界达到目标的充分条件；
还须把 (SK8) 和 (SK5) 算上。`X≥1` 强制 `η+ν≤r`；例如
ρ≈1、R<S 时这个充分条件没有内点，不能把固定 e 的改善冒充
全参数覆盖。

对平衡顶层 e=1，`0<ν≤1` 给出 `T^{6−ν+ε}`；j=0 快速衰减。
与已有 IC/JG 取较好者（不相乘）：

| ν 范围 | 当前可用的该平滑区块界 | 来源与限制 |
|---|---|---|
| `0<ν≤1/2` | `T^{11/2+ε}` | JG；IC 的较好界不会被撤回 |
| `1/2<ν≤1` | `T^{6−ν+ε}` | SK13 的完整 κ 消去，ν=1 为 T⁵ |
| 固定 `ν>1` | 任意负幂 | SK9；仅 Z≈T 顶层，保留全光滑 κ |
| K 有界、κ=1 端点 | 单列 IC2 原账本 | SK5 未被平滑 Poisson 自动处理 |

因此真正需要新的双 Möbius 估计的顶层区域收缩到
`K≲T^{1+o(1)}`，而不是 JG 表里整个 `K≤T³`。这个结论只是
当前实际 IC2 平滑分片的覆盖，不是全局剩余算子的覆盖声明。

## 5. 保留窄带上的双 Möbius Type I/II

在 (SK14) 的有限窗口内，未取模的主和为

\[
 -\mu^2(e)CK\sum_{A,d,k,l,j\ne0}
 {\mu(A)\mu(d)\over d}\,1_{\text{(SK3)}}
 1_{|jd-Akl|\le\Delta L_0}
 \widehat V_{A,d,k,l}\bigl(K(j-Akl/d)\bigr).            \tag{SK17}
\]

可以对有限 signed 和整体作算子/dispersion；不能逐条仿射线先
估计。若再次 Type 分解，必须只分解两个真实系数 µ(A)、µ(d)，
其余核与约束不动。对整数 U,V≥1，置
`c_U(a)=Σ_{b|a,b≤U}μ(b)`，定义

\[
 \begin{aligned}
 s_U(n)&=\mu(n)1_{n\le U},\\
 I_{U,V}(n)&=-\sum_{\substack{ab=n\\a>U,b\le V}}c_U(a)\mu(b),\\
 II_{U,V}(n)&=-\sum_{\substack{ab=n\\a>U,b>V}}c_U(a)\mu(b),\\
 \mu(n)&=s_U(n)+I_{U,V}(n)+II_{U,V}(n).                \tag{SK18}
 \end{aligned}
\]

证明：`c_U=1*μ_{≤U}`，故 `c_U*μ=μ_{≤U}`；a≤U 部分只有
a=1 非零，等于 µ(n)。拆余下 b 区间即得式子。两个父变量可用
独立的 U,V，产生全部九个有序 sector，所有小端点都保留。

例如 A=a₁b₁,d=a₂b₂ 的 I/II 项仍带

\[
      j a_2b_2-a_1b_1kl=r,\quad
      (a_1b_1,ea_2b_2)=1,\quad
      {1\over a_2b_2}\widehat V_{a_1b_1,a_2b_2,k,l}
            \left({Kr\over a_2b_2}\right).            \tag{SK19}
\]

其余 e,q 条件亦不动。`c_U` 需要时再展开成小 Möbius 因子和
无符号 quotient；不得给该 quotient 添加 squarefree 掩码。
这是当前未覆盖真实窄带的精确 Type 分解，不是新的已证不等式。

## 6. 已发表输入能做什么，真正还差什么

| 输入 | 在本区块的可用结论 | 不能获得的结论 |
|---|---|---|
| BRZ Theorem 1.4，经 [IC7](2026-08-30-mwkf-inverse-c-signed-roundtrip.md) 的单位掩码转移 | 合法固定线性 A 行；既有 IC 成本可与 SK 取较好者 | 不得与 SK 节省相乘 |
| 初等 Poisson、Schwartz 与除数界 SK6–SK16 | 全光滑 κ 后的非共振覆盖和真实整数带上界 | 没有估计两个 Möbius 的联合消去 |
| [Matomäki–Teräväinen Theorem 1.5](https://arxiv.org/html/1911.09076v2#S1.Thmtheorem1.5) | 对没有额外掩码的线性相位短和，长于 D^{3/5} 的区间有对数节省 | 当前 moving κ-kernel、互素层与联合固定幂 saving 未自动转移 |
| [MSTT all-interval uniformity](https://arxiv.org/abs/2204.03754) | 适用无额外算术掩码的 D^{5/8+δ} 以上短和，任意对数幂节省 | 对数不能代替下述缺失的 T² |

平衡 e=1、K≈T 的共振面有
`A≈T²,d≈T³,kl≈T,j≈1,|r|≲T² L₀`。固定 A,k,l,j 后，d
窗口长约 `D/K=T²`，即 `D^{2/3}`。只说明几何长度匹配短区间
输入，不说明可直接套定理。SK13 得 T⁵，目标 T³，仍差完整
T² 消去；这必须发生在 (SK17) 的联合 signed 和或更早的全局
重组，不能假设每条 µ(A)µ(d) 仿射线有平方根消去。

两个不同整数共振的 signed 项也不能当正量相加来证明目标。
下一解析任务是估计 (SK17) 的九块**重组和**或它保留符号的
dispersion，而不是把它另命名成已关闭的 gate。全部原 AFE、
reflection、canonical zero/nonzero 合成及未纳入当前 smooth core
的端点/尾项，继续服从 [PA](2026-08-30-mwkf-physical-reflection-adapter.md)。
