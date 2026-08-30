# 联合 κ 与 Type-I quotient：保留全部互素频率后的实际覆盖

白话结论：上一轮逐 κ 的总变差界还没有用尽实际核的光滑性。
先将整个 κ 与无符号 Type-I quotient 一起变换，再估计非零
quotient 频率，能把这个 Type-I 部分的成本从 `ρDZUV` 降到
`ρDZUV/K`。在平衡顶层 `K≈Z≈T`、`UV` 为固定对数幂时，它
达到自身的 `T^{3+ε}` 预算。**这不估计完整 Type-II，不关闭
coupled-kernel gate，也不是完整 twisted-moment 证明。**

本节不是将两个 saving 相乘。它重新估计一个联合 signed 和，
仍保留实际 hδ 核和外层 µ(A)，只在证明上界时才付外层绝对值。
作为比较，先对单 κ 使用二阶导数估计也能得到 `ρD√Z UV`；
最后可取二者较好值，但不可再乘到 SK、IC、JG 或 BBLR 上。

## 1. 原系数、端点与实际二维核

沿用 [TI1–TI4](2026-08-30-mwkf-type-i-density-aliases.md) 和
[SK1–SK5](2026-08-30-mwkf-smooth-kappa-resonance.md)。固定
`A,e,q,k,l`，令

\[
 Q=Aeq,\quad B=bc,\quad D=S/e,\quad
 z_0={KAkl\over D},\quad \Lambda=|z_0|\asymp Z={RP\over S}.
 \tag{JQ1}
\]

原限制 `(e,Aq)=1` 不动；TI 完成中 `(B,Q)=1`。这里考虑
`Λ≥1,K≥1`；所有尺度为 T 的固定幂。定义

\[
 \mathfrak a(t,x)={w(t)\over x}\,
  \widetilde G\left({tKAe\over R},x,{kH\over Sx},{lL\over Sx}\right)
  \times\text{实际光滑分片权},
 \qquad t\in(1/2,3),\ x\in(1,2).                  \tag{JQ2}
\]

它是实际核，不是新增的任意算术系数。`KAe/R=A/X≈1`，双
Fourier core 的后两个坐标至多对数大小，故每个所需固定阶混合
导数为 `O(T^ε)`。`1/x` 已包括在幅度内；物理 `1/d` 因而是
`D^{-1}` 乘该幅度。支撑外以零延拓，所有积分无硬边界项。

TI2 的精确小端点仍是
`Σ_{b≤V,(b,Q)=1}µ(b)g_κ(b)`，并须对整个 κ 求和。只有 d 支撑
全部在 V 之上才可删除。κ=e=1 的独立 SK5 纠正项也仍保留；
固定 κ 分片满足 K>2 时它为零。**不能先删整数端点再套 Poisson。**

## 2. 双 Poisson 与连续密度：系数 K/(Bv)

暂只考虑一个 B 的完成和，所有离散求和因支撑有限：

\[
 \mathcal U_{B,Q}={1\over D}
  \sum_{\kappa\ge1}\sum_{\substack{m\ge1\\(m,Q)=1}}
  \mathfrak a(\kappa/K,Bm/D)
             e\left({z_0(\kappa/K)\over Bm/D}\right).
 \tag{JQ3}
\]

对 `v|Q` 置 `M_v=D/(Bv)`。对 κ 和 m 分别 Poisson，定义

\[
 H_j(x)=\int_{\mathbb R}\mathfrak a(t,x)
                 e(z_0t/x-jKt)\,dt,\qquad
 \widehat H_j(\xi)=\int H_j(x)e(-\xi x)\,dx.
 \tag{JQ4}
\]

于是精确有

\[
 \mathcal U_{B,Q}
  =K\sum_{v\mid Q}{\mu(v)\over Bv}
       \sum_{j\in\mathbb Z}\sum_{\ell\in\mathbb Z}
                         \widehat H_j(\ell M_v).
 \tag{JQ5}
\]

Jacobian 是 `KM_v/D=K/(Bv)`，没有额外 S 或 M_v。对固定
参数二维紧支撑光滑函数的 Fourier 系数快速衰减，故双和绝对
收敛。这里的 j 与 ℓ 均不是原 canonical zero Gram 的标签。

ℓ=0 的全体 j 精确重组为

\[
 \mathcal D_{B,Q}={\varphi(Q)\over BQ}
  \sum_{\kappa\ge1}\int
       \mathfrak a(\kappa/K,x)e(z_0\kappa/(Kx))\,dx.
 \tag{JQ6}
\]

这就是 TI 连续密度，不是遗漏的新主项。由于 `κ/K` 在固定
正支撑上，x 相位无驻点，故
`|𝒟_{B,Q}|≪_J T^ε K B^{-1}(1+Z)^{-J}`。可保留完整 signed
j 和使用此式；不能仅从后面的粗 `||H_j||₁≪1/Λ` 推出 rapid。
它也可由另一次 x 非驻相论证得到，不能当作该粗界的结论。

以下估计的是完整补集

\[
 \mathcal U_{B,Q}-\mathcal D_{B,Q}
   =K\sum_{v\mid Q}{\mu(v)\over Bv}
              \sum_{j\in\mathbb Z}\sum_{\ell\ne0}
                           \widehat H_j(\ell M_v).
 \tag{JQ7}
\]

## 3. 统一 x 导数范数与非零频率采样

令 `F(x,y)=∫𝔞(t,x)e(-ty)dt`，则 `H_j(x)=F(x,jK−z₀/x)`。
F 的所需混合导数在 y 上一致 Schwartz。链式法则给

\[
 |H_j^{(r)}(x)|\ll_{r,B_0}T^\varepsilon\Lambda^r
          (1+|jK-z_0/x|)^{-B_0}.
 \tag{JQ8}
\]

因 `|d(jK−z₀/x)/dx|=Λ/x²≈Λ`，单调换元给出对所有 j

\[
 \|H_j^{(r)}\|_1\ll_r T^\varepsilon\Lambda^{r-1},\qquad
 |\widehat H_j(\ell M)|\ll_J{T^\varepsilon\over\Lambda}
       \min\left\{1,\left({\Lambda\over |\ell|M}\right)^J\right\}
       \quad(\ell\ne0).
 \tag{JQ9}
\]

没有 K 的额外导数损失：jK 是关于 x 的常数。对任意实数
`a>0` 和 `J>1`，单调积分比较给完全显式的采样界

\[
 \sum_{\ell\ne0}\min\{1,(a/|\ell|)^J\}
 \le {2J\over J-1}a.
 \tag{JQ10}
\]

它对 a<1 仍成立，没有离散 `+1`，因为 ℓ=0 已独立提取。
取 `a=Λ/M_v`，(JQ9)–(JQ10) 说明每个 j 的 ℓ≠0 完整和，
在乘上物理系数 K/(Bv) 后至多 `T^ε K/D`。

## 4. 近 j、零 j 与无限远 j 一起结清

定义近集合 `0<|j|K≤2Λ`。其整数个数恰为
`2 floor(2Λ/K)≤4Λ/K`；若上界小于 1，集合就是空集。
因此近 j 对 JQ7 的绝对贡献（固定 v）至多

\[
                   T^\varepsilon{\Lambda\over D}.
 \tag{JQ11}
\]

剩下 j=0 以及 `|j|K>2Λ`。在这些位置
`|jK−z₀/x|≳Λ+|j|K`，故 JQ8 可强化为
`||H_j^(r)||₁≪T^ε Λ^r(Λ+|j|K)^{-B₀}`。
再用同一个 JQ10（例如 r=0,2），固定 v 的远部分至多

\[
 T^\varepsilon{K\Lambda\over D}
   \left\{\Lambda^{-B_0}+{\Lambda^{1-B_0}\over K}\right\}.
 \tag{JQ12}
\]

这里第一项包含 j=0，第二项由所有远 j 的积分尾给出。
在当前需要攻击的区域 `1≤K≤C₀Λ`，取 `B₀≥2` 即可将它
吸收到 JQ11。对 v 容斥的全部项使用 `2^{ω(Q)}≪T^ε`，得到

\[
 \boxed{K\sum_{v\mid Q}{|\mu(v)|\over Bv}
       \sum_{j\in\mathbb Z}\sum_{\ell\ne0}
                         |\widehat H_j(\ell M_v)|
       \ll_{C_0,\varepsilon} T^\varepsilon {Z\over D}.}
 \tag{JQ13}
\]

这是全 κ 与 quotient 的联合上界；并非将先前固定 κ 的估计
求绝对值相加。它不需要 v 小，也没有丢掉大除数驻相别名。
K 远大于 Z 的区域继续用 SK 的非共振结论及其原端点账本。

### 可直接截断的双频率尾

取整数 `J₀≥max(1,2Λ/K)`，每个 v 取整数 `L_v≥1`。
在 JQ7 中只保留 `|j|≤J₀,0<|ℓ|≤L_v`。对任意固定
`B₀>1,J>1`，遗漏部分的绝对值至多常数乘

\[
 T^\varepsilon\sum_{v\mid Q}|\mu(v)|\left\{
  {\Lambda K^{1-B_0}\over D}J_0^{1-B_0}
  +{K\over Bv}(2J_0+1)\Lambda^{J-1}
                 M_v^{-J} L_v^{1-J}\right\}.
 \tag{JQ14}
\]

第一项是全部远 j，已经包含其无限 ℓ 和；第二项是在剩下有限
j 上使用 JQ9 的 ℓ 尾。若恢复 c,b,A 等外层，须再逐项付其
实际数量与系数。ℓ=0 连续密度按 JQ6 保持精确，不在这个尾内。
因此没有把一个无限 Poisson 和误称为无误差有限恒等式。

## 5. 恢复物理外层与全部 e-shell

TI2 的系数仍是 `−µ(c)µ(b)`、`c≤U,b≤V`。JQ13 对每对 c,b
独立于 B，故支付至多 UV 对。此时剩余外层是
`C·XP=ρD²/K`，**不是再乘 κ 数量 K**。连续密度则使用
`Σc,b1/(bc)≪log(2U)log(2V)`。当精确小端点为零时，

\[
 |\mathcal B^{I_d}_{e,K}|
  \ll_J T^\varepsilon\rho
       \left\{D^2(1+Z)^{-J}+{DZUV\over K}\right\}.
 \tag{JQ15}
\]

对全部 `e≈E₀`，不是只取 e=1，得到

\[
 \sum_{e\asymp E_0}|\mathcal B^{I_d}_{e,K}|
  \ll_J T^\varepsilon\rho
       \left\{{S^2\over E_0}(1+Z)^{-J}+{SZUV\over K}\right\}.
 \tag{JQ16}
\]

若小端点或 SK5 不为零，须另加其原 signed 贡献；不声称已估计。
在平衡 R=S 上，`X=R/(eK)≥1` 自动给 `D≥K`。因此取 V≤K
即可同时满足所有这些 e 的 d 端点条件。若还 U≤K，d-small
系数也全部消失。对数多个 e-shell 可吸收到 T^ε，固定 q 的
原限制仍在；这不等于已经估计了整个原 AFE 的所有外参数。

## 6. 单 κ 的二阶导数改进，可与联合界取较好者

在 TI3 的相位 `z/x−ξx` 中，二阶导数为 `2z/x³`。将
`|φ'|≤√|z|` 的区间（长度 `O(|z|^{-1/2})`）与其至多两个
补区分开，在补区用一次分部积分，可得
`|Ψ̂_z(ξ)|≪T^ε |z|^{-1/2}`，对所有 ξ 一致。
`|ξ|>2|z|` 时则有任意阶 `O_J(T^ε|ξ|^{-J})`。
这就是经典 van der Corput 与非驻相方法；可参见
[Tao 247B notes 8, Lemmas 2.5–2.6](https://www.math.ucla.edu/~tao/247b.1.07w/notes8.pdf)。
上述分区给出本节所需的自包含证明，没有引入新的谱定理假设。

置 `h=D/(Bv)`，非零近带数量为 `2 floor(2|z|/h)≤4|z|/h`。
远带对 J=2 已满足
`h Σ_{|ℓ|h>2|z|}(|ℓ|h)^{-2}≤2/|z|`。
所以每个单 κ 的全部绝对别名至多 `T^ε√Z/D`，比 TI6 的
`T^ε(1+Z)/D` 强。恢复整个 κ 的绝对数量后，物理项为
`T^ερD√Z UV`。结合 JQ15，真正可用的是

\[
 T^\varepsilon\rho\left\{
 D^2(1+Z)^{-J}+DUV\min(\sqrt Z,Z/K)\right\}.
 \tag{JQ17}
\]

这是两个同一归一化上界的最小值，不是节省相乘。

## 7. 新参数覆盖，以及还必须处理的 Type-II

一般写 `ρ=T^ω,S=T^s,e≈T^η,Z=T^ζ,K=T^ν,UV=T^β`。
联合界的单 e 非零成本指数为 `ω+s−η+ζ+β−ν`，整个 e-shell
则为 `ω+s+ζ+β−ν`。只比较一个 e 会虚构额外的 T^η 节省。
连续密度需要单独支付；以下覆盖取固定 `ζ>0`，因而可选择 J
将其压小。ζ=0 不能仅由下面的不等式宣称覆盖。

在平衡 `R=S=T³,HL≈T⁵,P=T^p` 上，`ρ=T^{p−1},Z=T^p`。
对 SK 尚未排除的 `0<ν≤p` 和已核验的端点，固定 q 的这一个
Type-I 部分（包括全部 e-shell）达到 S 预算的充分条件为

\[
  \min\{3p/2+\beta,\;2p+\beta-\nu\}\le1,
  \qquad p>0\text{ 固定}.
 \tag{JQ18}
\]

| 输入 | Type-I 非零部分的整个 e-shell 指数 | 自身 S 预算条件 |
|---|---|---|
| TI 的 BV 完成 | `2+2p+β` | `2p+β≤1` |
| 单 κ 的二阶导数界 | `2+3p/2+β` | `3p/2+β≤1` |
| 联合 κ/quotient JQ13 | `2+2p+β−ν` | `2p+β−ν≤1` |

例如 `p=ν=3/4,U=V=T^{1/8}`，β=1/4，联合指数正好 3，
单 κ 驻相指数为 27/8，旧 BV 为 15/4。这里 V≤K，所有有效
e 的端点安全；`K≈Z`，不在 SK 的大 K 非共振快速衰减区。
这是一片真实新增的 Type-I 覆盖，不是整个原区块的覆盖。

顶层 `p=ν=1` 时，取 U,V 为任意固定对数幂，则 `UV=T^{o(1)}`，
JQ16 是 `O(T^{3+ε})`。因此这类短 Type-I 和 d-small 部分在
该顶层不再需要额外的 signed saving。然而精确 SK18 还包含
完整 Type-II；取更小 U,V 会将更多质量转移给它，不会令它
消失，也不构成 coupled-kernel gate 的替代证明。

对 Type-II 再展开 `c_U(a)` 后，µ(A) 与长 µ(b) 同时存在，
还保留 `cm>U,b>V`、单位掩码与实际核。JQ13 只对无符号 m
完成；逐 b 取绝对值会支付长 b 的全部数量，不能沿用短 UV
成本。要关闭目标，仍须在保留这些长 Möbius 系数的联合和中
获得新消去，或对完整外层先重组。本文没有给出该估计。

原 canonical zero Gram、两个 reflection 交叉项、完整非零
补集和物理端点/尾仍按 [PA](2026-08-30-mwkf-physical-reflection-adapter.md)
共同保留。此处的 Type-I 覆盖不允许删除那些独立义务。
