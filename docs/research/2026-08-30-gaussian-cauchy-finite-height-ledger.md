# 有限高度门槛重算：精确 Gaussian–Cauchy 常数与三个同时活跃的约束

按“先检查检测归一化，再攻最坏块，最后优化有限高度参数”的顺序重算，
得到了一个实际的条件性改善：在 `T=3·10^12`，保留 Gaussian–Cauchy 核常数
后，假设零点强制的**未归一化**边界二阶积分大于 `0.504`，而非示意性的
`1/log T≈0.0348`。因此“即使总常数 C=1、B=0 也必需到 10^97”的推断并不
对所有合法检测核成立。但是 `1/log T` 的渐近尺度没有消失，实际算术输入
及其常数仍未证明，不能据此宣布有限高度桥或零点界完成。

第二个发现是：旧 `7/289` 同时由内层小导体块与独立外边界取到。
只加强前者，即使允许重新选择 `θ`，保留另外两个旧约束后的最优余量也
至多为 `19/289`。本笔记给出这个模型的精确分段最优值和有限高度凸优化式。

## 1. 复用的工作树与先排除的旧问题

本次逐项读取，未修改以下旧工作树：

- `prove-14-over-17-math-20260824`，工作树 HEAD/base 为 `6c38296c`：
  引用的是**本地未跟踪**的 `2026-08-24-reciprocal-lcm-dual-zero-amplifier.md`，
  §§208、210、269、274、393、495；该稿不在此 commit 的 tree 内。
  本次读取版本的 SHA-256 为
  `c1e78057285f106675aff8acf49114cedac512f879964fa592e4fd5c0d9f8e1d`。
- `prove-eventual-14-over-17-20260826`，commit `af891896`：
  `2026-08-26-eventual-14-over-17-mwkf-proof-audit.md`，§67。
- `fixed-line-eventual-transfer-20260830`，commit `5e076274`：
  `2026-08-30-fixed-line-eventual-zero-free-transfer.md` 全文。

后两份是相应 commit 的干净受跟踪文件。本文所需转移证明及代数模型均在
下文独立写出，不以未跟踪旧稿作为缺失证明的代替。

旧 §393 对 `h_N=1-E_N^2` 使用 Poisson–Jensen 时遗漏内点项
`-log|h_N(z_*)|`；仅有 `log^+|h_N|≤|E_N|²` 并不能处理它。
后续 §67 已明确更正，改用 `E_N(ρ)=-1` 的 Cauchy 公式。
所以本次不从缺项的 Green 等式“优化常数”，而从修复后的 Cauchy 恒等式开始。
已存在的固定线转移定理也只是条件定理，不证明其所需二阶矩。

## 2. 一个完全显式的局部转移不等式

设 `T≥e^25`，固定

\[
 \sigma=\frac{14}{17},\quad \theta=\frac{30}{17},\quad
 N=\lfloor T^\theta\rfloor,\quad h=\frac1{\log T},\quad
 a=\sigma-h,\quad H=T/2,
 \quad E_N(s)=\zeta(s)\sum_{n\le N}\mu(n)n^{-s}-1. \tag{1}
\]

在整个区间使用**同一个** `N`。令

\[
 I_a(T)=\int_{T/2}^{5T/2}|E_N(a+it)|^2dt. \tag{2}
\]

若存在零点 `ρ=β+iγ`，`γ∈[T,2T]`、`σ≤β<1`，记 `d=β-a`。
在矩形 `[a,2]+i[γ-H,γ+H]` 上用核

\[
 \frac{E_N(z)\exp(\lambda(z-\rho)^2)}{z-\rho},\qquad \lambda>0.
 \tag{3}
\]

矩形不包含 ζ 在高度零的极点；`E_N` 在其邻域全纯，且 `E_N(ρ)=-1`。
把右边和两条水平边的绝对积分之和记为 `R_λ`，Cauchy 公式及左边
Cauchy–Schwarz 给出

\[
 2\pi\le\sqrt{I_a(T)\,K_\lambda(d)}+R_\lambda,\qquad
 I_a(T)\ge\frac{(2\pi-R_\lambda)^2}{K_\lambda(d)}
 \quad(R_\lambda<2\pi), \tag{4}
\]

其中左边有限区间包含于 (2)，核平方积分向全实线放宽：

\[
 \boxed{K_\lambda(d)=e^{2\lambda d^2}
 \int_{\mathbb R}\frac{e^{-2\lambda y^2}}{d^2+y^2}dy
 =\frac\pi d e^{4\lambda d^2}
       \operatorname{erfc}(\sqrt{2\lambda}\,d).} \tag{5}
\]

可直接证明最后的等式：写
`1/(d²+y²)=∫_0^∞ exp(-u(d²+y²))du`，用非负 Fubini 先积分 `y`，
再令 `v=d√(u+2λ)`，即得
`∫e^(-2λy²)/(d²+y²)dy=(π/d)e^(2λd²)erfc(√(2λ)d)`。
这里 `erfc` 的定义与 [DLMF 7.2.2](https://dlmf.nist.gov/7.2#E2) 相同。
特别注意 (5) 是 `exp(4λd²)`，不是只保留一份指数。

### 2.1 三条剩余边的显式上界

右边绝对收敛的逆 ζ 尾恒等式给出

\[
 E_N(2+it)=-\zeta(2+it)\sum_{n>N}\mu(n)n^{-2-it},\quad
 |E_N(2+it)|\le\zeta(2)/N<2/N.
\]

又 `2-β≥1`，所以

\[
 R_{\rm right}\le\frac2N\sqrt{\frac\pi\lambda}
 e^{\lambda(2-\sigma)^2}. \tag{6}
\]

这利用了真实右边数据，不是半平面任意 Hardy 函数的假设。
水平边上 `|z-ρ|≥H`，`|Re z-β|≤2-σ`。因 `a≥3/4`、`N≤T²`，
有 `∑_{n≤N}n^(-a)≤1+4N^(1/4)≤5√T`。
Euler 积分表达式给 `|ζ(z)|≤|z|/|z-1|+|z|/Re z≤6T`：这里
`T/2≤|Im z|≤5T/2`、`|z|≤3T`，所有不等式在当前 `T` 范围成立。
因此 `|E_N(z)|≤31T^(3/2)`，每条水平边长小于 `5/4`，从而

\[
 R_{\rm hor}\le155\sqrt T\,
 e^{\lambda(2-\sigma)^2-\lambda T^2/4}. \tag{7}
\]

下文 `R_λ` 可统一取 (6)+(7)。本节不使用 Möbius 消去、零点简单性、
`1/ζ` 在未知零点附近的上界或未证明的全局移线。
负高度由 `E_N(bar s)=overline(E_N(s))` 的共轭对称得到相同结论。

### 2.2 取 λ=10 后，对所有 β≥σ 的统一性

不能只把目标放在 `β=σ` 计算，而忘记别的候选零点。
由 `T≥e^25` 得 `h≤1/25` 且
`h≤d≤3/17+h<11/50`。证明

\[
 \sup_{h\le d\le3/17+h}K_{10}(d)=K_{10}(h). \tag{8}
\]

当 `d≤1/10`，对 (5) 取对数求导，有

\[
 \frac{K_{10}'(d)}{K_{10}(d)}
 =80d-\frac1d-
 \frac{2\sqrt{20}}{\sqrt\pi}
 \frac{e^{-20d^2}}{\operatorname{erfc}(\sqrt{20}d)}<0.
 \tag{9}
\]

当 `1/10≤d≤11/50`，由
`erfc(v)≤exp(-v²)/(√π v)` 得

\[
 K_{10}(d)\le\sqrt{\pi/20}\,e^{20d^2}/d^2<50. \tag{10}
\]

因为 `e^(20d²)/d²` 在 `d<1/√20` 递减，上界可在 `d=1/10` 取值；
再用 `√(π/20)<2/5`、`e^(1/5)<5/4`。
另一方面 `erfc(v)≥1-2v/√π` 给出
`K_10(h)≥π/h-2√(20π)>75-18=57`。
这证明 (8)，不靠网格扫描最坏 `β`。

于是统一检测阈值为

\[
 \boxed{I_a(T)\ge L(T):=
 \frac{(2\pi-R_{10}(T))^2 h}
 {\pi e^{40h^2}\operatorname{erfc}(\sqrt{20}h)}.} \tag{11}
\]

## 3. 在验证高度的条件算例与渐近边界

取 `T_v=3·10^12`；这是
[Platt–Trudgian 已发表的验证高度](https://arxiv.org/abs/2004.09765)，本文不声称
它是当前最高记录，也不重新进行零点计算。由上述完全显式函数，近似值为

\[
 h=0.034807266\ldots,\quad K_{10}(h)=78.231458\ldots,
 \quad L(T_v)=0.504636096\ldots,
 \quad T_v^{-7/289}=0.498638710\ldots. \tag{12}
\]

最后一项 `R` 对所示位数无影响，但证明中不能删掉它。
附带脚本用有理数上下界另行认证较宽但严格的

\[
 R_{10}(T_v)<2\cdot10^{-11},\qquad
 L(T_v)>0.504,\qquad T_v^{-7/289}<0.499. \tag{13}
\]

因此，**如果**同一个未归一化积分 (2) 真有总上界
`I_a(T_v)≤T_v^(-7/289)`，就在这个 dyadic 高度块产生矛盾。
这是给定输入时的局部转移，不是输入的证明，也不直接填满所有 `T≥T_v`。
如果算术估计针对的是加权积分，需要显式的正权覆盖常数；如果它针对的是
`I_a/T` 或 `I_a/(4π)`，必须先恢复归一化，不能直接带入 (11)。

这里对总乘法常数的容许量只有约 `1.012`（且假设 `B=0`）；微小的实际
常数、对数因子或多个误差分量之和都可能耗尽它。不是“常数已经控制”。

对于 `T→∞`，`λ=10` 固定，`R→0` 且 (5) 给出

\[
 L(T)\sim4\pi h=\frac{4\pi}{\log T}. \tag{14}
\]

所以没有去掉对数门槛。旧 §495 的半平面极值例子
`2h/(s-a+h-iγ)` 在候选点取值 1、左边平方积分等于 `4πh`，说明只凭
该类点值和边界积分不能要求零点贡献固定正质量。它在固定右边通常是
`O(h)`，不满足本题的 `O(N^-1)` 尾；因此 (12) 比 `4πh` 略大不与它矛盾。
本文不据此宣称所有可能利用更多算术信息的检测器均有同一障碍。

固定左移 `h>0` 会令信号固定，但也须重新估计左线误差。若使用有限长度
`N=T^θ` 的系数权比较，其平方权尺度变化为 `N^(2h)=T^(2θh)`；如果改用
固定线解析插值，则必须付出相应增长界的插值代价。两者均不能只重标定
信号而保持旧算术上界不变。

更一般地，若另外证明了某个移线代价模型
`I_(σ-h)≤Q(T)exp(c h log T)`，`c>0`，那么使用领先信号 `4πh` 时，
误差/信号比的最小值在 `h=1/(c log T)` 取得（前提是该点属于适用区间），
其值为 `e c Q(T)log T/(4π)`。这解释了优化左移距离后仍会出现对数。
它只是给定移线代价的标量优化；本文没有从系数逐项大小推出完整有符号
二阶矩满足该移线比较，也没有忽略 (11) 在有限高度的精确修正。

## 4. 最坏块不是唯一活跃约束：只加强它的精确收益

这里**仅分析旧条件模型**。未证明其对所有实际包成立；旧 §319 的低端
系数投影/范数次序缺口以及完整二阶矩组装义务仍在。
从 §208 提取三个指数：

\[
 A(\theta)=\frac{39\theta-68}{34},\qquad
 O(\theta)=\frac{11-6\theta}{17},\qquad
 M(\theta)=\frac{11\theta-17}{17}. \tag{15}
\]

分别来自内层下模数平台、外边界、主对角。`θ=30/17` 时
`A=O=7/289`、`M=41/289`。内层等号点的真实参数是

\[
 q=43/34,\quad\Delta=2/17,\quad\tau=0,\qquad
 c\asymp T^{13/17},\quad D\asymp T^{43/34},\quad K\asymp T^{9/34}.
 \tag{16}
\]

其中 `q` 是 `D` 的幂指数，不是另一个数值模数。
旧 §274 进一步识别：两条非主特征的乘积可以是主特征，形成
`ψ=bar χ` 的 Ramanujan 对角；不能把这一块全部交给非平凡 Kloosterman
模态的谱节省。完整两-Möbius 系数在绝对收敛区对应 `1/L(s,χ)^2`，
不是已知一因子抵消可以直接代入的任意系数。

即使乐观地假设内层平台**一致**增加 `η≥0`（改善单个等号点还不够），
新的三项模型最优值也只是

\[
 \boxed{\max_\theta\min\{A(\theta)+\eta,O(\theta),M(\theta)\}
 =\begin{cases}
 7/289+(4/17)\eta,&0\le\eta\le3/17,\\
 19/289,&\eta\ge3/17.
 \end{cases}} \tag{17}
\]

第一段在 `θ=30/17-(2/3)η` 取到。因为前两条线一升一降，它们的交点
给二者最小值的最大值；该处 `M` 不小于共同值恰好要求 `η≤3/17`。
第二段由另外两条线 `O=M`，即 `θ=28/17` 给出；该处
`A=-32/289`，所以 `η≥3/17` 后第一项也不再限制。
这同时证明上界与达到性。若实际适用参数域更窄，模型最优值只会降低。

`19/289≈0.06574` 仍小于旧单位阈值要求的
`log log(T_v)/log(T_v)≈0.11688`。因此只攻一个最坏块无法兑现旧归一化下
所需的约 `0.12` 余量；至少还要改变外边界/对角之一或检测比较。
这个结论不否定该块值得改进，而是给其独立收益划定准确上限。

## 5. 有限高度 θ 优化：必须加误差，不能只平衡指数

若未来逐项证明同一积分的有效上界

\[
 I_a(T)\le F_T(\theta):=
 C_A\ell^{B_A}T^{-A(\theta)}+
 C_O\ell^{B_O}T^{-O(\theta)}+
 C_M\ell^{B_M}T^{-M(\theta)},\quad\ell=\log T, \tag{18}
\]

且这些常数在所优化参数区间内固定，则 `F_T` 严格凸。以 `E_A,E_O,E_M`
表示三个非负项，内点最小值的准确方程为

\[
 \frac{39}{34}E_A+\frac{11}{17}E_M=\frac6{17}E_O. \tag{19}
\]

若忽略第三项，仅作两项模型，则

\[
 \theta_{\rm two}(T)=\frac{30}{17}+
 \frac{2}{3\ell}\log\left(\frac{13C_A}{4C_O}
                  \ell^{B_A-B_O}\right). \tag{20}
\]

此时是 `E_A/E_O=4/13`，不是要求它们相等；约束区间内无临界点时应取
端点。若真实 `C_j` 依赖 `θ`，必须把这种依赖一起微分或作区间上界，
不能把它们当常数。

作为明确标注的**演示，不是物理上界**，在 `T_v` 取每项 `C_j=1,B_j=0`：

\[
 \theta_{\rm opt}\approx1.792713446,
 \quad F_{T_v}(\theta_{\rm opt})\approx0.870616955,
 \quad F_{T_v}(30/17)\approx1.014255531. \tag{21}
\]

重选参数有收益，但两者都超过 (12)。这与 §3 的假设算例没有矛盾：
“总上界常数为 1”与“每个分量的常数均为 1”不是同一输入。
实际 dyadic、gcd、平滑覆盖和非本原特征的常数必须逐项给出，不能编造
数值后用 (19) 作为已完成的有限高度优化。

还有一个必要的跨高度检查：即使一直给予假设总上界 `T^(-7/289)`，固定
`λ=10` 的 (11) 也不能从 `T_v` 自动向所有高度延伸。例如在 `log T=45`，
即使忽略正的边界误差，误差/允许量的比值为

\[
 \frac{45}{4\pi}e^{-(7/289)45+40/45^2}
       \operatorname{erfc}(\sqrt{20}/45)
 \approx1.09079>1. \tag{22}
\]

脚本也用有理数下界认证其大于 1。因此单个高度的条件改善并不构成
中间高度桥；改变 Gaussian 参数时还须重新控制右边指数和所有候选 `β`。

## 6. 交付边界与下一步

本次新增可复用的结果是 (4)–(11) 的显式统一检测不等式，(13) 的有理数
认证条件算例，以及 (17)、(19)–(20) 的精确模型优化。
它确实推翻了“单位比较已经证明必须到 10^97”的过强读法，但没有证明
所需实际误差界，更没有证明 `14/17` 或 `2/3`。

后续实质输入必须是：同一 `N`、正确归一化的完整移动线或固定线二阶矩，
以及所有分量共同有效的常数和参数范围。已有固定线转移可避免另证移动线
一致性，但其插值成本也必须包含在有限高度比较中。
较弱全局零点界的自举需要一个已证起点及可量化的反馈估计，本次没有假设
这样的起点已经存在。

验证脚本 `scripts/check_gaussian_cauchy_finite_height.py` 使用标准库和有理数
区间认证 (13)，并以有限代数/数值检查保护模型优化。浮点显示值仅作说明。
它不提供算术二阶矩、零点计算、全高度桥或 Lean 验证。

### English summary

An exact Gaussian–Cauchy calculation gives a uniform conditional lower
bound greater than 0.504 for the unnormalized boundary moment at height
3e12, compared with the toy upper bound T^(-7/289) below 0.499. This
improves the previously schematic detection constant, but retains the
asymptotic inverse-logarithm scale and proves no arithmetic input. In the
old three-exponent model, improving only the inner plateau caps the
optimized margin at 19/289 because the outer and diagonal constraints
remain. Finite-height optimization balances weighted error derivatives,
not exponents alone. No eventual or global zero-free theorem is claimed.
