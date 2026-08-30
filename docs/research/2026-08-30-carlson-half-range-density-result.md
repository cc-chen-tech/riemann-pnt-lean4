# Carlson 型零密度改进：δ=1/400，B=6

本分支已给出实际 ζ 零点的无条件全局定理，并逐项通过 Lean：

\[
 N_{\ge}(2/3,T)\ll T^{8/9-1/400}(\log T)^6.
\]

这里 `N_ge` 统计 `0<Im rho<=T`、`Re rho>=2/3`，按 ζ 的真实解析重数计数。
旧接口使用严格实部不等号，由 `N_> <= N_ge` 同时得到其结论。
这不是新的最佳零密度指数，也不声称数学上的首创性：成果是指定 Carlson
检测器路线的可核查改进及无条件形式化，而不是引用 Ingham 替换该路线。
最终联合回归、公理审计及 forcing 接线已验收；证据和严格的声明边界见本文末尾。

## 1. 原框架反推与精确 no-go

在高度 `T` 的原 Carlson 证明中，取 `X=floor(T^x)`，先在
`sigma_0=sigma-O(1/log T)` 上作 Littlewood 计数。乘积多项式长度
`L=O(TX)`，卷积系数 `a_X(n)=sum_{d|n,d<=X} mu(d)` 在
`1<n<=X` 消失，且 `|a_X(n)|<=d(n)`。标准均方估计的两部分为

\[
 T\sum_{n>X}|a_X(n)|^2n^{-2\sigma_0},\qquad
 \sum_{X<n\ll TX}n|a_X(n)|^2n^{-2\sigma_0}.
\]

代入除数平方和界，分别得到
`T X^(1-2sigma_0) log^3(TX)` 与 `(TX)^(2-2sigma_0) log^3(TX)`；
截断余项见原模块 `CarlsonAsymptotic` 的 ambient-majorant 装配。
对固定有界 `x`，将 `sigma_0` 换回 `sigma` 只付常数；Littlewood 权重
`1/(sigma-sigma_0)` 付一个对数，水平边的多对数不改变幂次。因此

\[
 E_L=1+x(1-2\sigma),\qquad E_U=(1+x)(2-2\sigma).
\]

这是原模块 `carlson_optimized_lower_ambient_term_le` 与
`carlson_optimized_upper_ambient_term_le` 在代入最优长度之前的两个单项式。
第一项有正对角来源；第二项是一般均方误差的正上界，不能把它误称为
实际积分不可消除的正对角。三角不等式丢弃的符号主要在第二项。
更具体地，对每个素数 `X<p<=2X`，`a_X(p)=1`。由素数定理，这些项本身
给对角下界 `gg T X^(1-2sigma)/log X`；因此尖截断权的该正对角不能靠
保留 Möbius 符号取得固定幂次节省。这个测试不把非对角上界变成下界。

精确定义本 no-go 的方法类：只用上述两个固定幂次上界，允许改变常数、
对数次数及长度 `x`，最终保证的幂次为两者最大值。因为
`E_L-E_U=2sigma-1-x`，在 `1/2<sigma<1` 时前者严格递减、后者严格递增，
故

\[
 \inf_{x\in\mathbb R}\max(E_L,E_U)=4\sigma(1-\sigma),
 \quad \text{唯一取等点 }x=2\sigma-1.
\]

物理长度范围 `0<=x<=1` 也包含此取等点。端点 `sigma=1/2,1` 的唯一性
不在定理范围内。`sigma=2/3` 时是 `1-x/3`、`2/3+2x/3`，最优 `x=1/3`、
值 `8/9`。这只排除该方法类，不排除下面更广的 Carlson 型改造。

若两条线有与 `x` 无关的节省 `delta_L,delta_U`，交点变为
`x*=2sigma-1-delta_L+delta_U`，相同证明给出

\[
 q_{new}=4\sigma(1-\sigma)-2(1-\sigma)\delta_L-(2\sigma-1)\delta_U.
\]

这是全实数 `x` 上的精确公式；限制长度区间时须额外确认 `x*` 在区间内。
在 `sigma=2/3` 即 `8/9-(2/3)delta_L-(1/3)delta_U`。这些式子及唯一性
均由 `CarlsonLengthMinimax.lean` 形式化。

## 2. 成功路线及归一化

取 `Y0=floor(V^(2/5))`、`Y1=floor(V^(9/20))`，定义

\[
 w(n)=\begin{cases}1&n\le Y_0,\\
 \log(Y_1/n)/\log(Y_1/Y_0)&Y_0<n\le Y_1,\\0&n>Y_1,\end{cases}
 \qquad M(s)=\sum_{n\le Y_1}\mu(n)w(n)n^{-s}.
\]

两尺度权是两个线性 Selberg 权的精确线性组合，组合常数在 `V→∞` 时有界。
设 `F=zeta M-1`、`G=1-F^2`、`H=(s-1)^2G`。`H` 在正实部半平面解析，
每个 ζ 零点都是 `H` 的零点，且 ζ 重数不超过检测器重数。

核心以下卷积系数严格消失，不是假设 Möbius 平方根消去。临界线一侧用
平方根 AFE（包括正确的单位相位）、保留嵌套截断的有限二进制最大估计、
短 Dirichlet 多项式均方，得到真实全线 Gaussian 乘积矩。
`9/20<1/2` 保证所需短多项式范围；没有调用 DI/Kuznetsov 门。
远右侧使用核心消去，得到 `|F(4+it)| <= (10/3)Y0^(-3)`。

实际 Lean 归一化取 Gaussian 宽度 `Delta=16 V^(19/20)`，中心在
`[2V,3V]`，权为 `exp(-((t-w)/Delta)^2)`，积分为全实线积分。
`CarlsonHalfRangeEndpointBudget` 的局部两端是
`C V^(19/20)(1+log V)^6` 与 `D V^(-29/20)`。
三线后覆盖 `[2V,5V/2]` 需要 `O(V^(1/20))` 个窗口，故实际幂次为
`q(x)=1-(12/5)(x-1/2)/(4-1/2)`，在 `x=2/3` 得 `31/35`。
这完整保留了窗口长度和覆盖成本，没有把局部指数当成全局指数。

原纸面设计还使用一个较粗的、**覆盖归一化后**的两端账本 `1+epsilon`
与 `1+2a(1-R)`，其中 `a=2/5,R=4,epsilon=1/2000`；它比实际
`epsilon=0` 的指数稍弱，便于预留余量。在 `sigma=2/3` 权重为 `1/21`，所以

\[
 q_*={20\over21}(1+1/2000)+{1\over21}(1-12/5)
 ={1861\over2100},\qquad
 (8/9-1/400)-q_*={1\over5040}>0.
\]

实际左边界从固定区间 `(2/3-1/10000,2/3-1/20000)` 中选择；一致条带界
保留足够余量，所有阈值与常数先于该边界和内嵌高度区间。
水平边在 `[U-1,U]` 和 `[9U/8,9U/8+1]` 选择，使用同一 `V=10U/21`
和同一对整数长度。每边加权辐角积分为 `O((1+log U)^2)`；完整竖边
预算为 `O(V^(8/9-1/400)(1+log V)^6)`，包括正则化因子的精确抵消。
由 `2/3-x>=1/20000` 得闭壳 `[U,9U/8]` 的实际重数和上界。

最后对真实累计计数证明不交递推
`N_ge(2/3,9U/8)<=N_ge(2/3,U)+C U^q(1+log U)^6`。
正指数的几何求和吸收初始高度且不增加对数次数，再用
`(1+log T)^6<=64(log T)^6`，得到开头的全局定理。
完整过程在 `CarlsonHalfRangeDensity.lean` 的四个公开结论中没有解析前提。

分类：这是保留 Carlson 检测器与轮廓、引入额外临界均方/插值技术的 Carlson 型
改进，不是原两直线中只调长度。新插值几何不等于旧端点各减固定常数；
若仅作最终指数账本，`delta_L=0,delta_U=3/400` 给出相同 `q`，但这
不是对所有 `x` 都成立的新旧端点比较定理。实际可证明的节省为 `delta=1/400`。

## 3. 候选路线逐项结论

### 平滑与多段权

精确可用命题是第 2 节的双尺度矩与核心消去。单段线性 Selberg 权不在固定小整数
处等于 `1`，例如固定素数 `p` 的卷积系数约为 `log p/log Y`，会失去远右侧
所需的核心幂次衰减。双尺度修复此问题。正临界对角仍保留高度长度量级，未被
“消去”。已发表的 Conrey Theorem 2 覆盖更强的 `theta<4/7` 线性权矩；本次
实际 Lean 路线独立证明所需的 `theta<1/2` 特例。它改造旧上端预算，不能声称
`delta_L>0`；最终节省如上。

### 变分最优权

对任意实数权 `lambda_d`（`1<=d<=Y`，`lambda_1=1`），考虑精确有限二次型

\[
 Q(\lambda)=\sum_{d,e\le Y}{\lambda_d\lambda_e\over[d,e]}
 =\sum_{r\le Y}\varphi(r)y_r^2,\quad
 y_r=\sum_{r\mid d\le Y}\lambda_d/d.
\]

有限 Möbius 反演给 `sum mu(r)y_r=1`。Cauchy 得
`Q>=1/G(Y)`，其中 `G(Y)=sum_{r<=Y}mu(r)^2/phi(r)`；取
`y_r=mu(r)/(phi(r)G(Y))` 并反演即取等，故这是完整有限变分最优性证明。
它说明该正二次型不能被符号估计抹掉，但该二次型不是整个 Carlson 均方。
增加 plateau 约束只会缩小可行集；优化此型本身没有给本次端点任何额外
`T^(-delta)`，账本 `delta_L=delta_U=0`。更一般多段权的完整带非对角
泛函优化仍是另一任务，不能由这个有限 no-go 否定。

### 高阶矩与大值

归一化测试：若在长度 `Delta` 的同一窗口，实际误差满足
`integral |F|^(2k) <= C Delta T^(-k s) log^A T`，Hölder 才能给
`integral |F|^2 <= C^(1/k) Delta T^(-s) log^(A/k) T`。
缺少 `Delta` 或阈值归一化的高阶矩不能直接记作端点节省；常数函数测试
已否定对任意系数、任意检测器的一概幂次消去。在本次证明中未得到适配当前
`F` 的额外 `s>0` 命题，因此新增 `delta_L=delta_U=0`。
Guth–Maynard 提供独立的大值技术和密度结论，但没有把其最终密度定理接成
本证明的前提；其直接替换属于用户排除的第 3 类。

### 保留 Möbius 符号的非对角

对 `P(t)=sum b_n n^(-it)` 和固定非负光滑窗 `W(t/T)`，精确非对角为
`T sum_{m!=n} b_m conjugate(b_n) W_hat(T log(n/m))`，傅里叶约定
`W_hat(u)=integral W(v) exp(iuv)dv`，符号须与展开中 `log(n/m)` 同时固定。
只有对实际卷积系数、gcd 层、平移核一致的估计才能替换原均方误差。
其正对角 `T W_hat(0)sum |b_n|^2` 必须另记；无符号三角估计不会节省它。
本次半长证明不需要一个未证明的 Möbius dispersion 命题，额外谱节省记为 `0`。
Conrey/DI 的 taper 范围不能直接当作尖截断权或 `T^3` MWKF/QCT 的定理。

### 局部高度窗口

若同一 detector 在长度 `Delta` 的窗口有界 `C Delta T^(q-1)log^B T`，
覆盖长度 `T` 需 `O(T/Delta)` 窗，合计仍为 `T^q log^B T`。
因此局部化本身 `delta_L=delta_U=0`。本证明的真实全线 Gaussian 控制包含尾部，
不是把 `[0,T]` 均方误用作全线界；闭壳比例改变也只付几何常数。

### forcing 特殊零点族

精确可用结论：对任何有限实际零点族 `S` 满足
`Re rho>=2/3, U<=Im rho<=9U/8`，其 ζ 重数和均受第 2 节闭壳界控制。
若要求比全体零点更强的族专属节省，须额外证明 forcing 所产 `S` 的确定性
结构能给 `sum_S m_zeta << U^(q-eta)`、`eta>0`，并验证 forcing 到 `S`
的映射和重数。此项尚无本次可用的定理，额外节省记为 `0`；不能按随机稀疏性猜测。

## 4. 14/17 与 MWKF/QCT 的实际影响

在 `T=X^(lambda(1-beta))`，旧 forcing 损失 `qF=8/9` 不变时，幂次余量为

\[
 \lambda[2(\beta-2/3)-(1-\beta)(8/9+q_D)].
\]

在 `beta=14/17`、`qD=8/9-delta` 处，它精确等于 `3lambda delta/17`。
本次 `delta=1/400` 给 `3lambda/6800`。若 forcing 内部损失增加为
`qF=8/9+eta`，则余量精确为 `3lambda(1/400-eta)/17`，允许
`eta<1/400`；等号不能保证矛盾。直接从 `X` 幂次减去的总损失 `ell`
则必须满足 `ell<3lambda/6800`。若所有归一化均以同一个终端 `T` 为尺度，
附加 `T^eta` 损失对应上面的 `eta`；若经过 Cauchy、平方或改变尺度，必须重算，
不能原样套用。旧 `qF` 不变时的纯指数临界点为 `11191/13591<14/17`。

对当前 MWKF/QCT，这只能放宽**已被正确传递到 forcing 下界的幂次误差预算**，
不能修复共同权、gcd 层、varying-level 核或 all-box 重组缺失。例如现有 QCT
账本 (4.8bn)--(4.8bq) 在最坏面的差额为 `751/1000`，远大于本次
`1/400`；即使乐观假设一比一传递，也还差 `1497/2000`。
这两个数的比较不是一个新的 QCT 传递定理。现有 endpoint 绝对界 (4.78)--(4.79)
还有 `2T/(qRS)`、cardinal q 求和及共同核约束，不能靠密度小余量取消。

新增 forcing 接线只去掉 density-certificate 前提；实际 forcing lower count
仍是明确前提。没有因此证明 `Re rho<=14/17` 或 `Re rho<=2/3`。

## 5. 可追溯入口与验收

- 原框架/固定节省：`PrimeNumberTheorem/CarlsonLengthMinimax.lean`。
- 实际两尺度参数与有理指数：`CarlsonTwoThirdsHalfRangeExponent.lean`。
- 闭壳：`CarlsonHalfRangeShellCount.lean`。
- 累计计数及无对数损失求和：`CarlsonClosedCount.lean`、`CarlsonGeometricSummation.lean`。
- 无条件全局定理与证书：`CarlsonHalfRangeDensity.lean`。
- forcing 接线：`SingleLayerForcingHalfRangeDensity.lean`。
- 全推导及按阶段保存的构建证据：`docs/superpowers/specs/2026-08-27-carlson-two-scale-paper-proof.md`。

原始论文仅作为技术来源/比较，不作为替代零密度前提：
[Conrey 1989, Theorem 2](https://aimath.org/~kaur/publications/24.pdf)；
[Guth–Maynard, New large value estimates](https://arxiv.org/abs/2405.20552)。
本次最终证明不依赖尚未在 Lean 中实现的 `theta<4/7` 谱输入。

### 最终验收（2026-08-30）

- 联合构建本分支全部 152 个相关 Test 模块及其依赖：退出码 `0`，`9055 jobs`。
  补登记了此前未列入 Lake roots 的 19 个既有契约，没有排除失败项。
- 对上述 152 个实际构建 trace 汇总：465 条公理报告，仅有 `propext`、
  `Classical.choice`、`Quot.sound`；minimax、固定节省、无条件全局密度、
  certificate constructor 和 forcing 接线的关键声明无缺漏。
- 完整 Python 测试：`547 passed`，无跳过，退出码 `0`。
- 命题分类检查、chain-gap 检查、全项目占位符扫描、`git diff --check` 均退出 `0`。
- 独立只读审查无未解决 Critical/Important/Minor；已修正局部 Gaussian 指数
  与较粗纸面指数的表述。弱 AFE 的 Prop 分类有其实际无前提证明支撑。

确切构建目标、测试命令与范围保存在
[机器可读验收记录](2026-08-30-carlson-half-range-verification.json)。
本次通过的是全部分支相关契约及其依赖，不声称运行了整个仓库的默认 `lake build`
或全部其他路线的公理脚本。所有修改仅保存在隔离分支
`codex/carlson-two-thirds-improvement-20260826`，没有合并、推送或修改其他活动 worktree。
