# Conrey 真实 Gaussian 移位积分：支配、求导及同一 mollifier 的识别

本节补齐原长均方审计中尚缺的一个解析步骤：真实积分在固定复移位邻域
上存在统一的可积支配，因此可以把所选的一阶微分算子移进积分，并在
负移位处得到原计数路线使用的实际 mollified 均方。这里不假设任意
“解析代理函数”，也不把均方主项或谱估计作为本步骤的输入。

这是数学证明检查点，尚未新增 Lean 实现。当前资源窗口留给既有集成
验收，有限轮廓契约也仍待执行；#500 源 SHA `47c92840` 保持冻结。

原始公式核对了 [Conrey 1989, Section 5, pp.11–12](https://aimath.org/~kaur/publications/24.pdf)
的完整渲染页面，特别区分 `mathcal B(s)` 与带平移权的 `B(s)`。
原文的均方评价不作为下面有限参数解析恒等式的前提。

## 1. 固定有限参数及实际函数

固定 `L>=16, Delta>0, Y>=2`（`Y` 为整数），以及两个实值 profile
`P_1,P_2`。本步骤只需要它们在有限取值点的值，应用取既定多项式。
定义

\[
 c_j(n)=\mu(n)P_j\!\left(\frac{\log(Y/n)}{\log Y}\right),\qquad
 \mathcal B_j(s)=\sum_{1\le n\le Y}c_j(n)n^{-s},\qquad
 A_j=\sum_{1\le n\le Y}|c_j(n)|n^{-1/2}.
\]

所有幂都用正实数底数的实对数。有限和无收敛问题，且
`|mathcal B_j(1/2+it)|<=A_j` 于全部实数 `t`。
在当前源码中 `mathcal B_j=conreyMollifier Y (1/2) P_j`。
这里的整数 `Y` 和 `log Y` 完全匹配源码，不声称等于原文中任意实数
`y=T^theta` 所给的同一 profile 归一化；该改动的渐近控制仍需另证。

取任意实数 `w`，令 `s(t)=1/2+it`，定义实际函数

\[
 g(a,b,w)=\frac1{\Delta\sqrt\pi}\int_{\mathbb R}
 e^{-(t-w)^2/\Delta^2}
 \zeta(s(t)+a/L)\zeta(1-s(t)+b/L)
 \mathcal B_1(s(t))\mathcal B_2(1-s(t))\,dt.
 \tag{G-def}
\]

这正是向上竖线的 `ds/(i Delta sqrt(pi))` 参数化，`ds=i dt`。
不存在 `1/(2pi)` 因子。参数域取开双圆盘 `|a|<3, |b|<3`；
其中包含后续正负中心 `+/-6/5`、外半径 `21/40` 的闭双圆盘。
积分中两份 `mathcal B` 均与 `a,b` 无关。

## 2. 从已有实际 ζ 增长定理得到全高度导数界

源码 `ZeroFreeRegion.exists_norm_riemannZeta_le_polynomial_on_zero_four`
原生证明：当 `0<=Re z<=4, |Im z|>=1` 时，存在绝对常数使
`|zeta(z)|<=C(|Im z|+3)^4`。为覆盖本积分的低高度，取紧矩形

\[
 1/8\le\Re z\le7/8,\qquad |\Im z|\le1.
\]

它避开唯一极点1；实际 ζ 的连续性给出固定范数上界。扩大 `C>=1` 后
可得同一个不依赖 `L,Y,a,b,w,Delta` 的常数，满足

\[
 |\zeta(z)|\le C(|\Im z|+3)^4
 \quad(1/8\le\Re z\le7/8,
       \ \Im z\in\mathbb R).
\]

对于 `1/4<=Re z<=3/4`，半径 `1/8` 的 Cauchy 圆盘仍在这个大条带中，
避开极点，且圆上 `|Im xi|+3<=|Im z|+4`。由 Cauchy 估计，

\[
 |\zeta^{(j)}(z)|\le j!8^j C(|\Im z|+4)^4,
 \qquad j\ge0.
 \tag{Z-deriv}
\]

本任务只需要 `j=0,1`。在 (G-def) 的整个参数域中，两个 ζ 自变量的
实部位于 `(5/16,11/16)`，虚部绝对值至多 `|t|+3/16`。
故 (Z-deriv) 适用，右侧可统一替换为 `j!8^j C(|t|+5)^4`。
这一段明确处理 `t=0` 与两个方向的无限尾，不借助仅在高处成立的界。

## 3. 真实可积支配与复参数求导

还可以在所有 `w` 属于任意固定非空有界闭区间 `I=[w0,w1]`
（`w0<=w1`）上同时支配。
记 `d_I(t)=dist(t,I)`，则 `|t-w|>=d_I(t)`。将 (G-def) 中包括
`1/(Delta sqrt(pi))` 的被积函数记为 `F(a,b,w,t)`。对 `i,j` 属于
`{0,1}`，直接链式求导及上一节的界给出

\[
 |\partial_a^i\partial_b^jF(a,b,w,t)|
 \le \left(\frac8L\right)^{i+j}
 \frac{C^2A_1A_2}{\Delta\sqrt\pi}
 (|t|+5)^8 e^{-d_I(t)^2/\Delta^2}.
 \tag{Dom}
\]

因为 `L>=16`，省去 `(8/L)^(i+j)<=1` 后是一份共同的非负支配函数。
它在紧区间 `I` 上有界；在左右两尾，令 `x` 为距对应端点的非负距离，
便被一个固定八次多项式乘 `exp(-x^2/Delta^2)` 控制，故可积。
即使某个 `A_j=0`，实际被积函数也是零，不需除以这些量。

对每个 `t`，被积函数关于两个复移位分别解析，关于 `t,w` 连续。
用 (Dom) 先对 `a` 应用支配求导定理，再对所得积分关于 `b` 应用同一定理，
得到真正的混合导数恒等式

\[
 \partial_a^i\partial_b^j g(a,b,w)
 =\frac1{L^{i+j}\Delta\sqrt\pi}\int_{\mathbb R}
 e^{-(t-w)^2/\Delta^2}
 \zeta^{(i)}(s(t)+a/L)\zeta^{(j)}(1-s(t)+b/L)
 \mathcal B_1(s(t))\mathcal B_2(1-s(t))\,dt,
 \quad i,j\in\{0,1\}.
 \tag{D-real}
\]

各被积函数的绝对可积性在换序前已经证明。支配收敛也给出参数的联合
连续性；积分关于每个复参数分别全纯，后续迭代使用一变量 Cauchy 公式
即足够，无需引入一个仅声明联合全纯的额外接口。

这里的支配函数允许依赖固定的 `Y,Delta,I`；例如 `I=[T,2T]` 时它随
`T` 变化。这只用于真实积分的存在和求导，**不**给出关于 `T` 的均方
主项、`o(1)` 误差或任何谱消去。不能将此固定参数支配用于未经证明的
`T->infinity` 积分换极限。

## 4. 同一实际 mollifier 的均方恒等式

现在令 `P_1=P_2=P` 为实际选定的实系数多项式，`k=51/50`、`R=6/5`、
`sigma0=1/2-R/L`。由 `Q(z)=1-kz`，真正作用的算子为
`Q(-partial_a)=1+k partial_a`，符号是加号。于是 (D-real) 给出

\[
 [(1+k\partial_a)(1+k\partial_b)g(a,b,w)]_{a=b=-R}
 =\frac1{\Delta\sqrt\pi}\int_{\mathbb R}e^{-(t-w)^2/\Delta^2}
 \left|\bigl(\zeta(\sigma_0+it)+(k/L)\zeta'(\sigma_0+it)\bigr)
              \mathcal B(1/2+it)\right|^2\,dt.
 \tag{MS}
\]

这里使用 ζ 及其导数的共轭对称性，还有有限多项式实系数的共轭对称性。
求导时不能把 `b` 设置成 `conj a`：先保留两个独立复变量完成 (D-real)，
最后才在两个相同的实数移位处识别模平方。

由正底数幂的精确消去，对所有实数 `t`，

\[
 B_{Y,\sigma_0,P}(\sigma_0+it)
 =\sum_{1\le n\le Y}c(n)n^{\sigma_0-1/2}n^{-(\sigma_0+it)}
 =\mathcal B(1/2+it).
\]

故 (MS) 右侧正是源码
`conreyExplicitV L (sigma0+it) * conreyMollifier Y sigma0 P (sigma0+it)`
的 Gaussian 模平方积分。`P`、`Y`、`sigma0` 均固定；微分不会落到
`P`、截断或 mollifier 的 `n^(sigma0-1/2)` 上。
这一恒等式无任何均方假设，覆盖全部实数 `t`，不仅仅是 `[T,2T]`。

## 5. 接到现有误差审计时究竟还缺什么

原来的误差审计要求真实 `E_T=g-G` 在固定复双圆盘上满足一致加性
误差 `sup|E_T|<=e_T->0`。现在数学上已补齐其中 `g` 的实际解析性和
(MS) 的识别。主项 `G` 由有限区间上的多项式/指数积分给出，因此全纯。
在半径 `1/2` 的两个 Cauchy 圆上，若日后证明这个实际误差界，则

\[
 |[(1+k\partial_a)(1+k\partial_b)E_T]_{a=b=-R}|
 \le (1+2k)^2 e_T=(5776/625)e_T.
\]

这不是本轮新加的条件接口，也不是对 `e_T->0` 的证明；它只是定位
下一缺口：实际 Gaussian/Estermann 分解、DI/Weil 非零模式估计、算术
主项、去平滑及实数/整数截断归一化仍须完成。尤其不能拿已证明的
数值 envelope 来替代真实 `g-G`。

## 6. 原生形式化入口及当前状态

- 固定条带高处 ζ 界：
  `ZeroFreeRegion/PhragmenLindelofZeta.lean` 中上述现有定理。
- 低处紧致性：使用实际 `differentiableAt_riemannZeta`，条带排除1。
- Cauchy 导数界：可复用 `ConreyHorizontalJensenGrowth` 中已验证的
  小圆估计模式，但不能复用只覆盖高处 Jensen 圆盘的结论本身。
- 支配求导：Mathlib 的
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`，其底层域可取 `Complex`。
- Gaussian 多项式可积性：Mathlib 的
  `integrable_rpow_mul_exp_neg_mul_sq` 配合两尾平移。
- 实际 ζ 共轭：Mathlib `riemannZeta_conj`；导数共轭由该恒等式求导。
- 同一 mollifier：`ConreyMollifierProduct` 的有限和展开；实际 V 已定义于
  `ConreyV1Approximation`，不另定义一个不相关的目标函数。

本轮尚未运行新 Lean 构建，不声称以上新解析步骤已经内核核验。
独立只读数学审查完整核对原文第11–12页及上述实际源码定义，未发现
待修项：包括固定 ζ 界、共同支配、混合求导、Gaussian 归一化、
同一 mollifier 识别、复双圆盘及固定参数/渐近统一性的边界。
距中心区间的支配明确要求 `w0<=w1`，以排除空集距离的歧义。
本检查点只新增数学文档；未执行的新有限轮廓契约不纳入已通过结果。
