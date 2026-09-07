# 差频的全部消失矩、原函数判据与系数层面的 3/4 门槛

实际薄带核在对角附近为零，这使它的差频变换具有**全部多项式消失矩**。
因此先取绝对值确实丢掉了结构。本次把可以利用的结构写成一个精确原函数
判据，并进一步证明：若把这个判据加强成全局、系数相容的平方平均原函数，
那么它在 `σ ≤ 3/4` 已经失败。这个门槛不是 ζ 零点界，也不是实际薄带和
的反例；它告诉我们不能用过强的全局原函数假设替代所需的局部耦合估计。

状态：数学研究记录。没有证明 eventual/global `14/17` 或 `2/3`，没有改 Lean。
承接 [同零点径向隔离](2026-08-30-same-zero-radial-isolation.md) 和
[互素 Euler 乘积](2026-08-30-primitive-euler-zero-response.md)。本轮还重新检查了
`audit-mwkf-exact-20260824` 的既有密度与负矩讨论；不将零点计数当作留数权界。

## 1. 保留实际核，改用和频与差频

沿用非负 `U,V ∈ C_c^∞((1,2))` 及非零偶函数
`k ∈ C_c^∞({32 < |z| < 64})`，定义

\[
 B_\delta(x,y)=yU(x)V(y)k((x-y)y/\delta),\qquad \delta=X^{-1/3}.
 \tag{1}
\]

允许上一笔记的任意**固定**径向多项式过滤 `P(-E)`，其中
`E=x∂_x+y∂_y`；`P` 的次数与系数进入常数，不声称对增长窗口一致。
记

\[
 K_{\sigma,\omega,\delta}(t)
 =P(2\sigma+i\omega)\mathcal B_\delta
 (\sigma+i(\omega/2+t),\sigma+i(\omega/2-t)). \tag{2}
\]

令 `p=(log x+log y)/2, d=log(x/y)`。对数坐标 Jacobian 的绝对值为 1，故

\[
 K(t)=\int_{\mathbb R} f_{\sigma,\omega,\delta}(d)e^{itd}\,dd,
 \quad f(d)=P(2\sigma+i\omega)\int_{\mathbb R}
 e^{(2\sigma+i\omega)p}B_\delta(e^{p+d/2},e^{p-d/2})\,dp. \tag{3}
\]

这没有改变整数权，也没有把 `U(r/X)` 冻结为 `U(s/X)`。
在原支撑内 `1<x,y<2`。中值定理给出

\[
 8\delta<|d|<64\delta. \tag{4}
\]

因为 `32δ < |x-y|y < 64δ`，而 `d=(x-y)/ξ, 1<ξ<2`。
因此 `f` 在 `d=0` 的一个邻域恒为零。
按 (3) 的 Fourier 归一化直接反演，对每个整数 `j≥0`，

\[
 \boxed{\int_{\mathbb R}t^jK(t)\,dt=2\pi i^j f^{(j)}(0)=0.} \tag{5}
\]

这里是收敛的 Schwartz 积分，不是把发散振荡积分当普通积分。
与 [DLMF 的 Fourier/分布约定](https://dlmf.nist.gov/1.16) 相比，本文已在 (3)
显式指定正号及无归一化的正变换，避免混用 `2π`。

还需要定量版本。对 `σ` 在固定紧集内及固定 `j,N,M`，

\[
 |\partial_t^jK(t)|\ll_{j,N,M,P}
 \delta^{j+1}(1+|\omega|)^{-N}(1+\delta|t|)^{-M}. \tag{6}
\]

证明：在 (3) 中置 `d=δa`，则 `a` 位于固定紧集；对 `t` 求导提供
`(iδa)^j`，`dd` 提供 `δ`。相位为 `ωp+δta`。
在这些变量中
`z=e^{2p}(1-e^{-δa})/δ` 的每个固定阶 `p,a` 导数一致有界；对两变量分部
积分，再吸收固定多项式 `P(2σ+iω)` 即得 (6)。所有边界项为零。
特别地，任意固定 `θ≥0` 有

\[
 \int (1+|t|)^\theta|K'(t)|\,dt
 \ll_{\theta,N,P}\delta^{1-\theta}(1+|\omega|)^{-N}.
 \tag{7}
\]

## 2. 一个真正保留符号的充分判据

定义

\[
 F_{\sigma,\omega,\gamma}(t)
 =D(\sigma+i(\gamma+\omega/2+t),
     \sigma+i(\gamma+\omega/2-t)). \tag{8}
\]

假设在所讨论的竖线上这个函数可按以下方式处理：存在常数 `C_ω` 和局部
绝对连续原函数 `G_ω`，使 `F-C_ω=G_ω'` 几乎处处，且

\[
 |G_\omega(t)|\le A(\omega)(1+|t|)^\theta,
 \quad \int A(\omega)(1+|\omega|)^{-N}\,d\omega<\infty. \tag{9}
\]

这是**待证的解析输入**；不能在穿过 ζ 零点的竖线上默认存在，也不能用
下面的形式级数定义来证明它。(5)、分部积分及 (7) 严格给出

\[
 \int F(t)K(t)\,dt=-\int G_\omega(t)K'(t)\,dt,
 \quad
 |\mathcal V_\sigma(X)|\ll X^{2\sigma}\delta^{1-\theta}. \tag{10}
\]

其中

\[
 \mathcal V_\sigma(X)=\frac{X^{2\sigma}}{(2\pi)^2}
 \int X^{i\omega}\int F_{\sigma,\omega,\gamma}(t)K(t)\,dt\,d\omega.
 \tag{11}
\]

(10)–(11) 的内层积分按 `lim_{R→∞}∫_{-R}^R` 定义，或等价地按
`G_ω'+C_ω` 与 Schwartz 核的分布配对定义，再作外层 `ω` 积分。
(9) 保证分部积分后的 `∫G_ω K'` 绝对收敛及边界趋零；它本身不保证
`∫|F K|` 有限，故这里不额外声称双重绝对收敛或任意截断次序可换。

`t_1=ω/2+t,t_2=ω/2-t` 的 Jacobian 绝对值同样是 1。
在 `σ>1`，(11) 是原扭曲有限权和的 Mellin 反演；在 `σ≤1`，它只定义
相应竖线积分，**不是已完成的移线恒等式**。
`σ=2/3` 时 (10) 的幂次是 `X^(1+θ/3)`：有界原函数 `θ=0` 才恢复缺少
的完整 `X^(-1/3)`，任何固定正 `θ` 都留下幂次亏损。
若 (9) 额外带 `X^ε`，则结论同样带 `X^ε`，不能删掉。

在绝对收敛区确实可实现 `θ=0,C_ω=1`。因为

\[
 F(t)=1+\sum_{\substack{r\ne s\\(r,s)=1}}
 a_{r,s}e^{-it\lambda_{r,s}},\quad
 a_{r,s}=\mu(r)\mu(s)(rs)^{-\sigma-i(\gamma+\omega/2)},\quad
 \lambda_{r,s}=\log(r/s), \tag{12}
\]

并且 `∑|a_rs|/|λ_rs|<∞` 对 `σ>1` 成立。近对角令 `r=s+w≤2s`，用
`1/log(1+w/s)≤2s/w`，上界归结为 `∑s s^(1-2σ)log(2s)`；远离对角
的部分由 `ζ(σ)^2` 控制。故逐项原函数一致收敛且有界。
这只在已知绝对收敛区恢复薄带计数尺度，没有将 `σ` 推到 `2/3`。

## 3. 系数层面的原函数：精确 3/4 阈值

这一节把对象明确限制为系数空间，不默认它在 `1/2<σ≤1` 等于 (8)。
对有限指数和定义

\[
 \|Q\|_{B^2}^2=\lim_{L\to\infty}\frac1{2L}
 \int_{-L}^L|Q(t)|^2\,dt.
 \tag{13}
\]

不同实频率正交：交叉项平均为 `sin(L(λ-λ'))/(L(λ-λ'))→0`。
因此把有限指数和按这个范数完备化，等同于其频率系数的 `ℓ²` 空间。
这是本文需要的全部 `B²` 结构；不需要关于实际 ζ 竖线值的识别定理。
相关一般框架见 [Sepulcre–Vidal 的 B² 讨论](https://arxiv.org/abs/1711.04122)。

互素条件很关键：`r/s=r'/s'` 且两对均既约，便有 `(r,s)=(r',s')`。
频率零只来自 `(1,1)`，而非任意 `r=s`。
对 `σ>1/2`，(12) 的非零系数属于 `ℓ²`，因为

\[
 \sum_{(r,s)=1}|a_{r,s}|^2
 =\prod_p(1+2p^{-2\sigma})<\infty. \tag{14}
\]

**命题。** 对 `σ>1/2`，(12) 的零均值形式级数有系数相容的 `B²` 原函数
（即原函数在频率 `λ≠0` 上的系数是 `a_λ/(-iλ)`），当且仅当 `σ>3/4`。

等价地，

\[
 \boxed{\sum_{\substack{r\ne s\\(r,s)=1}}
 \frac{\mu(r)^2\mu(s)^2}{(rs)^{2\sigma}\log^2(r/s)}<\infty
 \quad\Longleftrightarrow\quad\sigma>\frac34.} \tag{15}
\]

**充分性。** 利用对称性取 `r>s`。若 `r≥2s`，分母 `log²(r/s)` 有固定正
下界，平方系数可和。若 `r=s+w<2s`，则

\[
 \frac1{(rs)^{2\sigma}\log^2(r/s)}
 \le4\,s^{2-4\sigma}w^{-2}.
 \tag{16}
\]

对 `w` 求和有界，再对 `s` 求和，收敛的充要幂次条件为 `2-4σ<-1`。

**必要性，包括端点。** 只留 `r=s+1`。它们自动互素。
同时平方自由的相邻整数具有足够的正密度；这里给出所需的初等下界，
不调用 Möbius 符号相关猜想。记

\[
 S_*:=\frac14+\frac19+\frac1{25}+\frac1{49}+\frac1{14}<\frac12,
 \qquad c_*:=1-2S_*>0.
 \tag{17}
\]

因为除 `2,3,5` 外的素数包含于 `7,9,11,…`，而递减积分比较给出
`∑_{j≥0}(7+2j)^(-2)≤1/49+1/14`，所以 `∑_p p^(-2)≤S_*`。
取正整数 `Y`。在整数区间 `Y≤s<2Y`，若 `s` 或 `s+1` 不平方自由，某个
`p≤√(2Y+1)` 的平方整除其中之一。并集界给出坏点数不超过
`2Y S_*+2√(2Y+1)`。故至少

\[
 c_*Y-2\sqrt{2Y+1} \tag{18}
\]

个相邻对同时平方自由，对充分大 `Y` 是固定正比例。
在这些点，`log(1+1/s)≤1/s`，所以 (15) 每个二进区间贡献
`≫_σ Y^(3-4σ)`。`σ<3/4` 时不趋零，`σ=3/4` 时各区间均有固定正贡献。
必要性得证。共同高度扭曲只改变单位复相位，因此不改变 (15)。

这个证明也给出有限尺度检查：仅取 `Y≤s<2Y,r=s+1` 的原函数，

\[
 \|G_Y\|_{B^2}\asymp_\sigma Y^{3/2-2\sigma}. \tag{19}
\]

在 `σ=2/3` 是 `Y^(1/6)`，在 `σ=3/4` 是常数量级。**没有**由此推出
实际 `D` 在 `σ≤1` 的点态原函数必定如此；形式系数与竖线值的识别未证。
即使存在某个有界原函数，也只有在它满足此处系数相容性时才与 (15) 矛盾。
这里也可用平移群生成元定义抽象原函数：生成元在频率 `λ` 上乘 `-iλ`。
`B²` 等价类本身不能直接与 (3) 的 Schwartz 核作普通积分；应用 (10)
仍需另行给出实际函数或分布代表的识别。`θ=0` 只达到 `X` 幂次，不自动
给出任何额外的对数节省。

同一证明还说明，对每个固定整数 `j≥1`，系数相容的 `j` 阶 `B²` 原函数
存在当且仅当 `σ>j/2+1/4`：近对角平方系数为
`O(s^(2j-4σ)w^(-2j))`，相邻平方自由对给出匹配下界。
因此 (5) 的全部消失矩不意味着可以免费反复分部积分获得任意幂次。

## 4. 为什么这不是实际薄带的反例

(15) 的坏贡献来自 `r=s+1`，但 (1) 在 `r,s≈X` 时选择的是
`|r-s|≈δX=X^(2/3)`，相邻对根本不在支撑内。
因此不能把 `3/4` 门槛解释成原研究目标的不可能性。

令 `A_X` 为 `X≤r,s≤2X` 且 `cδ≤|log(r/s)|≤Cδ` 的任意子集，其中
`0<c<C` 固定。若 `δX≥1`，其点数 `O(δX²)`。有限原函数满足

\[
 \|G_{A_X}\|_{B^2}^2
 =\sum_{A_X,(r,s)=1}\frac{\mu(r)^2\mu(s)^2}
 {(rs)^{2\sigma}\log^2(r/s)}
 \ll X^{2-4\sigma}\delta^{-1}. \tag{20}
\]

在 `σ=2/3,δ=X^(-1/3)`，右侧是 `X^(-1/3)`，范数上界反而为 `X^(-1/6)`。
但 (13) 的极限是 `L→∞` 后才去掉交叉项；实际核仅给 `|t|≈δ^(-1)`。
不能在这个短得多的窗口上免费使用 (20)。

精确的有限高度 Gram 矩阵为

\[
 \frac1{2L}\int_{-L}^L\left|\sum_j b_j e^{-it\lambda_j}\right|^2dt
 =\sum_{j,k}b_j\overline{b_k}\,
 \operatorname{sinc}(L(\lambda_j-\lambda_k)),\quad
 \operatorname{sinc}(v)=\frac{\sin v}{v},\quad\operatorname{sinc}(0)=1.
 \tag{21}
\]

例如 `N` 个互异频率位于宽 `1/(10L)` 的区间，系数全为 1，则右侧
`≥cos(1/10)N²`；无限平均仅为 `N`。这是**合成系数反例**，只反驳
“有限窗可直接用无限平均 Parseval”，不反驳实际 Möbius 消去。
实际既约分数频率很多且能很接近；单凭互异性没有有限高度正交性。

进一步，先按径向尺度删系数，再应用固定 `ω` 的全局判据也是不同操作。
(11) 的 `ω` 积分及 `X^(iω)` 必须保留；不能声称 (20) 已经处理实际
`U,V,k` 的完整耦合。本次留下的具体目标，是控制 (21) 中真实符号及
径向权共同参与的非对角项，而非再次计算无权频率个数。

## 5. 同时尝试簇轮廓：能去掉小间隔分母，但不能只靠计数

对解析函数 `A`，两个近零点的合并留数有精确模型

\[
 \operatorname{Res}_{z=\varepsilon}\frac{A(z)}{z^2-\varepsilon^2}
 +\operatorname{Res}_{z=-\varepsilon}\frac{A(z)}{z^2-\varepsilon^2}
 =\frac{A(\varepsilon)-A(-\varepsilon)}{2\varepsilon}
 \longrightarrow A'(0). \tag{22}
\]

`ε>0` 时右侧等于 `(1/2)∫_{-1}^1 A'(εv)dv`，因此合并后不需要逐项
支付 `1/ε`。双变量的两个这样的簇给混合差商，并由相应的混合导数
控制。这说明“零点太近，所以只能取每个巨大留数的绝对值”不是必然。

然而对实际 ζ，簇外轮廓 `Γ` 上仍有

\[
 \left|\frac1{2\pi i}\oint_\Gamma\frac{A(z)}{\zeta(z)}dz\right|
 \le\frac{\operatorname{length}(\Gamma)}{2\pi}
 \frac{\sup_\Gamma|A|}{\inf_\Gamma|\zeta|}. \tag{23}
\]

零点个数不提供最后这个下界。即使零点位置固定，解析模型的非零乘子
也能改变它；该观察不是对 ζ 本身的反例，而是说明计数信息缺少解析幅度。
因此本轮没有从零点密度推出加权留数和或负矩界。作为文献边界，
[Bui–Florea–Milinovich](https://arxiv.org/abs/2310.03949) 的负离散导数矩
结果本身含条件且针对子族，本文没有将其导入为无条件补丁。

## 6. 本轮结论与验证范围

已证明的是 (5)–(7) 的实际核消失矩及导数范数、(10) 的条件判据、
(15) 的精确系数空间阈值，以及 (20)–(23) 的有限窗/簇区分。
这缩小了有效尝试范围：保留实际差频窗口和径向振荡，不能用全局、系数
相容的 `B²` 原函数替代局部估计，也不能用无限高度平方平均代替短窗平方平均。

尚未证明 (9) 的可用局部替代、(21) 的实际耦合符号节省、合法移线的
全部剩余边，以及扭曲探测器与原 AFE/QCT 估计的完整连接。
故先前的正指数账本仍不是高高度零点定理。

有限检查脚本为 `scripts/check_difference_frequency_primitive.py`。
它只检查归一化、有限整数/有理数计数、幂次、有限指数和 Gram 恒等式
及簇差商；不数值认证无穷级数阈值，更不认证零点排除。

### English summary

The actual punctured thin-diagonal kernel has all difference-frequency
moments equal to zero. A bounded-primitive input would recover its full
width factor, but the coefficient-compatible Besicovitch-square primitive
of the coprime two-Möbius series exists precisely for sigma greater than
3/4. This statement is about the coefficient completion, not an identification
with the meromorphically continued zeta quotient. Adjacent squarefree pairs
prove the sharp threshold. The actual annular shift window excludes those
pairs; its favorable infinite-height norm cannot be transferred to the
short Mellin window without controlling the finite Gram off-diagonal.
Cluster residues remove inverse-gap artifacts but still need analytic
boundary control. No zero-free half-plane theorem is established.
