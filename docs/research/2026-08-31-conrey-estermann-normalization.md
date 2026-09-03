# Conrey 实际 Estermann 变换：从有限 Hurwitz 和固定归一化

本节把上一个检查点的双射线级数推进到实际 Estermann 变换：证明
有理扭转的函数方程、极点主项、常数项与收敛的对偶余项。
先从有限 Hurwitz 和推导，避免把原文印刷公式直接当作定理输入。
本节为纸面证明，未新增或运行 Lean；#500 的冻结源树不变。

核对了 [Conrey 1989, Lemmas 4–5, pp.14–16](https://aimath.org/~kaur/publications/24.pdf)
的完整渲染页。按其所写的 `D` 与 `e(x)=exp(2 pi i x)` 定义，
印刷函数方程的常数及移线后余弦符号与下列精确推导不符。
第8节给出无需数值近似的检验；这不否定论文最终定理。

## 1. 实际函数、固定参数及分支

取整数 `K>=1,H`，满足 `gcd(H,K)=1`，并取整数 `Hbar` 使
`H Hbar=1 mod K`。`K=1` 包含在内，所有模1相位都等于1。
正实数幂用实对数，右半平面复数的幂用主值 `Log`。

在 `Re(s+alpha)>1, Re(s+beta)>1` 内定义实际绝对收敛级数

\[
 D(s,\alpha,\beta;H/K)
 =\sum_{m,n\ge1}m^{-s-\alpha}n^{-s-\beta}e(mnH/K).
 \tag{D-def}
\]

记 `Z(u,a)=sum_(j>=0) (j+a)^(-u)` 为通常 Hurwitz zeta，
初始 `Re u>1, a>0`；使用其实际亚纯延拓。记
`F(u,a)=sum_(n>=1) e(na)n^(-u)`，初始 `Re u>1`。
它们不是本步骤任意选择的代理函数。

为后面的具体移线，固定 `|alpha|,|beta|<=1/4`，`Im x>0`，
令 `z=-2 pi i x`，所以 `Re z>0`，定义

\[
 S(x,\alpha,\beta;H/K)
 =\sum_{m,n\ge1}m^{-\alpha}n^{-\beta}e(mnH/K)e(mnx).
 \tag{S-def}
\]

其绝对收敛可由 `exp(-u)<=C_2 u^(-2)` 应用于
`u=2 pi mn Im x` 后，两份指数至少 `7/4` 的 p 级数得到。

## 2. 有限 Hurwitz 分解及精确极点部分

在 (D-def) 的绝对收敛域内按 `m,n mod K` 分组，直接得到

\[
 D(s,\alpha,\beta;H/K)
 =K^{-2s-\alpha-\beta}
 \sum_{r,t=1}^{K}e(Hrt/K)
 Z(s+\alpha,r/K)Z(s+\beta,t/K).
 \tag{finite-Hurwitz}
\]

右边给出实际亚纯延拓。令 `h_r(u)=Z(u,r/K)-zeta(u)`。
Hurwitz 与 Riemann zeta 在1的极点留数均为1，因此 `h_r` 整函数，
且 `h_K=0`。根单位正交性给出

\[
 \sum_{t=1}^{K}e(Hrt/K)=K\,\mathbf1_{r=K},\qquad
 \sum_{r,t=1}^{K}e(Hrt/K)=K.
\]

把 `Z=zeta+h` 展开，两个一次交叉项均因 `h_K=0` 消失，故

\[
 \boxed{D=K^{1-2s-\alpha-\beta}\zeta(s+\alpha)\zeta(s+\beta)
 +K^{-2s-\alpha-\beta}\sum_{r,t=1}^{K}e(Hrt/K)
 h_r(s+\alpha)h_t(s+\beta).}
 \tag{pole-split}
\]

第二项为整函数。若 `alpha!=beta`，两处留数分别为

\[
 \operatorname*{Res}_{s=1-\alpha}D
 =K^{-1+\alpha-\beta}\zeta(1-\alpha+\beta),\qquad
 \operatorname*{Res}_{s=1-\beta}D
 =K^{-1+\beta-\alpha}\zeta(1-\beta+\alpha).
 \tag{D-residues}
\]

`alpha=beta` 时两极点合为二阶，不能分别代入上述两个无穷值。

## 3. 从一维 Hurwitz 函数方程推导真正 D 函数方程

使用标准且现有 Mathlib 已原生证明的实际一维等式：

\[
 Z(1-u,a)=(2\pi)^{-u}\Gamma(u)
 \{e^{-i\pi u/2}F(u,a)+e^{i\pi u/2}F(u,-a)\}.
 \tag{Hurwitz-FE}
\]

先在 `Re(s+alpha)<0, Re(s+beta)<0` 中推导。
此时代入 `u=1-s-alpha` 或 `1-s-beta` 后，两份 `F` 级数
都绝对收敛，有限和与它们交换没有问题。对 `epsilon,eta` 各取
`+1,-1`，出现的有限相位和是

\[
 \sum_{r,t=1}^{K}e((Hrt+\varepsilon mr+\eta nt)/K)
 =K e(-\varepsilon\eta\bar Hmn/K).
 \tag{finite-phase}
\]

证明先对 `r` 求和；唯一留下的 `t` 满足
`H t+epsilon m=0 mod K`，故 `t=-epsilon Hbar m mod K`。
于是 (finite-Hurwitz) 的共同因子为

\[
 A(s)=K^{1-2s-\alpha-\beta}(2\pi)^{2s+\alpha+\beta-2}
 \Gamma(1-s-\alpha)\Gamma(1-s-\beta).
\]

当 `epsilon=eta` 时，两个指数系数之和为
`-2 cos(pi(2s+alpha+beta)/2)`，对偶扭转为 `-Hbar/K`；
当 `epsilon=-eta` 时，和为 `2 cos(pi(alpha-beta)/2)`，
对偶扭转为 `+Hbar/K`。因此

\[
 \boxed{\begin{aligned}
 D(s,\alpha,\beta;H/K)=2A(s)\bigl[&
 \cos\tfrac\pi2(\alpha-\beta)D(1-s,-\alpha,-\beta;\bar H/K)\\
 &-\cos\tfrac\pi2(2s+\alpha+\beta)
 D(1-s,-\alpha,-\beta;-\bar H/K)\bigr].
 \end{aligned}}
 \tag{D-FE}
\]

这是由两个已有实际一维函数方程和有限正交性推导出的等式。
两边亚纯延拓后仍相等；后续仅用在 `Re s=-1/2`，属于上述
直接绝对收敛推导域，不需在奇点处解释各个 Gamma 因子的单独值。

## 4. 移线所需增长界不是新假设

以下给出固定 `K` 的充分界，暂不追求最终谱估计所需的 K 次数。
对 `a>0`，两次分部积分的 Euler 求和公式给出

\[
 Z(u,a)=\frac{a^{1-u}}{u-1}+\frac12a^{-u}
 +\frac{u}{12}a^{-u-1}
 -\frac{u(u+1)}2\int_0^\infty
 B_2(\{t\})(a+t)^{-u-2}\,dt,
 \tag{Hurwitz-EM}
\]

这里 `B_2(v)=v^2-v+1/6`，`|B_2({t})|<=1/6`。
可先在 `Re u>1` 对每个单位区间分部积分，端点项求和后取上限；
余积分在 `Re u>-1` 局部一致绝对收敛，因而等式亚纯延拓到该域。
其余项绝对值至多

\[
 \frac{|u(u+1)|}{12}
 \frac{a^{-\Re u-1}}{\Re u+1}.
\]

对 `-1/2<=Re s<=2, |alpha|,|beta|<=1/4, |Im s|>=1`，
两份 Hurwitz 参数实部属于 `[-3/4,9/4]`，且远离各自极点1。
(Hurwitz-EM) 与有限和给出真正的统一界

\[
 |D(s,\alpha,\beta;H/K)|\le C_K(1+|\Im s|)^4.
 \tag{D-strip-growth}
\]

`C_K` 可依赖 K，但不依赖此域内移位、实部或高度。

另由 Euler Gamma 积分旋转到角度 `+/-theta` 的射线，有

\[
 |\Gamma(v)|\le \Gamma(\Re v)(\cos\theta)^{-\Re v}
 e^{-\theta|\Im v|}
 \quad(\Re v>0,\ 0<\theta<\pi/2).
 \tag{Gamma-ray}
\]

这是已有 `SelbergGammaRayBound` 的实际旋转估计；不是 Stirling
误差接口。用 `Gamma(s)=Gamma(s+2)/(s(s+1))`，在上述高高度
闭条带上便有 `|Gamma(s)|<=C_theta exp(-theta |Im s|)`。

取 `|arg z|<theta<pi/2`，结合
`|z^(-s)|=|z|^(-Re s) exp(Im s arg z)`，可知
`D(s)Gamma(s)z^(-s)` 的两条水平边一致趋于零，且竖线绝对可积。
故下面的移线不是形式操作。

## 5. 实际 Mellin 积分移线与极点合流

对 `Re z>0`，`exp(-u)` 的 Mellin 反演为

\[
 e^{-mnz}=\frac1{2\pi i}\int_{(2)}\Gamma(w)(mnz)^{-w}\,dw.
\]

第4节的 Gamma 衰减与
`sum m^(-2-Re alpha) sum n^(-2-Re beta)<infinity`
允许交换级数与积分，从而

\[
 S=\frac1{2\pi i}\int_{(2)}D(w,\alpha,\beta;H/K)
 \Gamma(w)z^{-w}\,dw.
 \tag{S-Mellin}
\]

将竖线向左移动到 `Re w=-1/2`。所跨极点恰为
`w=1-alpha, 1-beta` 以及 Gamma 的 `w=0`；后者留数为
实际值 `D(0,alpha,beta;H/K)`。因此

\[
 S=M(\alpha,\beta;K,z)+D(0,\alpha,\beta;H/K)+R,
 \quad R=\frac1{2\pi i}\int_{(-1/2)}D(w)\Gamma(w)z^{-w}\,dw.
 \tag{S-split}
\]

当 `alpha!=beta` 时，

\[
 \begin{aligned}
 M={}&K^{-1+\alpha-\beta}\zeta(1-\alpha+\beta)
       \Gamma(1-\alpha)z^{\alpha-1}\\
 &+K^{-1+\beta-\alpha}\zeta(1-\beta+\alpha)
       \Gamma(1-\beta)z^{\beta-1}.
 \end{aligned}
 \tag{M-off-diagonal}
\]

当 `alpha=beta=a` 时，令 `psi=Gamma'/Gamma`，正确合流值为

\[
 \boxed{M(a,a;K,z)=K^{-1}\Gamma(1-a)z^{a-1}
 [2\gamma_E+\psi(1-a)-2\log K-\operatorname{Log}z].}
 \tag{M-collision}
\]

可直接对 (pole-split) 的二阶极点求留数；亦可令 `beta=a+h`，
利用 `zeta(1+h)=1/h+gamma_E+O(h)` 与
`zeta(1-h)=-1/h+gamma_E+O(h)`。两个 `1/h` 抵消；第二项的
一阶乘子为 `log K+Log z-psi(1-a)`，得到上式。
例如 `a=0` 时为 `(gamma_E-2 log K-Log z)/(Kz)`。

组合主项在合流处可去奇异。固定 `z` 的右半平面紧集时，S、D(0)
及 R 对移位均全纯且有局部一致支配，所以不存在只验证
`alpha!=beta` 后遗留的移位求导漏洞。

## 6. 对偶余项：常数和余弦移位各自保留

在 R 中令 `w=1-s`，路径方向反转与 `dw=-ds` 抵消；所得竖线
`Re s=3/2` 仍向上。代入 (D-FE) 并使用

\[
 \cos\tfrac\pi2(2-2s+\alpha+\beta)
 =-\cos\tfrac\pi2(2s-\alpha-\beta),
\]

可得精确余项

\[
 \boxed{\begin{aligned}
 R={1\over\pi i}\int_{(3/2)}&z^{s-1}
 K^{2s-1-\alpha-\beta}(2\pi)^{\alpha+\beta-2s}
 \Gamma(1-s)\Gamma(s-\alpha)\Gamma(s-\beta)\\
 {}\times\bigl[&\cos\tfrac\pi2(2s-\alpha-\beta)
 D(s,-\alpha,-\beta;-\bar H/K)\\
 &+\cos\tfrac\pi2(\alpha-\beta)
 D(s,-\alpha,-\beta;\bar H/K)\bigr],ds.
 \end{aligned}}
 \tag{R-dual}
\]

把 K 和 `2 pi` 的幂分开写，是为了不藏掉归一化因子。如果合并为
`(K/(2 pi))^(2s-1-alpha-beta)`，积分外因子应为
`1/(2 pi^2 i)`，不是 `1/(pi i)`。

这里两份对偶 D 都是绝对收敛级数，并且范数至多
`zeta(3/2-Re alpha) zeta(3/2-Re beta)<=zeta(5/4)^2`。
三个 Gamma 可用 (Gamma-ray) 和递推式处理；第一个余弦的范数
至多一个固定移位因子乘 `exp(pi |Im s|)`。
选 `(pi+|arg z|)/3<theta<pi/2`，便使两项各自绝对可积。
因此 (R-dual) 不依赖两项之间未证明的相消。

还可直接得出真实但仅在固定闭角域内使用的界：对
`0<delta<=pi/2, |arg z|<=pi/2-delta`，存在 `C_delta`，使

\[
 |R|\le C_\delta K^{2-\Re\alpha-\Re\beta}|z|^{1/2}
 \quad(|\alpha|,|\beta|\le1/4).
 \tag{R-sector-bound}
\]

它来自上述三 Gamma 的可积上界，常数不依赖 K、H、z 或允许范围内
的移位，但可随 `delta->0` 变坏。这不是 DI 所需的长均方误差界。

## 7. 与已有双射线级数的准确连接

在上一份 [双射线求和证明](2026-08-31-conrey-gaussian-ray-summation.md)
中，令 `r_0=h_0/k_0=H/K>0` 为约分后的比值，
`gamma=alpha+beta` 是那份文档的合并移位。正、负相位分别满足

\[
 \begin{aligned}
 \sum_{m,n\ge1}m^{-\gamma}e(mnr_0v)
 &=S(r_0(v-1),\gamma,0;H/K),&&v\in L_{+\phi},\\
 \sum_{m,n\ge1}m^{-\gamma}e(-mnr_0v)
 &=S(-r_0(v-1),\gamma,0;-H/K),&&v\in L_{-\phi}.
 \end{aligned}
 \tag{ray-S-match}
\]

两者的 x 都在上半平面。负相位不但要改变 x，也必须改变有理扭转
的符号；否则多出 `e(2mnH/K)`。应用本节变换时需
`|gamma|<=1/4`；它由真实移位足够小得到，不能从
`|alpha|,|beta|<=1/4` 自动推出。

此处只取得每个射线点上的实际分解。将全部 M、D(0)、R 分别积分
回外层 Gaussian 时，还须给出对整条射线的支配：例如
`arg(-2 pi i r_0(v-1))` 在 `v->0` 时接近右半平面边界，
不能把固定 delta 的 (R-sector-bound) 当作全射线统一常数。

## 8. 印刷公式的精确回归检验

以下均基于原文自己的 D 和相位定义，不是改变其归一化：

1. **K=1 的常数检验。** 取 `alpha=beta=0, s=-1/2`，
   `D(s)=zeta(s)^2`。Riemann 函数方程给出
   `zeta(-1/2)^2=zeta(3/2)^2/(16 pi^2)>0`。
   第15页印刷前因子 `-2(K/(2 pi))^(1-2s-alpha-beta)`
   则给出 `zeta(3/2)^2/(8 pi)`，正好多 `2 pi`。
   (D-FE) 的实际前因子通过此检验。
2. **移线余弦检验。** 在对偶变量 `s=3/2` 处，取
   `alpha=1/8,beta=0`。应有
   `cos(pi(2s-alpha-beta)/2)=-sin(pi/16)`，而第16页
   所印 `cos(pi(2s+alpha+beta)/2)=+sin(pi/16)`。
   即使先纠正共同常数，这两者仍不同。`K=1` 时对应 D 非零。
3. **负相位扭转检验。** 按第15页 S 定义，第18页式(57) 若沿用
   所印的末参数 `+h/k`，则与目标负相位相差 `e(2mn h/k)`。
   取 `h=1,k=3,m=n=1` 即得非平凡差异。应按 (ray-S-match)
   的负扭转对接，不能靠 `K=1` 特例掩盖它。

这些检查固定的是本项目后续实现应采用的实际公式。不能据此说
论文的主结果错误；也不能未经检查断言所有后续印刷式均已修正。

## 9. 原生化与最终定理仍缺的工作

实际可复用的一维原生输入是
`Mathlib/NumberTheory/LSeries/HurwitzZeta.lean` 中
`HurwitzZeta.hurwitzZeta_one_sub`、`hasSum_expZeta_of_one_lt_re`，
以及 `HardyTheorem/SelbergGammaRayBound.lean` 的 Gamma 旋转估计。
有限正交性、D 的有限 Hurwitz 组装、条带支配、Mellin 移线和极点
合流尚需逐步写成 Lean；本节不将它们作为已验证实现。

更重要的后续数学任务是：整条 Gaussian 射线上的 M、常数项、R
可积性及评价；小移位下 `D(0,alpha,beta;H/K)` 的正确统一 K 界；
对偶双和的实际核估计与 DI 谱估计；以及完整均方、去平滑和简单
零点计数。`R-sector-bound` 不能替代其中任一步。
