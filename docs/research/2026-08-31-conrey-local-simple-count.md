# Conrey：先数每个局部区间的真实简单零点，再作有限分块求和

先说结论：此前固定全局 mollifier 的低高度均方缺口，可以通过
局部化零点计数绕开，而不是把未知均方当作已证。
本文结合 companion 的真实 `[T/2,T]` V1 均方、已存在的有限
轮廓与选高定理，推导局部简单零点下界，再得所有大实高度的比例。

**结论层级必须区分：**这完成的是基于已发表 DI/Weil 深输入的
纸面应用链，不是这些深输入的独立重证，也不是原生 Lean 完成。
没有新增一个假设最终均方或最终计数的条件接口。原生目标
`conreyTwoFifthsSimpleZerosTarget` 仍未在本检查点得到无条件 Lean 证明。

本节来源树固定为 `5b1a00fb1f9f97fbced093ded4b4d6f89164ba9e`。
历史文档所列的待办反映当时边界；本节只更新以下局部应用链的数学状态。

## 1. 固定同一函数，选择局部两端

全部参数、实际函数 `B_T,V_T,V_{1,T}`、常数 mathfrak C 沿用
[局部 V1 均方](2026-08-31-conrey-local-v1-mean.md)。另令

\[
 A=2\log L,\qquad
 \eta_T(s)=\frac{49}{100}\xi(s)+\frac{k}{L}\xi'(s)
           =H(s)V_{1,T}(s),\qquad F(s)=V_{1,T}(s)B_T(s).
\]

`xi=H zeta` 是同一原生 completed zeta；在正实部、正高度矩形上
H 解析非零，eta 的零点及阶与 V1 相同。

已有 `exists_conreyHorizontalJensenHeight_weightedLogDeriv_le_coarse`
并不限于全局底边；它对任意单位窗口 `[b,b+1]` 成立，只需
`A+1<=b`、`b+1<=exp L`、`2<=Y<=exp L` 及统一的大 L 门槛。
分别取 `b=T/2` 和 `b=T-1`。充分大 T 时两窗口均合规且不交，得到

\[
 u\in[T/2,T/2+1],\qquad v\in[T-1,T],\qquad
 \ell=v-u=T/2+O(1)>0.
 \tag{local-heights}
\]

在这同一 u,v 上，F 的两条水平边无零，且各自的加权 argument
积分绝对值至多 `1100000000000 L^7`。
这不是套用只对旧底窗口陈述的组合定理，而是对任意窗口的原始
已证定理调用两次。选择不改变 T、L、Y 或任何系数。

## 2. 完整 Littlewood 余项仍为 O(T/L)+O(L^7)

定义全部非左边余项，方向为下边加右边减上边：

\[
 \begin{split}
 B_{\rm edge}={}&-\int_u^v\log|F(A+it)|dt
  +\int_{\sigma_0}^A(x-\sigma_0)\Im(F'/F)(x+iu)dx\\
 &-\int_{\sigma_0}^A(x-\sigma_0)\Im(F'/F)(x+iv)dx
 +(A-\sigma_0)\int_u^v\Re(F'/F)(A+it)dt.
 \end{split}
 \tag{complete-edge-remainder}
\]

已证全局右边结果对任意 `1<=u<=v<=exp L` 有
`Re F(A+it)>=3/10`，右边 argument 积分绝对值至多 pi，且
`int_1^T |log|F(A+it)||dt<=507 T/L`。因此通过非负积分限制到
`[u,v]`，而不是改变 F，得到精确的现成预算

\[
 |B_{\rm edge}|\le B_T^*
 :=507T/L+2200000000000L^7+(A-\sigma_0)\pi.
 \tag{local-edge-budget}
\]

来源分别为 `ConreyExplicitRightVerticalLow`、`ConreyRightArgument`、
`ConreyHorizontalJensenAsymptotic`；同样的代数组合已在
`ConreyEquation37Edges` 写出。它所用的右边限制不要求低底边窗口。
于是 F 的其余三边与所有角点均非零，左边允许零点。

## 3. eta 的三边变幅有正确的局部长度主项

记 E_eta 为 eta 在下边、向上右边、反向上边的 argument 变幅之和。
因为 F 两条水平边非零，V1 在这两边非零。
`exists_conreyV1_horizontalArgument_le_coarse` 在任意合规窗口、
任意无零水平线均成立，因此在已选同一 u,v 上适用；每边误差
仍至多 `1100000000000 L^7`，不需要重新选高。

H 的水平积分由 `conreyH_horizontalArgument_bound` 给出，大小为
`O((1+log L)L)`：其高度基数在两个窗口都至多 `3 exp(2L)`，
故该定理中的 `1+log(heightBase+2)=O(L)`。
V1 右边的 argument 积分至多 pi。
H 右边则有已经证明的精确有限不等式

\[
 \left|\int_u^v\Re\frac{H'}H(A+it)dt
 -\frac12\int_u^v\log\frac{t}{2\pi}dt\right|\le8\ell.
\]

`eta=H V1` 只在这三条无零边上拆开 logarithmic derivative，
各项连续可积；不拆左边的奇异复值积分。合并得

\[
 E_\eta\ge\frac12\int_u^v\log\frac{t}{2\pi}dt
   -8\ell-O(L\log L)-2200000000000L^7-\pi
 =\frac{\ell L}{2}-O(T)-O(L^7).
 \tag{eta-local-main}
\]

最后一步使用同一 `t in [T/2,T]`，故 `log(t/(2pi))=L+O(1)`。
不能误写为 `TL/2`；区间长度 ell 必须保留到计数归一化之后。

## 4. 保留有限轮廓证明实际返回的零点见证

`exists_conreyDegreeOneEta_simpleZero_finset_of_three_edges` 已构造
真实有限集 `S subset (u,v)`，其中每个 t 都满足
`zeta(1/2+it)=0`、解析阶恰为1，且

\[
 \#S\ge E_\eta/\pi-2N_{\eta,\mathrm{full}}-1.
 \tag{local-witness}
\]

这里 N_eta,full 计同一矩形 `[1/2,A] x [u,v]` 上全部 eta 零点
的完整重数。半重数轮廓公式与分量损失已在上游精确合并；
不要换成正跳跃变幅，也不要再减一次临界线重数。

同一矩形上的 H 非零、B 解析，故逐点阶相加，已证的
`conreyEta_zero_mass_le_mollified_bounded_full` 给出
`N_eta,full<=N_F,full`。于是 (local-witness) 中可换为后者。

`ConreyMollifiedContourCount` 的原公开结论随后把 S 放进高度 v
的全局集合，丢掉了定位信息；这里保留它实际已返回的 `S subset (u,v)`。
从未通过两个全局**下界相减**来推断局部下界。

## 5. 对同一选高区间应用 Littlewood 和真实均方

已有 `conreyMollified_boundedFullCount_le_logNorm_edges` 给出

\[
 2\pi(R/L)N_{F,\mathrm{full}}
 \le I_{\log}+B_{\rm edge},\qquad
 I_{\log}=\int_u^v\log|F(\sigma_0+it)|dt.
 \tag{local-Littlewood}
\]

所有函数非平凡且在矩形邻域解析，故左边只有有限个零点。
局部解析因子化使 log 范数可积；零点集合测度为0。
`conreyMollified_logNorm_meanSquare_bounds` 已对此实际 F 证明

\[
 I_2:=\int_u^v|F(\sigma_0+it)|^2dt>0,\qquad
 2I_{\log}\le\ell\log(I_2/\ell).
 \tag{local-Jensen}
\]

这一步没有假设左边处处非零，也不在零点附近声称 log 连续。
代入 (local-witness)、(local-Littlewood) 和完整预算得

\[
 \#S\ge\frac{E_\eta}{\pi}
 -\frac{\ell\log(I_2/\ell)+2B_T^*}{2\pi(R/L)}-1.
 \tag{local-count-finite}
\]

注意右侧整个非左边预算乘2，再除以 `2pi(R/L)`；没有丢失2。

companion 已证明同一 F 的 `[T/2,T]` 均方等于 `mathfrak C+o(1)`。
因为被积函数非负且 `[u,v] subset [T/2,T]`，有

\[
 0<I_2/\ell\le\frac{T/2}{\ell}(\mathfrak C+o(1))
 =\mathfrak C+o(1).
\]

`mathfrak C>=1`，log 在它附近连续且单调，因此可将这一**上界**
插入 (local-count-finite)。无须证明选高所删单位段的均方为 o(T)。
由 (eta-local-main)，`B_T^* L=O(T)+O(L^8)=o(TL)`，得到

\[
 \boxed{\#S\ge\frac{TL}{4\pi}
  \left(1-\frac{\log\mathfrak C}{R}-o(1)\right),\qquad S\subset(T/2,T).}
 \tag{local-simple-count}
\]

误差对实际选出的 u,v 一致；所有输入的窗口常数均绝对，
而均方上界直接来自整个 `[T/2,T]`。这已经是真实简单零点下界，
不是假设一个 counting interface。

## 6. 有限分块先行，得到所有大实数高度

记 `N_s(X)=positiveCriticalLineSimpleZeroCount X`、
`kappa=1-log(mathfrak C)/R`。高度约定为 `0<Im rho<=X`。
局部见证在严格开区间内，故不会因分块公共端点而重复计数。

先固定正整数 J。对 `j=0,...,J-1`，将 (local-simple-count)
应用于 `T_j=X/2^j`，每段选择各自函数及有限见证集 S_j。
所有 S_j 都是真实 zeta 简单零点，并且分别包含在
`(X/2^(j+1),X/2^j)` 中，所以两两不交。于是

\[
 \begin{split}
 N_s(X)&\ge\sum_{j=0}^{J-1}\#S_j,\\
 \liminf_{X\to\infty}\frac{N_s(X)}{X\log X/(2\pi)}
 &\ge\kappa\sum_{j=0}^{J-1}2^{-j-1}
 =\kappa(1-2^{-J}).
 \end{split}
 \tag{finite-dyadic-sum}
\]

理由是 J 固定时每个 T_j 都趋于无穷，有限个 o(1) 一起趋于0，
且 `log(T_j)/log X->1`。不对随 X 增长的无限多个误差求和，
也不需要关于 J 的一致性。最后让 J 趋于无穷，得到 liminf 下界 kappa。
这一论证对全部充分大的实 X 成立，而不是仅在 dyadic 高度子序列上。

若用 eventual 语言：对任意 `0<c<kappa`，先选 J 使
`c<kappa(1-2^(-J))`，再用有限个局部门槛和误差选 X0；
便得到所有 `X>=X0` 的相应下界。`c<=0` 由计数非负直接处理。

最后使用已有 Riemann--von Mangoldt 归一化

\[
 N(X)=\sum_{0<\Im\rho\le X}\operatorname{ord}_\rho\zeta
 \sim X\log X/(2\pi).
\]

具体来源是 `PrimeNumberTheorem/RiemannVonMangoldt/AllHeightAsymptotic.lean`
的 `exists_abs_riemannZeroCount_sub_mainTerm_le_log`，它对所有 X>=8
给出 `|N(X)-M(X)|<=C(1+log(X+6))`，其中
`M(X)=X log(X/(2pi))/(2pi)-X/(2pi)`。除以 `X log X/(2pi)`
就得到这里所需的极限，不再额外假设一个 RVM 比例接口。

若要 `c N(X)<=N_s(X)`，先选严格中间常数 `c<d<kappa`，
用上面的最终下界 d 和 `N(X)/(X log X/(2pi))->1` 吸收误差。
因此每个 `c<kappa` 都有 eventual 真正计数下界。

## 7. 精确数值余量与交付边界

已有 `conreyExplicitMeanSquareIntegral_eq_constant` 将同一个实际
双积分精确展开为

\[
 \mathfrak C=-\frac{7119751197749681}{5935545000000000}
 +\frac{43767545344030157}{148388625000000000}e^{12/5}.
\]

`conreyExplicitMeanSquareIntegral_lt_exp` 已证
`mathfrak C<exp(18/25)`，所以

\[
 \kappa=1-\frac{\log\mathfrak C}{6/5}>1-\frac{18/25}{6/5}=2/5.
\]

选择 `c=(2/5+kappa)/2`，本节纸面应用链给出相同简单零点目标。
这不是改用所有临界线零点或无重数分母。

本节新增的是局部 V1 均方到局部真实见证、再到全局计数的推导。
它与 [Conrey 1989, pp.6--7](https://aimath.org/~kaur/publications/24.pdf)
的重数和微分系数约定一致，但采用已修正的分段变幅与实际有限
见证，保留端点损失1；没有重新使用被反例否定的正跳跃计数。

仍未完成：DI/Weil 深输入的独立重证，新增纸面链的原生 Lean
证明、最终源 SHA 上相应 Lean 验收，以及原生最终目标的组合。
固定全局 mollifier 在 `[0,T]` 的均方依然未证，但已不再是
本条局部计数路线的必需前提。不能把纸面应用链完成写成原生目标完成。

本检查点只新增两篇 Markdown，不改 Lean/Lake/契约或冻结源分支。
轻量验收使用已缓存 Python 环境，命令为
`uv run --offline --no-project --with pytest --with mpmath --with numpy --with python-flint python -m pytest -q`、
`python3 scripts/list-prop-targets.py`、
`python3 scripts/check-chain-gaps.py` 和 `git diff --check`。
这些检查不验证上述数学推导；推导另作独立只读数学审查。
