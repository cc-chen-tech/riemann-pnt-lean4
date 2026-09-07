# Conrey 实际对偶核：绝对 Fubini 与所需的加权积分界

本节处理 #512 之后仍保留的实际对偶积分。先证明整条射线上的
双积分及 Dirichlet 展开绝对可积，再在射线角 `phi=1/T` 上给出
进入 DI 估计所需的加权核界。这里没有假设对偶算术和的消去。

这是一份纸面证明，不是新的 Lean 通过记录；#500、#508、#510、
#512 源树不改，本次从 #512 的 `1f23dabc` 独立继续。
核的源目标是 [Conrey 1989, (62)、(67)–(68) 与 Lemma 7, pp.19–21](https://aimath.org/~kaur/publications/24.pdf)。
下文使用已重新推导的归一化及移位符号，并证明实际界，不引用
原文“与另一篇论文相同”的证明省略。

## 1. 冻结实际核、四种相位与积分测度

继续取 `L=log T>=24, Delta=T^(1-delta), 0<delta<1`，
`T<=w<=2T`、`alpha=a/L, beta=b/L, gamma=alpha+beta`、
`|a|,|b|<=3`、`u=1/2+iw-beta`。实际有限 mollifier 系数及整数
`2<=Y<=T` 与前文相同。
具体为 `c_j(n)=mu(n) P_j(log(Y/n)/log Y)`（`1<=n<=Y`），
其中 P_j 固定且不依赖移位，记 `B_j=sup_(0<=t<=1)|P_j(t)|`，
于是 `|c_j(n)|<=B_j`。原实际对偶项取自
[Gaussian 轮廓分解的 R-actual 与第6节](2026-08-31-conrey-gaussian-contour-decomposition.md)。

对 `sigma=+1,-1`，射线 `L_(sigma phi)` 均向外；写

\[
 W_u(v)=v^u e^{-\Delta^2(\operatorname{Log}v)^2/4},\qquad
 z_\sigma^0(v)=-i\sigma(v-1).
\]

z_sigma^0 始终在右半平面。相位标签 `epsilon=+1,-1` 对应

\[
 C_-(s,\gamma)=\cos\tfrac\pi2(2s-\gamma),\qquad
 C_+(s,\gamma)=\cos\tfrac\pi2\gamma.
\]

定义**实际**核

\[
 \boxed{\mathscr K_{\sigma,\epsilon}(v,s)
 =\frac1{\pi i}W_u(v)(2\pi)^{\gamma-s-1}
 (z_\sigma^0(v))^{s-1}
 \Gamma(1-s)\Gamma(s-\gamma)\Gamma(s)C_\epsilon(s,\gamma).}
 \tag{K-actual}
\]

全部复幂用主值 Log；积分测度是 `ds dv/v`，核中不再重复放置
`1/v`。竖线 s=c+i tau 向上，范数测度为 `d tau dr/r`。

从原式的 `z_sigma(v)=2 pi (h/k) z_sigma^0(v)` 提取尺度，
`(2pi)^(gamma-2s) (2pi)^(s-1)` 恰为
`(2pi)^(gamma-s-1)`。因此 (K-actual) 没有遗漏那个额外的
`(2pi)^(-1)`，也不是原文印刷前因子的直接复制。

## 2. 所需 Gamma 竖带界从已证 digamma 余项得到

先证明：对任意固定紧区间 `0<A<=x<=B`，有

\[
 |\Gamma(x+it)|\le C_{A,B}(1+|t|)^{x-1/2}e^{-\pi|t|/2}.
 \tag{Gamma-strip}
\]

[前一主项证明](2026-08-31-conrey-gaussian-main-term-evaluation.md)
已从 Euler 求和推导 `psi(z)=Log z+O(1/|Im z|)`，在这样的
正实部竖带及 `|Im z|>=1` 上一致。
另一方面，Gamma 共轭对称性和
[反射公式](https://dlmf.nist.gov/5.5.E3) 给出精确值

\[
 |\Gamma(1/2+it)|^2=\frac\pi{\cosh(\pi t)}.
\]

沿实方向从1/2到x积分 `Re psi(q+it)`，得到

\[
 \log\frac{|\Gamma(x+it)|}{|\Gamma(1/2+it)|}
 =(x-1/2)\log|t|+O_{A,B}(1/|t|).
\]

路径实部下界取 `min(A,1/2)>0`，长度有统一上界；因此允许
x<1/2。结合半整数点的精确值即得高高度界。低高度紧集无
Gamma 极点，以紧性补齐 (Gamma-strip)。

若实部在固定负区间但避开 Gamma 极点，使用
`Gamma(z)=Gamma(z+1)/z` 或其迭代式，保留分母的
`(1+|t|)` 幂次，即可把 (Gamma-strip) 转移过去。

现在固定 `0<eta<=1/8`，要求

\[
 L\ge\max(24,16/\eta).
 \tag{eta-threshold}
\]

于是即使在开双圆盘 `|a|,|b|<4`，仍有 `|gamma|<eta/2`。
对 `c=eta` 或 `c=1+eta`，三份 Gamma 的逐项界为

\[
 \begin{split}
 |\Gamma(1-s)|&\le C_\eta(1+|\tau|)^{1/2-c}e^{-\pi|\tau|/2},\\
 |\Gamma(s-\gamma)|&\le C_\eta(1+|\tau|)^{c-\Re\gamma-1/2}e^{-\pi|\tau|/2},\\
 |\Gamma(s)|&\le C_\eta(1+|\tau|)^{c-1/2}e^{-\pi|\tau|/2}.
 \end{split}
\]

第二行把 `tau-Im gamma` 换成 tau 只花费统一常数。
在 c=1+eta 时，第一行通过 `Gamma(2-s)/(1-s)`，分母在
低高度至少 eta；在 c=eta 时直接使用正实部界。
在初始直线 c=3/2 上，对 `|gamma|<=1/4` 同样成立，常数可取
绝对常数，因为分母 `|1-s|>=1/2`。

两个余弦均满足 `|C_epsilon|<=C exp(pi|tau|)`；故在以上三条
线上有共同的实际乘积界

\[
 |\Gamma(1-s)\Gamma(s-\gamma)\Gamma(s)C_\epsilon|
 \le C_\eta(1+|\tau|)^{c-\Re\gamma-1/2}e^{-\pi|\tau|/2}.
 \tag{Gamma-product}
\]

不用两相位之间的相消，也没有让 eta 随 T 趋零。

## 3. 射线原点附近的角隙不能当常数

写 `v=r exp(i sigma phi)`，记

\[
 d_\phi(r)=|r e^{i\phi}-1|,\qquad
 \omega_\sigma(r)=\arg z_\sigma^0(v),\qquad
 q_\phi(r)=\pi/2-|\omega_\sigma(r)|.
\]

q_phi 与 sigma 无关，且 `0<q_phi<=pi/2`。从右半平面几何得

\[
 \sin q_\phi(r)=\frac{r\sin\phi}{d_\phi(r)},\qquad
 q_\phi(r)\ge\frac{r\sin\phi}{d_\phi(r)}.
 \tag{angle-gap}
\]

虽然 r->0 时该角隙趋零，损失是可以明确计算的。
`|z^(s-1)|=|z|^(c-1) exp(-tau arg z)`，结合 (Gamma-product)，
再计入未来算术估计所需的权重 `1+|s|`，得到

\[
 (1+|s|)|\mathscr K_{\sigma,\epsilon}(v,s)|
 \le C_\eta |W_u(v)|d_\phi(r)^{c-1}
 (1+|\tau|)^{c-\Re\gamma+1/2}e^{-q_\phi(r)|\tau|}.
\]

当前幂次 `p=c-Re gamma+1/2` 在固定正紧区间内。对
`0<q<=pi/2`，换元 `x=q|tau|` 并用 Gamma 的正实积分可得
`int_R (1+|tau|)^p exp(-q|tau|)d tau <= C_p q^(-p-1)`，
常数对上述 p 区间一致。因此

\[
 \int_\mathbb R(1+|s|)|\mathscr K_{\sigma,\epsilon}(v,s)|d\tau
 \le C_\eta |W_u(v)|
 (\sin\phi)^{-c+\Re\gamma-3/2}
 r^{-c+\Re\gamma-3/2}
 d_\phi(r)^{2c-\Re\gamma+1/2}.
 \tag{tau-integrated}
\]

这里对 (angle-gap) 取负幂的方向正确，幂次总和保留为
`(c-1)+(c-Re gamma+3/2)=2c-Re gamma+1/2`。

## 4. 先得固定参数绝对 Fubini

对任意固定 `0<phi<pi/2`，有

\[
 |W_u(v)|=r^{\Re u}
 \exp(-\sigma\phi\Im u+\Delta^2\phi^2/4)
 e^{-\Delta^2\log^2r/4}.
\]

又 `d_phi(r)<=1+r`。所以 (tau-integrated) 再对 `dr/r`
积分有限：在 `x=log r` 坐标中，仅有固定实指数增长乘负二次
Gaussian；零点和无穷远两端均可积。这证明实际加权双积分

\[
 \int_{L_{\sigma\phi}}\int_{(c)}
 (1+|s|)|\mathscr K_{\sigma,\epsilon}(v,s)|\,|ds|\,|dv/v|<\infty.
 \tag{K-Fubini}
\]

初始线 c=3/2 上，实际两份对偶 D 的 Dirichlet 展开在范数中
由 `zeta(3/2-Re gamma) zeta(3/2)` 控制，最多为
`zeta(5/4) zeta(3/2)`。h,k 外层有限，正底数复幂的范数在
这条竖线上与 tau 无关。因此 Tonelli/Fubini 也适用于
**展开后的全部 m,n 项和两个积分**。

这比先前仅有的“每个 v 点内层收敛”和“合并余项可积”更强。
但它没有在 c=eta 上展开无限 D 级数；那条线上的后续操作必须
先用有限 dyadic 块。

## 5. 取 phi=1/T 后的有效核尺度

现在取 `phi=1/T`。因为 `Delta<=T`、`w<=2T`，角度产生的
`exp(-sigma phi Im u+Delta^2 phi^2/4)` 有绝对上界。
又 `sin(1/T)>=2/(pi T)`，于是 (tau-integrated) 给出

\[
 I_c:=\int_{L_{\sigma/T}}\int_{(c)}
 (1+|s|)|\mathscr K_{\sigma,\epsilon}|\,|ds|\,|dv/v|
 \le C_\eta T^{c-\Re\gamma+3/2}
 \int_0^\infty r^{\Re u-c+\Re\gamma-3/2}
 d_{1/T}(r)^{2c-\Re\gamma+1/2}
 e^{-\Delta^2\log^2r/4}\frac{dr}{r}.
\]

令 `x=log r`、`h=2c-Re gamma+1/2>0`。精确的初等界

\[
 |e^{x+i\sigma/T}-1|\le e^{|x|}(|x|+1/T)
\]

将实指数因子吸收为一个固定 `exp(B|x|)`。B 和 h 留在固定
有界范围；`Delta>=1` 时
`exp(B|x|-Delta^2 x^2/4)<=C_B exp(-Delta^2 x^2/8)`。
因为 `1/T<=1/Delta`，换元 `y=Delta x` 得到

\[
 \int_\mathbb R e^{-\Delta^2x^2/8}(|x|+1/T)^h\,dx
 \le C_h\Delta^{-h-1}.
\]

正实 Gaussian 矩在 h 的紧区间上统一有界，故

\[
 \boxed{I_c\le C_\eta
 T^{c-\Re\gamma+3/2}\Delta^{-2c+\Re\gamma-3/2}.}
 \tag{K-effective}
\]

在 c=eta 或 c=1+eta 时，它推出所需的共同尺度

\[
 \boxed{I_c\le C_\eta\Delta^{-c-5/2}T^{5/2+\eta}.}
 \tag{K-Lemma7}
\]

具体地，两式右边之比为
`T^(-eta) (Delta/T)^(1-c+Re gamma)`。
当 c=eta 时指数为正，比值至多1；当 c=1+eta 时，比值为
`Delta^(-eta) (Delta/T)^(Re gamma)`，由
`|gamma|<=6/L`、`|log(Delta/T)|<=L` 控制在 `exp(6)` 内。
这说明大 O 常数不依赖 T、w、移位或 delta；可依赖固定 eta。

在初始线 c=3/2，(K-effective) 同样给出
`I_(3/2)<=C T^3 Delta^(-9/2)`。这里仍只是核的 L1 尺度，
不是对完整算术余项的消去估计。

## 6. 本节关闭什么、仍没有关闭什么

本节证明了实际双积分/Dirichlet 展开的绝对 Fubini，以及后续
两条竖线上的 `1+|s|` 加权核界，涵盖两射线、两余弦相位和闭
复移位域。没有在原点附近使用一个错误的固定角隙常数。

同一检查点的 [有限块移线证明](2026-08-31-conrey-dual-dyadic-contour.md)
进一步处理真实有限 dyadic 块的选线、s=1 留数及快速衰减。
在完整四相位采用同一选线时，还证明合计留数逐块精确相消。
仍须证明长 mollifier 所需的真正 DI 算术消去及块求和。
核界本身不能删除 #512 中的实际对偶项，完整均方、全局去平滑、
简单零点比例和原生 Lean 验证仍未完成。
