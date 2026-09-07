# Conrey 实际对偶余项：精确算术分块、两种移线及留数控制

本节把刚证明的实际核 Fubini 用在 #512 仍未估计的对偶余项上。
先做绝对收敛域内的完整算术重组，再逐个有限 dyadic 块移线，
保留全部 s=1 留数并证明这些留数快速衰减。
四相位采用相同选线时，进一步证明合计留数逐块精确相消。
这一步没有把无限 Dirichlet 级数直接搬到左半收敛域。

最终未估计的对象是明确的有限算术块及其求和；DI 消去仍未
证明。当前交付仍为纸面数学，没有新 Lean 构建记录。
原始结构参照 [Conrey 1989, (67)–(74), p.20 及 Lemmas 7–8, p.21](https://aimath.org/~kaur/publications/24.pdf)，
使用本任务已校正的双扭转符号、余弦移位和 `2pi` 归一化。

## 1. 沿用已证明的实际核

参数、两条射线、相位标签与
[核/Fubini 证明](2026-08-31-conrey-dual-kernel-fubini.md) 完全相同。
特别地固定 `0<eta<=1/8`，`L>=max(24,16/eta)`，取
`phi=1/T`；该选择对复移位独立。
初始竖线为 c0=3/2，后续两线为 eta 与1+eta。

将约数系数记为

\[
 d_\gamma(n)=\sum_{m\mid n}m^\gamma.
\]

它不是 Kronecker delta，也不是已经取范数的约数函数。
在 `c>max(1,1+Re gamma)` 上有

\[
 \sum_{n\ge1}|d_\gamma(n)|n^{-c}
 \le\zeta(c-\Re\gamma)\zeta(c)<\infty.
 \tag{divisor-absolute}
\]

这是对原双级数逐项取范数、再按 n=ml 绝对重排的直接结果。

## 2. 提取每一个 h,k 的真正尺度

写 `d=gcd(h,k), H=h/d, K=k/d`，选择任一整数 Hbar 使
`H Hbar=1 mod K`。K=1 时取 Hbar=0，所有相位均为1。
对 `kappa=+1,-1`，定义实际算术函数

\[
 \mathscr A_\kappa(s)=\sum_{n\ge1}d_\gamma(n)n^{-s}
 \sum_{h,k\le Y}c_1(h)c_2(k)
 d^{1+\gamma-2s}h^{s-1-\beta}k^{s-1-\alpha}
 e(\kappa n\bar H/K),\qquad e(x)=e^{2\pi i x}.
 \tag{A-actual}
\]

在 c0 上，两份对偶 D 分别展开为扭转 `kappa=sigma epsilon`。
全部换序由 (divisor-absolute) 及前文加权双积分界保证。精确
尺度计算为

\[
 k^{\beta-1}h^{-\beta}K^{2s-1-\gamma}(h/k)^{s-1}
 =d^{1+\gamma-2s}h^{s-1-\beta}k^{s-1-\alpha}.
\]

因此原来的实际对偶余项恰为

\[
 \boxed{\mathcal E=
 \sum_{\sigma=\pm1}\sum_{\epsilon=\pm1}
 \int_{L_{\sigma/T}}\int_{(3/2)}
 \mathscr K_{\sigma,\epsilon}(v,s)
 \mathscr A_{\sigma\epsilon}(s)\,ds\,\frac{dv}{v}.}
 \tag{E-kernel-arithmetic}
\]

这里 C_- 对应负逆元扭转、C_+ 对应正逆元扭转；不能把两者
同时换成同一个相位。正底数复幂不产生额外分支。

## 3. gcd 分层的 1/g 精确消去

在 (A-actual) 中令 `h=g u, k=g v`、`gcd(u,v)=1`。
此处 u,v 是正整数；为免符号冲突，下文将射线积分变量改记 z，
并将前文的解析参数 `u=s_0-beta` 在本节改记 `upsilon=s_0-beta`。
核始终使用这个固定解析参数，而不是算术求和指标 u。
精确 g 幂次为

\[
 g^{1+\gamma-2s}(gu)^{s-1-\beta}(gv)^{s-1-\alpha}
 =g^{-1}u^{s-1-\beta}v^{s-1-\alpha}.
\]

所以

\[
 \mathscr A_\kappa(s)=\sum_{g\le Y}\frac1g
 \sum_{n\ge1}d_\gamma(n)n^{-s}
 \sum_{\substack{u,v\le Y/g\\(u,v)=1}}
 c_1(gu)c_2(gv)u^{s-1-\beta}v^{s-1-\alpha}
 e(\kappa n\bar u/v).
 \tag{gcd-exact}
\]

系数中还保留 `mu(gu),mu(gv)`；没有把它们擅自变成
`mu(g)^2 mu(u)mu(v)` 而忘掉与 g 的互素限制。

## 4. 真正覆盖 n=1 的有限 dyadic 块

取尺度集合 `D={2^j:j=0,1,2,...}`，使用半开块
`B_N={n in N: N<=n<2N}`。这样 n=1 恰好属于 N=1 的块，
各正整数只出现一次。

对 `N,U,V in D`、`1<=g<=Y`，定义实际**有限**整函数

\[
 \begin{split}
 A_\kappa(N,U,V,g;s)=
 \sum_{n\in B_N}d_\gamma(n)n^{-s}
 \sum_{\substack{u\in B_U,\ v\in B_V\\
                 gu\le Y,\ gv\le Y,\ (u,v)=1}}
 c_1(gu)c_2(gv)u^{s-1-\beta}v^{s-1-\alpha}
 e(\kappa n\bar u/v).
 \end{split}
 \tag{block-actual}
\]

系数 c_j 只在 `gu,gv<=Y` 的实际范围求值。若内层为空则该块为0。
非空时 U,V<=Y/g；所以 U,V、g 总共只有有限多个选择，只有 N
仍为无限序列。在 c0 上完整重组为

\[
 \mathcal E=\sum_{\sigma,\epsilon}\sum_{g\le Y}\frac1g
 \sum_{N,U,V\in\mathcal D} Z_{\sigma,\epsilon}(N,U,V,g;3/2),
 \tag{E-blocks}
\]

其中

\[
 Z_{\sigma,\epsilon}(N,U,V,g;c)=
 \int_{L_{\sigma/T}}\int_{(c)}
 \mathscr K_{\sigma,\epsilon}(z,s)
 A_{\sigma\epsilon}(N,U,V,g;s)\,ds\,\frac{dz}{z}.
 \tag{Z-actual}
\]

按块求和与两个积分都绝对可交换，因为取范数后仍受第1节
的同一约数 Dirichlet 级数和有限 u,v,g 和控制。

## 5. 只对有限块移线，极点清单完整保留

为每个尺度三元组选择

\[
 c_{NUV}=\begin{cases}
 \eta,&UV\ge TN,\\
 1+\eta,&UV<TN.
 \end{cases}
 \tag{chosen-line}
\]

等号明确放在左线分支。A(block;s) 为有限整函数，在任何固定
实部条带上范数关于 `Im s` 一致有界。
对每个固定射线点 z，前文 Gamma 界在高水平边上给出
`C_z(1+|Im s|)^B exp(-q_phi(z)|Im s|)`，其中 q_phi(z)>0。
因此上下水平连接边消失。整条移动区间为 `eta<=Re s<=3/2`：

- `Gamma(s)` 的极点都在0及左侧；
- `Gamma(s-gamma)` 的极点在 `gamma-j`，实部小于 eta；
- `Gamma(1-s)` 只在 s=1 有条带内极点；
- 其余因子全纯，z 和正实底数均不为0。

移到1+eta不跨极点；移到eta恰跨 s=1。
不能在这里用无限 `A_kappa(s)` 代替有限块：其 Dirichlet
收敛域不包含左线。

正向矩形给出 `integral_right-integral_left=2 pi i Res`。
`Gamma(1-s)` 在 s=1 的留数为 -1，故令

\[
 G_\sigma=\int_{L_{\sigma/T}}W_\upsilon(z)\frac{dz}{z}
 =\frac{2\sqrt\pi}{\Delta}e^{\upsilon^2/\Delta^2},
\]

则当 UV>=TN 时，确切移线贡献为

\[
 \boxed{\mathcal R_{\sigma,\epsilon}(N,U,V,g)
 =-2(2\pi)^{\gamma-2}\Gamma(1-\gamma)C_\epsilon(1,\gamma)
 A_{\sigma\epsilon}(N,U,V,g;1)G_\sigma.}
 \tag{residue-exact}
\]

这里核里的 `1/(pi i)` 已经与 `2 pi i` 合并；不能再乘一次
`2pi`。`C_-(1,gamma)=-cos(pi gamma/2)`，
`C_+(1,gamma)=cos(pi gamma/2)`，故两个相位的留数符号相反，
但没有假设其算术系数相同从而相消。

逐点移线之后再对 z 积分合法：两条竖线的实际核均绝对可积，
有限块的范数与 Im s 无关；留数的 Gaussian 积分也绝对可积。
因此得到真正的块恒等式

\[
 Z(3/2)=Z(c_{NUV})+
 \boldsymbol 1_{UV\ge TN}\mathcal R_{\sigma,\epsilon}(N,U,V,g).
 \tag{block-shift}
\]

## 6. 留数有限和：单独快速衰减，四相位精确相消

当块非空且 UV>=TN 时，

\[
 N\le UV/T\le (Y/g)^2/T,\qquad n<2N\le2Y^2/T.
 \tag{finite-residue-range}
\]

故被跨留数中的 N 也只有有限多个。不得省略这个范围理由再对
所有 N 在 s=1 求和。

用粗界即可处理这些留数，不消耗 DI 的相消。
因为 `n<=2Y^2`、`Y<=T`、`|gamma|<=6/L`，有
`|d_gamma(n)|<=C tau(n)<=C n`，C 为绝对常数；并且
`|u^(-beta)v^(-alpha)|<=e^6`。于是 s=1 的每个 n,u,v 项
（除去1/g）的范数不超过 `C B_1B_2`。
半开 dyadic 块互不相交，所有被跨块的项总和可以按实际 n,u,v
重排；取所有 `n<=2Y^2` 作上界，得到

\[
 \sum_{g\le Y}\frac1g
 \sum_{UV\ge TN}|A_\kappa(N,U,V,g;1)|
 \le C B_1B_2Y^2\sum_{g\le Y}\frac1g(Y/g)^2
 \le C B_1B_2Y^4.
\]

Gamma 与余弦在当前移位域上有固定界，而已证精确 Gaussian
评价给出 `|G_sigma|<=C Delta^(-1) exp(-T^(2delta)/2)`。
故合计移线留数满足

\[
 \boxed{|\mathcal R_{\rm shift}|\le
 C B_1B_2\frac{Y^4}{\Delta}e^{-T^{2\delta}/2}
 =O_{\delta,M}(B_1B_2T^{-M})\quad(M\ge0).}
 \tag{residue-uniform}
\]

其中 `R_shift=sum_(sigma,epsilon,g) 1/g sum_(UV>=TN) R`。
不利用两相位的取消，也不把任何无限 n 尾塞入该式。

当前实际 E 包含全部四相位，而且 (chosen-line) 与 sigma、epsilon
无关，因此还可作一个更强的精确简化。记
`Q_gamma=2(2pi)^(gamma-2) Gamma(1-gamma) cos(pi gamma/2)`，
并用已经证明的 `G_+=G_-=G`。对同一个有限块，(residue-exact) 给出

\[
 \mathcal R_{\sigma,-}=Q_\gamma G A_{-\sigma}(1),\qquad
 \mathcal R_{\sigma,+}=-Q_\gamma G A_{\sigma}(1),
 \qquad
 \sum_{\sigma,\epsilon}\mathcal R_{\sigma,\epsilon}=0.
 \tag{residue-cancellation}
\]

这里没有使用 `A_+(1)=A_-(1)`：两个系数各自出现一次正号和一次
负号。被跨块集合对四相位相同且有限，故 **R_shift=0 精确成立**。
上面的快速界仍分别控制未合并的各相位留数；若改变相位或选线，
必须重新检查该抵消，不能自动沿用零结论。

## 7. 移线后的无限尾仍可相加

左线块只有有限个，逐块绝对可积已经足够。
其余无限 N 块全在线 `c=1+eta`；因 `Re gamma<=eta/2`，
(divisor-absolute) 在该线由
`zeta(1+eta/2) zeta(1+eta)` 一致控制。
u,v,g 有限，所以这些块与双积分可再次绝对交换。
于是从原实际对偶余项得到精确等式

\[
 \boxed{\mathcal E=
 \sum_{\sigma,\epsilon}\sum_{g\le Y}\frac1g
 \sum_{N,U,V\in\mathcal D}
 Z_{\sigma,\epsilon}(N,U,V,g;c_{NUV}).}
 \tag{E-shifted}
\]

所有范数支配在 `|a|,|b|<4` 的紧子双圆盘上局部一致。
留数求和范围只依赖实际 T、Y 和整数尺度，不依赖复移位，且为
有限集，故各相位留数和全纯。沿用半径1/2的 Cauchy 圆后，所需
混合微分的各相位留数界也只乘 `5776/625`，仍比任意负幂小。
合计留数恒等于0，混合微分后也精确为0。

这里的无限尾绝对可积只是合法重组依据；其随 T 的粗上界并不
足够证明 `mathcal E=o(1)`，不能代替 DI 估计。

## 8. 当前真正剩下的算术任务

本节把实际 E 接成明确的有限块 (block-actual)、具体选线
(chosen-line)、正确归一化的核和已经关闭的留数误差。
在本节完整四相位组合中，该留数误差实际精确为0。
核的 `1+|s|` 加权 L1 界已经在 companion 中证明。

下一步必须对 (block-actual) 的真正互素逆元相位和两个 Möbius
系数证明所需消去，再按实际 N,U,V,g 范围求和。不得将固定 T
下的绝对 Fubini 或一个抽象误差 envelope 宣布为这份消去。
当前没有新增“假设块估计成立”的 Lean 接口。

因此实际 DI 算术估计、完整长均方、全局去平滑、简单零点比例
以及这些纸面步骤的原生验证仍未完成；本节不宣称严格 >2/5。
