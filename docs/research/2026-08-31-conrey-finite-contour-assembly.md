# Conrey 实际有限 Möbius 和：轮廓误差拼接

本轮从冻结的 `47c9284010de99c8cbac976c94110f7196e4d325` 继续，
不改动 #500 分支。目标是把已经原生证明的右尾、左右竖边和水平边接到
实际有限互素 Möbius 和；不新增解析假设，不声称已证明完整 Conrey 定理。

## 数学推导（先于本轮 Lean 实现）

写 `W_m(z)=z/Q(1+z)/F_m(1+z)`，其中 `Q` 是实际 ζ pole-unit，
`F_m(s)=prod_{p|m}(1-p^(-s))`。记

\[
 S=\sum_{1\le n\le X,(n,m)=1}\mu(n)n^{-1-\alpha}\log(X/n),
 \qquad J=(\log X)W_m(\alpha)+W_m'(\alpha).
\]

`S` 使用自然数下取整；整数端点的对数权恰为零，不作半权约定。
假设 `m>=1, X>=1, 0<=delta<=1/16`。统一常数先于所有可变参数选取：
从实际高矩形取 `kappa_H`，左边界取 `kappa_L,C,M_L`，水平边取 `c,T`，令

\[
 \kappa=\min(\kappa_H,\kappa_L,c),\qquad
 M=\max(M_L,T+1).
\]

假设 `K>=M, |alpha|<b, |alpha|<u, b+|alpha|<=2delta`，以及
`b+|alpha|<=kappa/(1+log(K+3)), u+|alpha|<=1`。
这些条件推出 `b,u>0` 和 `a=Re(alpha)+u>0`。
因为 `log(K+1)<=1+log(K+3)`，同一个窄条宽度满足三个既有估计的条件。

令 `R,L` 为右、左竖线上的实际被积函数沿高度从 `-K` 到 `K` 的积分；
`B,H` 为底、顶水平边上沿实部从 `-b` 到 `u` 的积分。正向矩形恒等式为

\[
 B-H+iR-iL=2\pi iJ.
\]

因此必须保留如下符号和归一化：

\[
 S-J=(S-R/(2\pi))+L/(2\pi)+i(B-H)/(2\pi).
\]

写 `B_m=prod_{p|m}(1+p^(-(1-2delta)))` 和

\[
 A=X^u\frac{1+\Re\alpha+u}{\Re\alpha+u},\quad
 L_E=C B_m X^{-b}(1+\log(1+1/b)),
\]
\[
 H_E=\frac{(b+u)X^u C_0B_m
       (1+\log(K+1)/c)\exp(\log(K+1)/4)}{K^2}.
\]

右尾既有估计为 `|S-R/(2pi)|<=A/(pi K)`，不是 `A/K`。
左右竖边以 `dw=i dt` 积分；因此左边的系数是 `1/(2pi)`。
两条水平边各为 `H_E`，合计归一化后是 `H_E/pi`。三角不等式给出

\[
 \boxed{|S-J|\le A/(\pi K)+L_E/(2\pi)+H_E/\pi.}
\]

这估计实际有限和而非任意抽象函数；所有边的解析性、可积性和定量界
均来自既有原生证明。`alpha=0` 和 `X=1` 都包含在内；`m=0` 被明确排除，
因为右线的互素 Dirichlet 级数恒等式要求非零模数。
`delta=0` 没有满足正宽条件的实例，但整个声明非空。
这里没有线性 profile 的额外 `1/H` 因子。

## 与完整内层渐近的边界

精确留数 `J` 尚未替换成 `(1+alpha log X)/F_m(1+alpha)`。
该差的统一移位误差仍按前一研究文件第17节另证；随后还需参数特化、
Volterra 转移、外层算术、实际长均方主项及最终零点比例。

历史对照是 [Conrey 1983, Lemma 10, pp.54–56](https://aimath.org/~kaur/publications/3.pdf)。
这里重建有限参数估计，不把原文渐近或其更强倒数 ζ 界作为 Lean 假设。

## 冻结验收

字面契约先于实现编写：常数在所有可变参数之前，左侧为实际互素有限和，
右侧完整保留三个误差和各自的 `pi` 归一化。初次失败必须只因目标定理缺失。

```sh
nice -n10 lake build Test.ConreyCoprimeMobiusFiniteContourContract \
  Test.ConreyCoprimeMobiusLeftBoundContract \
  Test.ConreyCoprimeMobiusPerronTailContract \
  Test.ConreyCoprimeMobiusHorizontalBoundContract \
  Test.ConreyCoprimeMobiusHighRectangleContract
uv run --no-project --with pytest --with mpmath --with numpy --with python-flint python -m pytest -q
python3 scripts/check-targets-consistent.py
python3 scripts/check-chain-gaps.py
git diff --check
```

当前状态：数学推导与独立只读审查完成，Lean 实现及最终 SHA 验收待完成。
新 worktree 的同源基线复核已退出成功（8738 jobs）；这不是新契约的通过
记录。按唯一集成负责人的资源协调要求，尚未启动新契约的 RED 或新证明
编译，等待其安排的内存窗口；冻结 #500 源树不动。

## 后续数学：直接把有限参数误差转移到实际多项式权

这里给出完整的有限参数推导，不把下面的转移作为 Lean 调用假设。
它尚未形式化，也不扩大上面的有限和契约：实际实现仍先闭合一次对数
有限和。一个有用的顺序变化是先转移精确 `W,W'` 留数，再化简它们；
不必先证明一整族更高阶 Perron 核或 `W` 的高阶导数界。

固定上文的 `m,delta,alpha,K,b,u`，并取 `H>0, 1<=X<=exp H`。
令 `t=log X/H`，设 `P` 为 `[0,1]` 上的固定复值 `C^2` 函数且 `P(0)=0`。
写 `p0=|P'(0)|`，取 `p2>=0` 满足 `|P''(s)|<=p2` 于 `[0,1]`。
定义实际有限多项式权和

\[
 G_P(X)=\sum_{1\le n\le X,(n,m)=1}
   \mu(n)n^{-1-\alpha}P\!\left(\frac{\log(X/n)}H\right).
\]

对每个 `1<=n<=floor X`，Taylor 积分余项及换元
`s=log(X/v)/H` 给出精确恒等式

\[
 P\!\left(\frac{\log(X/n)}H\right)
 =\frac{P'(0)}H\log(X/n)
 +\frac1{H^2}\int_n^X
   P''\!\left(\frac{\log(X/v)}H\right)\log(v/n)\,\frac{dv}{v}.
\]

求和时全程用固定有限集合 `1<=n<=floor X`；第 `n` 项乘上
`1_{v>=n}`。它在 `v=n` 连续，因为 `log(v/n)=0`。于是所有有限和
均可与通常积分交换，并准确得到

\[
 G_P(X)=\frac{P'(0)}H S(X)+\frac1{H^2}\int_1^X
     P''\!\left(\frac{\log(X/v)}H\right)S(v)\,\frac{dv}{v}.
 \tag{V-fin}
\]

在 `X=1` 时区间退化而两边均为零；整数截断处没有跳跃修正。
对于每个 `1<=v<=X`，同一组轮廓参数有效，不重新选择任何常数。
把上面的有限和误差写成

\[
 |S(v)-(\log v)W_m(\alpha)-W_m'(\alpha)|
 \le D_+v^u+D_-v^{-b},
\]
\[
 D_+=\frac{1+\Re\alpha+u}{(\Re\alpha+u)\pi K}
 +\frac{(b+u)C_0B_m(1+\log(K+1)/c)
               \exp(\log(K+1)/4)}{\pi K^2},
 \quad D_-=\frac{CB_m(1+\log(1+1/b))}{2\pi}.
\]

关键是 `D_+,D_-` 不依赖 `v`。精确留数部分经 (V-fin) 变成

\[
 W_m(\alpha)P(t)+\frac{W_m'(\alpha)}H P'(t),
\]

因为 `int_0^t P''(t-r)dr=P'(t)-P'(0)`，且
`int_0^t rP''(t-r)dr=P(t)-tP'(0)`。用正的标量积分
`int_1^X v^(u-1)dv=(X^u-1)/u` 和
`int_1^X v^(-b-1)dv=(1-X^(-b))/b` 控制误差，得到真正的有限参数界

\[
\begin{aligned}
&|G_P(X)-W_m(\alpha)P(t)-W_m'(\alpha)P'(t)/H|\\
&\quad\le D_+\left(\frac{p_0X^u}H+
                    \frac{p_2(X^u-1)}{H^2u}\right)
       +D_-\left(\frac{p_0X^{-b}}H+
                    \frac{p_2(1-X^{-b})}{H^2b}\right).
\end{aligned}
\tag{PV-fin}
\]

这是从实际一次对数和得到的多项式权估计，不以抽象渐近函数替代 `S`。
即使 `X=1`，右侧也允许非零：左侧此时是 `|W_m'(alpha)P'(0)|/H`，
而不是零。不能因为原始和为零就把主项也误设为零。

选定的具体多项式
`P(t)=(84t+15t^3+t^5)/100` 满足 `p0=21/25`，
`P''(t)=9t/10+t^3/5`，可取 `p2=11/10`。因此无需未知的 profile 范数
就可把该实际权代入 (PV-fin)。

## 所选大参数确实接上原算术误差尺度

以下仍是数学证明，不是已通过的 Lean 端点。
令 `ell=log H, K=H^4, b=kappa/(16ell), u=2/H, delta=1/ell`，
`|alpha|<=1/H`。取只依赖统一常数的 `H0`，使 `H>=H0` 时

- `ell>=16`、`K>=M`、`1/H<b`、`3/H<=1`；
- `1+log(H^4+3)<=8ell`；
- `1/H<=min(delta,r)`，其中 `r` 是 pole-unit 的固定解析半径。

存在这样的 `H0`，因为 `log H/H` 趋于零且
`log(H^4+3)/log H` 趋于4。由 `b+|alpha|<2b=kappa/(8ell)`
及第二项（注意分母方向）可得完整共同窄条条件。
又 `kappa<=1/4` 保证 `b+|alpha|<=2delta`。

对任意 `1<=X<=exp H`，有 `X^u<=exp 2`、
`1/H<=a=Re(alpha)+u<=3/H`，从而右尾部分为 `O(H^(-3))`。
水平边部分为 `O(B_m H^(-7)ell)`；两者经 (PV-fin) 后分别为
`O_P(H^(-4))` 和 `O_P(B_m H^(-8)ell)`。
这里 `(X^u-1)/u<=H(exp 2-1)/2`，所以没有隐含的额外 `H` 损失。

由于 `B_m>=1`、`1/b=O(ell)` 及
`1+log(1+1/b)=O(ell)`，左边误差经 (PV-fin) 为

\[
 O_P\!\left(B_m[H^{-2}\ell^2+H^{-1}\ell X^{-b}]\right).
\]

最后需要实际局部留数误差（前一文件第17节，下段补齐统一常数的取法）：
`W_m(alpha)-alpha E_m(alpha)=O(B_m|alpha|^2)`，
`W_m'(alpha)-E_m(alpha)=O(B_m|alpha|(1+1/delta))`。
它们把 (PV-fin) 的主项替换为
`[alpha P(t)+P'(t)/H]/F_m(1+alpha)`，代价仅为 `O_P(B_m ell/H^2)`，
吸收在上述误差中。这证明了该有限参数路径在数学上足以给出所需 (GV)，
并明确 Lean 剩余顺序：有限轮廓拼接 → 实际有限 Volterra → 局部移位留数
误差及参数特化。外层算术和实际长均方主项仍是之后的独立任务。

## 局部留数误差的统一常数与所选多项式

这里不用把未证明的误差式作为上一节的数学前提：可以直接如下构造。
`U(z)=Q(1+z)^(-1)` 在零点附近实际解析且 `U(0)=1`。
固定 `0<rho<=1/4`，使 `U` 在闭圆盘 `|z|<=2rho` 的邻域解析，
再取 `A>=1` 为该紧圆盘上的范数上界，记 `D=A/rho`。
对每个 `|z|<=rho`，中心 `z` 半径 `rho` 的圆包含在该大圆盘内，
Cauchy 估计及沿线段从0到z积分给出

\[
 |U(z)|\le A,\qquad |U'(z)|\le D,\qquad |U(z)-1|\le D|z|.
\]

这些常数都先于模数 `m` 选取。另一方面，若 `0<delta<=1/16` 且 `|alpha|<=delta`，
中心 `alpha` 半径 `delta` 的闭圆盘满足 `Re z>=-2delta>-1`，
所以实际 Euler 倒数 `E_m` 在其邻域解析。原生统一 Euler 界给出

\[
 |E_m(\alpha)|\le C_0B_m,\qquad
 |E_m'(\alpha)|\le C_0B_m/\delta.
\]

此处这个较大的 `delta` 圆盘只用于 `E_m`，没有要求 `U` 也在它上面
解析。正半径 `delta>0` 不能省略；在前文应用中由
`0<b` 及 `b+|alpha|<=2delta` 推出。只要 `|alpha|<=min(delta,rho)`，
对 `W_m(z)=zU(z)E_m(z)`
精确求导即得

\[
 |W_m(\alpha)-\alpha E_m(\alpha)|
   \le C_0D B_m|\alpha|^2,
\]
\[
 |W_m'(\alpha)-E_m(\alpha)|
   \le C_0 B_m|\alpha|(2D+A/\delta).
 \tag{R-fin}
\]

这是避免丢失 `|alpha|` 的关键：对 `zU(z)E_m(z)` 求导，而不是对
半径 `delta` 上的粗略二次余项再取一次 Cauchy 上界。
当 `alpha=0` 时两项误差都严格为零。

所选 `P` 在 `[0,1]` 上满足 `0<=P<=1` 和 `0<=P'<=67/50`。
因此 (PV-fin) 主项与真正目标主项之间的误差至多为

\[
 C_0B_m\left(D|\alpha|^2+
       \frac{67|\alpha|}{50H}(2D+A/\delta)\right).
\]

在 `|alpha|<=1/H, delta=1/ell, ell>=1` 下，这进一步不超过

\[
 \frac{C_0B_m\ell}{H^2}
   \left(D+\frac{67}{50}(2D+A)\right).
\]

由此，在纯数学层面，实际有限和 → 多项式权 → 真正算术主项的局部
推导已经闭合且常数统一；待完成的是这些新步骤的原生形式化和后续外层
分析。不能据此宣布完整均方主项或最终零点比例已获证明。

本轮只读数学审查覆盖了窄条、轮廓方向、归一化、(V-fin)、(PV-fin)、
参数特化和 (R-fin)。审查指出独立陈述 Cauchy 圆盘时必须显式保留
`delta>0`，现已补入；应用中的正宽条件本来就保证这一点。
本文件是数学推导检查点，尚无新 Lean 定理通过记录，也不更新 #500。
