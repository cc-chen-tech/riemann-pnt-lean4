# Conrey 实际双线性余项：精确矩形化、DI 应用与 Gaussian 均方接合

本节补出实际长双线性块使用 DI 定理前的全部适配：有限 Möbius
分组、g 互素限制、乘积硬截断和真实 profile 的分离。然后证明
所需块估计并接回 #513 的真实核，而不是新增一个条件接口。

**外部输入与结论层级：**本文使用 Deshouillers–Iwaniec 1984
Lemma 1 这一已发表谱估计；伴随 Type I 证明使用经典 Weil 定理。
这两份深输入没有在本任务中独立重证，更没有原生 Lean 证明。
以下关闭的是使用这些明确数学定理的纸面应用链。无条件原生形式化、
全局去平滑和最终简单零点比例仍不能宣布完成；同一参数的
[dyadic 区间去平滑](2026-08-31-conrey-dyadic-desmoothing.md) 在本检查点另行证明。

原刊已逐页核对：J.-M. Deshouillers and H. Iwaniec,
*Power mean-values for Dirichlet's polynomials and the Riemann zeta-function, II*,
[Acta Arith. 43 (1984), 305–312, Lemma 1 pp.310–311](https://www.impan.pl/shop/en/publication/transaction/download/product/104164)。
其证明在 p.311 明确调用作者1982论文的 Theorem 12；本文不隐藏该谱依赖。
Conrey 的应用位置是 [1989论文 pp.23–25, Lemma 9、(89)–(99)](https://aimath.org/~kaur/publications/24.pdf)。

## 1. 已有的真实对象和剩项

参数、系数与归一化全部沿用
[实际 Möbius/Type I 证明](2026-08-31-conrey-actual-mobius-type-i.md)。
其有限恒等式为 `mu=v_1+v_2+v_3`，其中

\[
 v_1(u)=\sum_{p q h=u,\ p,q>W}D(p)D(q)\mu(h),\qquad
 v_3(u)=-\sum_{ab=u}\lambda_W(a),\qquad W=U^{1/4}.
\]

伴随证明已经处理 v_2 以及 v_3 中 a<=W 的部分。
当前 S_II 是 v_1 全部项与 v_3 中 a>W 部分的真实有限和。
始终保留 `U<=u<2U`、`gu<=Y`、`v in B_V`、`gv<=Y` 和 `(u,vg)=1`。

## 2. 有限分组，避免把系数变成依赖另一变量的函数

### 2.1 v_1 部分

分别将 p,q 放入半开二进段 B_P、B_Q，仍保留 p,q>W。
利用 p,q 的对称性，只取 P<=Q：P<Q 的组乘2，P=Q 的组乘1。
当 P=Q 时保留所有有序 p,q，不再添加 p<=q 这一耦合限制。

令 a=p、b=qh，并把 b 再放入某个二进段 B_B。系数成为

\[
 d_A(a)=D(a)\boldsymbol1_{a>W},\qquad
 d_B(b)=\sum_{\substack{q\mid b\\q\in B_Q,\ q>W}}D(q)\mu(b/q),
 \qquad A=P.
 \tag{group-v1}
\]

d_A 只依赖 a，d_B 只依赖 b；没有留下 a<=q 之类的隐藏限制。
有 `|d_A(a)|<=tau(a)`、`|d_B(b)|<=tau_3(b)`。
非空组满足

\[
 U/4<AB<2U,\qquad W/2<A\le\sqrt{2U}.
 \tag{balanced-range}
\]

第一式由 `AB<=ab<4AB` 和 `U<=ab<2U` 得到。
第二式左端由 a>W、a<2A 得到；右端由 P<=Q、
`pqh>=PQ>=P^2` 和 `pqh<2U` 得到。
P,Q,B 的有效选择数至多 `C(1+log Y)^3`。

### 2.2 v_3 的 a>W 部分

把 a,b 各放入 B_A、B_B，取 `d_A(a)=-lambda_W(a)1_(a>W)`、
`d_B(b)=1`。lambda_W 支撑在 a<=W^2，故同样有
`W/2<A<=sqrt(U)` 和 `U/4<AB<2U`。
组数至多 `C(1+log Y)^2`，系数仍为约数界大小。

两种分组的每个组都保留真实乘积限制

\[
 H_g(ab)=\boldsymbol1_{U\le ab\le M_g},\qquad
 M_g=\min(2U-1,\lfloor Y/g\rfloor).
 \tag{hard-product}
\]

U 是整数，所以 `ab<2U` 精确等价于 `ab<=2U-1`。
若 M_g<U，该组为空。g 过滤精确拆成 `(a,g)=(b,g)=1`，
而 `(ab,v)=1` 精确拆成 `(a,v)=(b,v)=1`。

## 3. 整数乘积硬截断的精确 Mellin 分离

本节给出一个有限整数范围内的精确展开，无截断余项。
固定整数 R>=2、0<=M<=R，要求在 `1<=m<=R` 的整数点表示
`1_(m<=M)`。M=0 或 M=R 时分别取常数0或1即可。

其余情况取周期 `P=log(4R)+4`、`h=1/(8R)`。在一个周期中令
J 为区间 `[-1,log(M+1/2)]` 的示性函数，再与归一化区间核
`(2h)^(-1)1_[-h,h]` 作周期卷积，得连续分段线性函数 F_M。

对整数 m 有

\[
 |\log m-\log(M+1/2)|\ge\frac1{3R}>h.
\]

这是中值定理和 `|m-M-1/2|>=1/2` 的结果。左端支持边界-1与
`log m>=0` 相隔至少1；所选周期也留有固定间隔，不发生卷绕。
因此 `F_M(log m)=1_(m<=M)` 精确成立，包括 m=M、M+1。

若 `hat F_M(k)` 是周期 Fourier 系数，区间积分和盒核的显式
Fourier 系数给出（k!=0）

\[
 |\widehat F_M(k)|\le
 C\min(1,|k|^{-1})\min\left(1,\frac P{h|k|}\right),
 \qquad |\widehat F_M(0)|\le1.
\]

故级数绝对收敛，并且

\[
 \sum_{k\in\mathbb Z}|\widehat F_M(k)|
 \le C(1+\log(P/h))\le C\log(2R).
 \tag{cutoff-l1}
\]

该 Fourier 级数确实等于 F_M：其 Fejér 均值用正的、积分为1的
有限几何级数平方核表示，对连续周期函数一致收敛；绝对收敛的
同一系数级数，其 Fejér 均值也一致趋向原级数。因此

\[
 \boldsymbol1_{m\le M}=\sum_{k\in\mathbb Z}\widehat F_M(k)m^{2\pi ik/P}
 \qquad(1\le m\le R).
 \tag{cutoff-exact}
\]

取 R=8Y。由 (balanced-range)，每个矩形中的乘积满足
`1<=ab<4AB<8U<=8Y`。将 M=M_g 与 M=U-1 的两个展开相减，即有

\[
 \boxed{H_g(ab)=\sum_k\omega_k a^{i t_k}b^{i t_k},
 \quad t_k=2\pi k/P,\quad\sum_k|\omega_k|\le C\log(2Y).}
 \tag{hard-separated}
\]

有限 a,b,n,v 和可以与绝对收敛的 k 和交换。
纯虚幂的范数为1，故不会因 k 很大而损失任何大小控制。
这不需要把硬截断近似成光滑截断，也不需要估计 Perron 余项。

## 4. 真实 profile 和 g 条件确实适配矩形系数

在每组中，真实光滑权重是

\[
 F_g(ab)=(AB/U)^{s-1-\beta}(a/A)^{s-1-\beta}(b/B)^{s-1-\beta}
 P_1\!\left(1-\frac{\log g+\log a+\log b}{\log Y}\right).
\]

将固定多项式展开，只产生有限个 `f(a)j(b)` 项：
系数为 `log g/log Y` 的固定多项式，a,b 因子为各自对数幂与所写
复幂的乘积。由于 `g<=Y`、`a,b<=8Y`、`Y>=2` 和
`1/4<AB/U<2`，所有归一化权重在完整矩形上有固定界。
矩形外的 profile 参数不一定在[0,1]，但仍在固定有界区间；
这里用的是多项式在该固定区间上的界，没有越域使用 B_j。

结合 (hard-separated)，每个实际组成为绝对系数和为
`O_P(log(2Y))` 的矩形和组合，矩形和具有形状

\[
 \sum_{\substack{v\in B_V\\gv\le Y}}q_v
 \sum_{b\in B_B,(b,v)=1}j(b)\boldsymbol1_{(b,g)=1}
 \sum_{n\in B_N}\sum_{a\in B_A,(a,v)=1}
 c(a,n)e(\kappa n\bar a\bar b/v).
 \tag{rectangle-actual}
\]

这里 `(a,g)=1` 已作为零系数条件放在 c(a,n) 中；
c(a,n) **不依赖 b 或 v**。j(b) 包含该组 d_B(b)，c(a,n) 包含
d_A(a)、真实 r_n、移位权重和 k 的纯虚幂。
对任意 rho>0，二者范数分别由 `C_rho Y^rho` 和
`C_rho (NY)^rho` 控制，统一于 k、g、Im s 及复移位。
这里沿用伴随证明对无上界 N 的单独移位损失控制。

对外层系数取范数，只把约数界损失提出；v 的实际子区间可在
取绝对值后扩大。g 过滤没有变成 DI 定理不允许的内层 v 依赖。
负相位 kappa=-1 通过将内层系数整体共轭转为正相位的同一界。

## 5. 已发表 DI 定理的逐变量映射

将 DI84 Lemma 1 的固定整数参数取1，外层模数变量对应此处 v，
外层逆元因子对应 b，两个内层变量对应 n,a。各 dyadic 系数向
`1<=n<2N, 1<=a<2A` 零延拓，外层范围扩大到 v<2V、b<2B。
其上界是

\[
 \begin{split}
 &(NABV)^{1/2+\rho}\big\{(BV)^{1/2}\\
 &\qquad +(A+N)^{1/4}
 [BV(N+A)(V+A^2)+NA^2B^2]^{1/4}\big\}.
 \end{split}
 \tag{DI-map}
\]

所有被扩大范围的常数2只改变统一常数。由 AB 与 U 相比在
固定常数之间，得到 Conrey Lemma 9 所写的实际尺度

\[
 \begin{split}
 \mathfrak B(A,N,U,V)=(NUV)^{1/2}\big\{(UV/A)^{1/2}\\
 +(A+N)^{1/4}[UV A^{-1}(N+A)(V+A^2)+NU^2]^{1/4}\big\}.
 \end{split}
\]

因此每个组的范数至多 `C_epsilon (NY)^epsilon mathfrak B`。
所有对数、约数和 DI 的 rho 损失先取 epsilon/100 等独立小量；
有限组数的对数损失也可包含进去。无需对复幂权重求导，故本节
不会额外损失 Im s 的幂次；如需与 Type I 合并，可放宽乘以1+|s|。

## 6. 七个单项式的尺度核对

四次方后先用 `(x+y)^4<=8(x^4+y^4)` 和
`(A+N)^2<=2(A^2+N^2)`，逐项展开得到

\[
 \mathfrak B^4\le C\sum_{(a,n,u,v)\in\mathcal F} A^aN^nU^uV^v,
\]

其中七元集合为

\[
 \mathcal F=\{(-2,2,4,4),(-1,4,3,4),(1,4,3,3),
 (1,2,3,4),(3,2,3,3),(0,4,4,2),(1,3,4,2)\}.
\]

此处小写 a,n,u,v 仅是七个指数，不是求和整数或 zeta 移位。
设 M=max(TN,UV)。若 a>=0，用 A<=sqrt(2U)；若 a<0，用
`A>U^(1/4)/2`。分别令 h=a/2 或 h=a/4，即有

\[
 A^aN^nU^uV^v
 \le C M^4 T^{-n}Y^{2n+u+v-8+h}.
 \tag{monomial-bound}
\]

因为 n<=4，`(TN)^n(UV)^(4-n)<=M^4`；其余两份 U,V 幂次为
`n+u-4+h`、`n+v-4`，逐项非负，才可使用 U,V<=Y。

以下是每项除去 M^4 后的幂次，以及与目标 `T^(-2)Y^(7/2)`
比较的比值：

| (a,n,u,v) | 上界单项式 | 比值 |
|---|---|---|
| (-2,2,4,4) | T^(-2)Y^(7/2) | 1 |
| (-1,4,3,4) | T^(-4)Y^(27/4) | T^(-2)Y^(13/4) |
| (1,4,3,3) | T^(-4)Y^(13/2) | T^(-2)Y^3 |
| (1,2,3,4) | T^(-2)Y^(7/2) | 1 |
| (3,2,3,3) | T^(-2)Y^(7/2) | 1 |
| (0,4,4,2) | T^(-4)Y^6 | T^(-2)Y^(5/2) |
| (1,3,4,2) | T^(-3)Y^(9/2) | T^(-1)Y |

在 `Y<=T^(8/13)` 时比值全部至多1（T>=1）。因此

\[
 \boxed{|S_{\mathrm{II}}|\le
 C_\epsilon(NY)^\epsilon\max(TN,UV)T^{-1/2}Y^{7/8}.}
 \tag{TypeII-actual}
\]

该估计包含真实截断、系数和所有 g；它是本文使用已发表 DI 定理
后导出的实际有限块结论，不是未经适配地粘贴 Conrey Lemma 8。

## 7. 接回全部实际对偶余项

乘回 `N^(-c)(UV)^(c-1)` 的真实尺度，再用伴随文档第6节的
max(TN,UV) 两分支计算，得到

\[
 |\mathcal A_{\mathrm{II}}|
 \le C_\epsilon(TN)^\epsilon Y^{2\eta}T^cN^{-\eta}
 T^{-1/2}Y^{7/8}.
\]

与 (A-I-line) 合并，实际全部算术块满足

\[
 \boxed{|\mathcal A_\kappa|
 \le C_\epsilon(1+|s|)(TN)^\epsilon Y^{2\eta}T^cN^{-\eta}
 (T^{-1/2}Y^{7/8}+T^{-1}Y^{7/4}).}
 \tag{A-full-actual}
\]

取独立的 `0<epsilon<eta`，使用 #513 已证明的加权核界和
精确四相位移线（合计留数为0），然后对真正 g,N,U,V 求和，得到

\[
 \boxed{|\mathcal E|\le C_{\epsilon,\eta}(1+\log Y)^3
 Y^{2\eta}T^{5/2+\eta+\epsilon}\Delta^{-7/2}(T/\Delta)^\eta
 (T^{1/2}Y^{7/8}+Y^{7/4}).}
 \tag{E-full-actual}
\]

这里 N 和为 `sum_(j>=0)2^(j(epsilon-eta))`，g 的1/g和与 U,V
块数给出对数三次幂。所有换序和支配现在作用于真实有限块及核，
不是另设的抽象误差函数。

当 `Y<=T^theta`、固定 theta<4/7 时，`Y<=T^(8/13)` 自动满足。
代入 `Delta=T^(1-delta)`，两份 T 的主幂分别为
`-1/2+7theta/8` 和 `-1+7theta/4`，共同正损失为
`7delta/2+(1+delta+2theta)eta+epsilon`。
先固定 theta，再固定足够小的正 delta、eta 与 epsilon<eta，
两者均有严格负余量；对数可吸收。因此 **实际 E=o(1)**，
在所需闭复移位域上一致。局部一致的支配给出全纯性，半径1/2
Cauchy 圆保证所需 `(1+k partial_a)(1+k partial_b)E` 同样为 o(1)。

## 8. 与 #512 的实际 Gaussian 主项接合

保持既定 `theta=571/1000`、`Y=floor(T^theta)`、`R=6/5`、
`k=51/50` 及 `P(x)=(84x+15x^3+x^5)/100`，不改 profile。
[实际 Gaussian 主项证明](2026-08-31-conrey-gaussian-profile-main-term.md)
已经得到真实微分后 Gaussian 均方等于

\[
 C_{P,R,k,\theta}+
 [(1+k\partial_a)(1+k\partial_b)\mathcal E]_{a=b=-R}+o(1),
\]

其中 C 就是既有 `conreyExplicitMeanSquareIntegral` 的实际积分值，
不是新定义的代理常数。将本节对真实 E 的一致界代入，便得到
该 Gaussian 均方的纸面渐近 `C_{P,R,k,theta}+o(1)`。

这一步明确使用已发表 DI 和 Weil 定理。它没有完成这些深输入
及整条链的原生 Lean 证明。同一参数的 [T,2T] 去平滑见 companion，
但到固定全局参数 [0,T] 所需均方的转移，以及最终简单零点比例定理仍未完成。
这些是后续实际工作；本节不把它们隐藏在“均方已完成”的表述中。
