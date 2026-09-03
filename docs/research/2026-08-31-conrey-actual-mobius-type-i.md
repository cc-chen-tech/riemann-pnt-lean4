# Conrey 实际对偶块：有限 Möbius 分解与短因子 Type I 估计

这里对 #513 已接出的真实有限算术块做估计，不增加一个假设块
估计成立的 Lean 接口。先逐项证明有限 Vaughan 恒等式，保留 g
的互素限制，再用有限 Fourier 补全和经典 Weil 界控制短因子项。
最后把该估计接回已经证明的实际解析核。

**证明边界：**本文明确使用经典完全 Kloosterman 和的 Weil 定理。
该定理在这里是引用的已发表数学输入，不是本任务独立重证或已
原生化到 Lean 的结果。长双线性项不由本节处理，见
[DI 适配与实际余项接合](2026-08-31-conrey-actual-di-remainder.md)。
两篇合用的结论仍依赖明确引用的深定理，不是原生 Lean 或严格 >2/5 的完成。

源结构为 [Conrey 1989, pp.22–25, (79)–(85)、(98)–(99)](https://aimath.org/~kaur/publications/24.pdf)。
本节补出带 g 限制的补全、端点、权重导数和无限 N 的一致损失。
源基线为 #513 的 `d85f0db6`，其冻结分支不改。

## 1. 实际块、归一化与移位一致性

沿用 [实际 dyadic 块](2026-08-31-conrey-dual-dyadic-contour.md)：
`L=log T`，`2<=Y<=T` 为整数，`alpha=a/L, beta=b/L`，
`gamma=alpha+beta`，`|a|,|b|<=3`。固定 `0<eta<=1/8`，
`L>=max(24,16/eta)`，`s=c+it`，c 按 UV>=TN 取 eta，否则取1+eta。
N,U,V 均为从1开始的二进尺度，`B_X=[X,2X)` 取整数点。

记 `d_gamma(n)=sum_(m|n)m^gamma`，实际系数为
`c_j(n)=mu(n)P_j(log(Y/n)/log Y)`；P_j 是固定实多项式。
以下常数可依赖 P_j、eta 和单独指定的小损失，但不依赖
T、N、U、V、g、Im s 或移位。

将 (block-actual) 中的函数另记为 `mathcal A_kappa`，kappa=+1,-1。
对 `1<=g<=Y`，使用**带条件的精确式**

\[
 \mu(gu)=\mu(g)\mu(u)\boldsymbol1_{(u,g)=1}.
 \tag{mu-g}
\]

这是素因子分解的直接结果：g 非平方自由时两边均为0；否则
u 含平方因子或与 g 共享素因子时两边也均为0，其余情况乘法成立。

定义

\[
 \begin{split}
 r_n&=d_\gamma(n)(n/N)^{-s},\\
 F_g(x)&=(x/U)^{s-1-\beta}
 P_1\!\left(\frac{\log(Y/(gx))}{\log Y}\right),\\
 q_v&=\mu(v)\boldsymbol1_{(v,g)=1}(v/V)^{s-1-\alpha}
 P_2\!\left(\frac{\log(Y/(gv))}{\log Y}\right).
 \end{split}
\]

F_g 只在 `U<=x<=min(2U,Y/g)` 上使用；q_v 只在
`v in B_V, gv<=Y` 上使用。于是

\[
 \begin{split}
 \mathcal A_\kappa&=\mu(g)^2N^{-s}U^{s-1-\beta}V^{s-1-\alpha}S_\kappa,\\
 S_\kappa&=\sum_{n\in B_N}r_n
 \sum_{\substack{v\in B_V\\gv\le Y}}q_v
 \sum_{\substack{u\in B_U\\gu\le Y,\ (u,vg)=1}}
 \mu(u)F_g(u)e(\kappa n\bar u/v).
 \end{split}
 \tag{normalization}
\]

所有求和有限；v=1 时逆元取0，相位定义为1。
外部因子的范数至多 `C N^(-c)(UV)^(c-1)`，不是 `(UV)^(1-c)`。
这里 `U,V<=Y` 且 `|alpha|,|beta|<=3/L`，故移位尺度只给统一常数。

对任意 rho>0，当 T 足够大（允许阈值依赖 rho）时，

\[
 |r_n|\le C_\rho N^\rho,\quad |q_v|\le C,
 \quad |F_g(x)|\le C,\quad |F_g'(x)|\le C(1+|s|)/x.
 \tag{actual-weights}
\]

后两式来自 `1<=x/U<=2`、profile 变量在[0,1]、`log Y>=log2`，
以及对所写 F_g 直接求导。第一式需注意 N 无上界：
`|d_gamma(n)|<=tau(n)n^max(Re gamma,0)`。先令 `|gamma|<=rho/2`，
再用 `tau(n)<=C_rho n^(rho/2)`，而非错误地把 n 的移位幂当作
固定常数。约数界的初等证明是：大素数 p 上 `e+1<=p^(rho e/2)`，
有限个小素数上取 `(e+1)p^(-rho e/2)` 的有限上确界，再相乘。
对固定阶约数函数使用相同论证。

这些论证也在 `|a|,|b|<4` 的紧子双圆盘上局部一致，只需增大
T 的阈值。系数和切分集合均不依赖复移位。

## 2. 完全有限的 Vaughan 恒等式及精确支撑

对正整数上的算术函数用 Dirichlet 卷积 `*`，令 1 为恒1函数，
e 为卷积单位 `e(1)=1, e(n)=0 (n>1)`。全部系数恒等式只涉及
某个整数的有限约数和，不需要 Dirichlet 级数收敛。

固定 `W=U^(1/4)>=1`，取 `m(n)=mu(n) 1_(n<=W)`，并令
`D=e-1*m`。由 `mu*1=e`，直接展开得到

\[
 \boxed{\mu=\mu*D*D+2m-1*m*m.}
 \tag{Vaughan-finite}
\]

具体地 `mu*(e-1*m)*(e-1*m)=mu-2m+1*m*m`。
对 n<=W，D(n)=0（包括 n=1）；对 n>W，

\[
 D(n)=-\sum_{\substack{d\mid n\\d\le W}}\mu(d).
\]

所以三项分别为

\[
 \begin{split}
 v_1(u)&=\sum_{\substack{a b h=u\\a>W,\ b>W}}D(a)D(b)\mu(h),\\
 v_2(u)&=2\mu(u)\boldsymbol1_{u\le W},\\
 v_3(u)&=-\sum_{ab=u}\lambda_W(a),\qquad
 \lambda_W(a)=\sum_{\substack{d e=a\\d,e\le W}}\mu(d)\mu(e).
 \end{split}
 \tag{Vaughan-pieces}
\]

这里 `|D(n)|<=tau(n)`、`|lambda_W(a)|<=tau(a)`，且 lambda_W
支撑在 `a<=W^2=U^(1/2)`。严格的 `a>W,b>W` 与 m 的 `<=W`
互补；整数 W 时也不重复端点。

将上述三项逐项代入 (normalization) 得到真实有限和
`S=S_1+S_2+S_3`，每项仍带 `(u,vg)=1`。在 u=ab 的项中该条件
等价于 `(a,vg)=(b,vg)=1`，不能删掉 g 或把它只留在外层。

因为尺度 U 是二进数，U>=2 时 `W<U`，所以 S_2=0；U=1 时仅
可能有 u=1。保留较粗但统一的界也有

\[
 |S_2|\le C_\rho(NY)^\rho NWV.
 \tag{short-supported}
\]

## 3. 完全 Kloosterman 和：唯一显式外部输入

定义

\[
 K_v(h,l)=\sum_{x\bmod v}^{*}e((hx+l\bar x)/v).
\]

使用经典 Weil 定理；精确的所有整数模数版本见作者公开的
[Iwaniec–Kowalski, Corollary 11.12, (11.16), p.280](https://people.math.ethz.ch/~kowalski/ik-ant-exp-sums.pdf)，
也正是 Conrey p.25 的 (98) 所调用的完全和输入：

\[
 |K_v(h,l)|\le\tau(v)v^{1/2}(h,l,v)^{1/2}.
 \tag{Weil-input}
\]

v=1 时约定该和为1，公式仍成立。下面从这个**完全和定理**
推导实际带 g 限制的不完全和；不把原文 (98) 整体当成未检验输入。
本文不证明 (Weil-input) 的代数几何基础，也不将其添加为 Lean 公理。

## 4. 有限 Fourier 补全与 g 的互素限制

先设 v>=2，J 是连续整数段且 `#J<=v`，故模 v 不重复。设 H_J 是 J 在
`Z/vZ` 上的示性函数，并取
`Hhat(h)=sum_(x mod v) H_J(x)e(-hx/v)`。有限 Fourier 反演给出

\[
 \sum_{b\in J,(b,v)=1}e(l\bar b/v)
 =\frac1v\sum_{h\bmod v}\widehat H_J(h)K_v(h,l).
 \tag{completion-exact}
\]

这只是有限群上单位根正交关系。几何级数直接给出
`|Hhat(h)|<=min(#J,1/|sin(pi h/v)|)`；h=0 项为 #J<=v。
对 `1<=h<=v/2` 用 `sin(pi h/v)>=2h/v`，并将 h 与 v-h 配对，得

\[
 \frac1v\sum_h|\widehat H_J(h)|\le C\log(2v).
\]

结合 (Weil-input) 和 `(h,l,v)<=(l,v)`，得到短段的上界
`C tau(v) sqrt(v) sqrt((l,v)) log(2v)`。
任意实区间 I 长度为 H，将其中整数顺序分成完整 v 周期和一个
余段，即有

\[
 \left|\sum_{b\in I\cap\mathbb Z,(b,v)=1}e(l\bar b/v)\right|
 \le C\tau(v)\sqrt v\sqrt{(l,v)}\log(2v)(1+H/v).
 \tag{incomplete}
\]

现在使用 `1_(b,g)=1=sum_(d|g,d|b)mu(d)`。若 `(d,v)>1` 则没有
满足 `(b,v)=1` 的 b；其余项写 b=dc，真实相位变为
`e(l dbar cbar/v)`，区间长度 H/d，且 `(l dbar,v)=(l,v)`。
因此

\[
 \boxed{
 \left|\sum_{b\in I\cap\mathbb Z,(b,vg)=1}e(l\bar b/v)\right|
 \le C\tau(g)\tau(v)\sqrt v\sqrt{(l,v)}\log(2v)(1+H/v).}
 \tag{incomplete-g}
\]

v=1 的情况直接用整数个数不超过 H+1，增大同一个绝对常数即可。
端点开闭仅改变至多两个项，已经包含在常数中。
任意子区间也有同一形式的界，因此可以用于精确 Abel 分部求和。

## 5. 实际短因子项：只损失一次 1+|s|

将 S_3 中 a<=W 的部分记为 `S_{3,short}`；a>W 留在双线性部分。
对固定 a,n,v，b 的**真正**范围是

\[
 I_a=\{b\in\mathbb N: U\le ab<2U,\quad gab\le Y\}.
 \tag{actual-interval}
\]

它是一个整数段，实区间长度至多 U/a；末端 `gab=Y` 按原式保留。
仅当 `(a,vg)=1` 时有贡献；此时 `l=kappa n abar mod v` 满足
`(l,v)=(n,v)`。实际权重为 F_g(ab)，并且

\[
 |F_g(ab)|\le C,\qquad
 \left|\frac d{db}F_g(ab)\right|\le C(1+|s|)/b.
\]

积分区间的端点比不超过2，所以总变差至多 `C(1+|s|)`。
先对每个前缀应用 (incomplete-g)，再作有限 Abel 分部求和，得

\[
 \left|\sum_{b\in I_a,(b,vg)=1}F_g(ab)e(\kappa n\bar a\bar b/v)\right|
 \le C(1+|s|)\tau(g)\tau(v)\sqrt v\sqrt{(n,v)}
 \log(2v)\left(1+\frac U{av}\right).
 \tag{weighted-actual}
\]

这里没有对硬截断示性函数求导；截断已经放进整数段 I_a。
也没有假定 Möbius 系数是光滑函数；被求导的仅是已写出的 F_g。

用 `|lambda_W(a)|<=tau(a)`、
`sum_(a<=W)tau(a)<=C W log(2W)` 和
`sum_(a<=W)tau(a)/a<=C log^2(2W)`，再对 a,n,v 求和。
所需 gcd 平均可以初等证明：由
`(n,v)=sum_(d|n,d|v)phi(d)`，且 d<=2min(N,V)，
两个 dyadic 段中 d 的倍数个数分别至多3N/d与3V/d，得到

\[
 \sum_{n\in B_N}\sum_{v\in B_V}(n,v)
 \le9NV\sum_{d\le2\min(N,V)}\frac{\varphi(d)}{d^2}
 \le C NV\log(2\min(N,V)).
 \tag{gcd-average}
\]

因 `sqrt((n,v))<=(n,v)`，这也控制 (weighted-actual) 所需平均。
将所有约数与对数损失以独立的小参数分配，得到对任意 epsilon>0
的实际估计

\[
 \boxed{|S_{3,\mathrm{short}}|
 \le C_\epsilon(1+|s|)(NY)^\epsilon
 \left(N U^{1/4}V^{3/2}+NUV^{1/2}\right).}
 \tag{TypeI-actual}
\]

例如对有限个约数/对数因子先各取 epsilon/100，并在
(actual-weights) 中用同样小的 rho，再增大 T 阈值；总损失不超过
epsilon。此处 epsilon 独立于 eta，不能为了便于书写将二者混同。

非空块满足 U,V<=Y/g<=Y，所以

\[
 |S_{3,\mathrm{short}}|+|S_2|
 \le C_\epsilon(1+|s|)(NY)^\epsilon N Y^{7/4}.
 \tag{TypeI-Y}
\]

S_2 的粗界由 `WV<=Y^(5/4)<=Y^(7/4)` 包含在内。
这是真实 Vaughan 两部分的估计，不是对全部 S 的估计。

## 6. 接回原尺度与两条实际积分直线

令 `mathcal A_I` 为 (normalization) 外部因子乘
`S_2+S_{3,short}`。设 M=max(TN,UV)，则 `N<=M/T`。
按 #513 的选线，

\[
 N^{-c}(UV)^{c-1}M\le Y^{2\eta}T^cN^{-\eta}.
\]

确实，UV>=TN 时左边为 `N^(-eta)(UV)^eta`；另一侧为
`T N^(-eta)(UV)^eta`。分别用 `(UV)^eta<=Y^(2eta)`、
`1<=T^eta` 即可。故

\[
 \boxed{|\mathcal A_I(N,U,V,g;s)|
 \le C_\epsilon(1+|s|)(TN)^\epsilon
 Y^{2\eta}T^cN^{-\eta}\,T^{-1}Y^{7/4}.}
 \tag{A-I-line}
\]

这给出 Conrey Lemma 8 中真正的短因子 `T^(-1)Y^(7/4)` 分支。
`T^(-1/2)Y^(7/8)` 的双线性分支尚未在本文证明。

## 7. 这部分实际对偶积分已经可求和

定义 E_I 为 #513 的 E-shifted 中把每个实际块替换为 A_I 后的
四相位积分和；相位标签及外部1/g不变。取 `0<epsilon<eta`。
由已证明的加权核界和 (A-I-line)，每个积分块的范数至多

\[
 C_\epsilon Y^{7/4+2\eta}N^{\epsilon-\eta}
 T^{5/2+\eta+\epsilon}\Delta^{-7/2}(T/\Delta)^\eta.
 \tag{I-integrated}
\]

理由是 `(T/Delta)^c` 随 c 增大，故可用最大 c=1+eta。
这一步是将真正算术块界代入真正核界，不是引入任意误差包络。

N 的二进和为 `1/(1-2^(epsilon-eta))`，确实收敛；g 的1/g和
至多 `1+log Y`，每个 g 对应 U,V 的选择数至多
`C(1+log Y)^2`。因此

\[
 \boxed{|\mathcal E_I|\le
 C_{\epsilon,\eta}(1+\log Y)^3Y^{7/4+2\eta}
 T^{5/2+\eta+\epsilon}\Delta^{-7/2}(T/\Delta)^\eta.}
 \tag{E-I-actual}
\]

对任意固定 `theta<4/7`、`Y<=T^theta`，令
`Delta=T^(1-delta)` 后，T 的总幂次（尚未吸收对数）为

\[
 -1+\frac{7\theta}{4}
 +\frac{7\delta}{2}+(1+\delta+2\theta)\eta+\epsilon.
\]

先固定 theta，再选正 delta、eta 和 `0<epsilon<eta` 足够小，
便有严格负余量；对数三次幂仍可吸收。因此 **E_I=o(1)**，
在此前复移位域上一致。既定 `theta=571/1000` 严格小于4/7，
适用同一结论；不需要改动已有 profile 或另调指数目标。

有限块全纯，且上述无限求和支配在紧子双圆盘上统一；故 E_I
全纯。取既定负移位中心的半径1/2 Cauchy 圆，所需混合微分的
界只乘 `5776/625`，同样为 o(1)。

## 8. 新的准确剩项

由有限 Vaughan 恒等式，现在原实际对偶项精确分成
`E=E_I+E_II`。E_II 由 v_1 的双线性项和 v_3 中 a>W 的项构成，
保留全部 g 互素限制、乘积截断和两个逆元扭转。
E_I 的实际一致衰减在本文由明确引用的 Weil 定理推出；E_II
未在本节估计。既有完整 E 的绝对尾部重组与上述 E_I 的绝对求和
保证这个差项定义合法，不需要在左线展开无限 Dirichlet 级数。

本节交出的剩项是 E_II 的 DI 算术消去和准确矩形化，不是增加
“假设 Type II 已小”的接口。同一检查点的 companion 对此继续
给出实际推导，并明确引用 DI84 Lemma 1。Weil、DI 及纸面步骤
的原生 Lean 验证仍欠缺；完整非平滑长均方和最终简单零点比例
不能宣布完成。
