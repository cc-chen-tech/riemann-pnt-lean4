# Conrey 的 DI 输入：系数能量、Poisson 补全和零频项的展开证明

先说结论：本节证明实际 DI84 Lemma 1 应用之前的算术与 Fourier
步骤，包括精确平方展开、系数二次能量、Poisson 补全、零频和尾项。
随后从 **DI82 Theorem 11 这一仍未自证的谱输入** 推导所需的 DI84
界，不再把 DI84 Lemma 1 和 DI82 Theorem 12 整体作为未展开黑箱。
这不是 DI 谱估计的完整自证，也不是新增 Lean 定理或条件接口。

本篇在冻结源 `6337c0a62a7ae10ea61e1d78bfcfbf3887bc70f8` 之后
独立交付，只新增本篇 Markdown。前一篇已经给出实际完全和的
[Weil 界纸面证明](2026-08-31-conrey-prime-weil-stepanov-proof.md)；
本篇仍不宣布完整 Conrey 原生证明完成。

另一个核对结果是：DI82 Theorem 12 确有2019年勘误，但本任务
对应其 S=1 的情形，修正项不变。第7节从实际变量解释这点。

## 1. 同一个实际矩形和

以下 C,D,U,V 为正整数，`e(t)=exp(2 pi i t)`。
令 `a(u,v)` 为 `1<=u<=U,1<=v<=V` 上的任意复系数，模不超过1。
研究 dyadic 外层和

\[
 \mathcal T=
 \sum_{\substack{C<c\le2C,\ D<d\le2D\\(c,d)=1}}
 \left|\sum_{u\le U}\sum_{\substack{v\le V\\(v,c)=1}}
       a(u,v)e\left(\frac{u\overline{vd}}c\right)\right|.
 \tag{actual-rectangle}
\]

所有求和变量均为正整数，除非另有说明。逆元总是在分母 c 下取。
实际 Conrey 映射为：这里 `c,d,u,v` 分别对应之前实际矩形中的
外层模数、外层逆元因子、n、a；也就是尺度约为
`C=V_actual,D=B_actual,U=N_actual,V=A_actual`。
半开 dyadic 端点差异和系数零延拓只需用常数倍参数覆盖。
外层系数先按前篇方式提出范数；内层 a(u,v) 不依赖 c 或 d。
乘积硬截断、g 互素限制和 profile 分离仍沿用
[实际 DI 余项证明](2026-08-31-conrey-actual-di-remainder.md)，不重新放宽这些条件。

选固定非负 `w_1,w_2 in C_c^infinity((1/2,3))`，在[1,2]上至少为1。
例如先取正的光滑 bump，再在覆盖该紧区间的有限个平移上相加并放大。
设 `G(c,d)=w_1(c/C)w_2(d/D)`。其导数常数此后固定。
Cauchy--Schwarz 及 G 的主化性质给出

\[
 \mathcal T^2\le CD\,\mathcal Q,\qquad
 \mathcal Q=\sum_{(c,d)=1}G(c,d)
 \left|\sum_{u\le U}\sum_{v\le V,(v,c)=1}
 a(u,v)e(u\overline{vd}/c)\right|^2.
 \tag{cauchy-before-expansion}
\]

这里 Q 是非负实数；平滑外层只扩大非负的平方和，没有主化带符号的和。
若某块需包含左端点 C 或 D，外层项数改用 `4CD`，所有后续式只改
绝对常数。这样也覆盖 c=1 或 d=1 的单点，不漏掉前缀求和的起点。

## 2. 精确系数及 determinant-zero 项

定义有限系数

\[
 b(n,r)=\sum_{\substack{v_1v_2=r\\v_1,v_2\le V}}
 \sum_{\substack{u_1,u_2\le U\\u_1v_2-u_2v_1=n}}
 a(u_1,v_1)\overline{a(u_2,v_2)}.
 \tag{determinant-coefficient}
\]

其支撑满足 `1<=r<=V^2, |n|<UV`。直接展开平方并合并相位，得到

\[
 \mathcal Q=
 \sum_{r\le V^2}\sum_{|n|<UV}b(n,r)
 \sum_{\substack{c,d\ge1\\(c,rd)=1}}G(c,d)
     e\left(\frac{n\overline{rd}}c\right).
 \tag{exact-square}
\]

因为 `(v_1v_2d,c)=1` 时
`u_1 overline(v_1d)-u_2 overline(v_2d)` 模 c 等于
`(u_1v_2-u_2v_1) overline(v_1v_2d)`。
系数 b 完全独立于 c,d。式中 n 有正、负、零三个部分，不能只留正 n。

n=0 的系数总质量满足一个可显式计数的上界。设 H_k 为第 k 个
调和数。将 `v_1=h alpha,v_2=h beta` 化为 `(alpha,beta)=1`，
零 determinant 条件等价于 `u_1=t alpha,u_2=t beta`。
记 m=max(alpha,beta)，c_m 为有序正互素对最大值为 m 的数量。
则 c_1=1，m>=2 时 c_m=2 phi(m)，尤其 c_m<=2m。于是

\[
 \begin{aligned}
 \sum_r|b(0,r)|
 &\le\#\{u_1v_2=u_2v_1\}\\
 &=\sum_{m\le\min(U,V)}c_m
       \lfloor U/m\rfloor\lfloor V/m\rfloor
 \le2UVH_{\min(U,V)}.
 \end{aligned}
 \tag{determinant-zero-mass}
\]

外层 G 的总质量为 `O_w(CD)`，所以 (exact-square) 的 n=0
部分绝对值为 `O_w(CD UV H_min(U,V))`。代回 Cauchy 后，它对 T
贡献至多 `O_w(CD sqrt(UV H_min(U,V)))`。
这与下一节的 Fourier 零频 m=0 是两种不同的零项，不能混淆。

## 3. b(n,r) 的二次能量：保留 gcd 后逐项计数

固定 v_1,v_2，令 `B_(v_1,v_2)(n)` 为 (determinant-coefficient)
中的内层和。由 |a|<=1，平方展开取模得

\[
 \sum_n|B_{v_1,v_2}(n)|^2
 \le\#\{u_1v_2-u_2v_1=u_3v_2-u_4v_1\}.
\]

设 `h=gcd(v_1,v_2), alpha=v_1/h,beta=v_2/h`。
因 alpha,beta 互素，上式中的等式精确等价于存在整数 k 使
`u_1-u_3=k alpha,u_2-u_4=k beta`。因此其右端恰为

\[
 \sum_{k\in\mathbb Z}(U-|k\alpha|)_+(U-|k\beta|)_+
 \le U^2\left(1+\frac{2Uh}{\max(v_1,v_2)}\right),
 \tag{exact-energy-count}
\]

其中 x_+=max(x,0)。固定 k 时两个有序差值的解数各为所写的三角因子；
非零项要求 `|k|<U/max(alpha,beta)`，给出最后的界。

再次按互素对及其最大值 m 分组，

\[
 \sum_{v_1,v_2\le V}\frac{\gcd(v_1,v_2)}{\max(v_1,v_2)}
 =\sum_{m\le V}\frac{c_m}{m}\lfloor V/m\rfloor
 \le2VH_V.
\]

设 `D_V=max_(1<=r<=V^2) tau(r)`。对 b(n,r) 中至多 tau(r)
个有序分解 `v_1v_2=r` 用 Cauchy，再求和，得到实际系数界

\[
 \boxed{\|b\|_2^2\le D_V U^2(V^2+4UVH_V).}
 \tag{coefficient-energy}
\]

范数在所有 n,r 上求和，因此也控制删掉 n=0 后及任何 dyadic
子块的范数。通常记号下，对任意 eta>0，可写成
`||b||_2^2 <<_eta (UV)^eta U^2 V(U+V)`。
这里仅用了初等约数界和调和和界：对足够大的素数 l 有
`j+1<=2^j<=l^(eta j)`，剩下有限个小素数的指数比值有有限上确界，
相乘即得 tau(r)<<_eta r^eta；调和和不超过1+log V。
分别缩小 eta 即吸收所有这些损失。

## 4. 精确 Poisson 补全、Fourier 零频和可控尾项

本节先对任意有限支撑复系数 b(n,r) 工作，支撑为
`0<|n|<=N,1<=r<=R`，N,R 正整数。**不包含 n=0**。
记其未完成和为

\[
 \mathcal H=\sum_{n,r}b(n,r)
 \sum_{(c,rd)=1}w_1(c/C)w_2(d/D)e(n\overline{rd}/c).
\]

采用 Fourier 约定 `hat w(xi)=integral w(t)e(-xi t)dt`。
对每个剩余类 t 模 c，周期化的 Fourier 展开为

\[
 \sum_{l\in\mathbb Z}w_2((t+cl)/D)
 =\frac Dc\sum_{m\in\mathbb Z}\widehat w_2(mD/c)e(mt/c).
 \tag{progression-poisson}
\]

这可以直接证明：左边是光滑 c 周期函数，对一个周期积分并作
变量替换，其第 m 个 Fourier 系数就是 `(D/c)hat w_2(mD/c)`。
分部积分给系数任意次衰减，故级数绝对、一致收敛；由 Fejer 核的
一致逼近或 Fourier 系数唯一性，它等于原周期化函数。
左边 d 的负值或零不会产生新项，因为 w_2 支撑在正半轴。

将 (progression-poisson) 对单位剩余类求和，再换元 `x=rt mod c`，
得到准确归一化的补全式

\[
 \boxed{\mathcal H=D\sum_{n,r}b(n,r)
 \sum_{(c,r)=1}\frac{w_1(c/C)}c
 \sum_{m\in\mathbb Z}\widehat w_2(mD/c)
          K_c(m\bar r,n).}
 \tag{completed-actual}
\]

其中 `K_c(A,B)=sum_(x mod c,unit)e((Ax+B/x)/c)` 是前篇实际完全和。
系数 m 与 n 的位置、r 的模逆、D/c 因子都在式中保留。
这不是有限域 F_(p^k) 的求和。所有 c,n,r 范围有限，m 级数绝对收敛，
故这些求和的交换有依据。

### 4.1 Fourier 零频的实际估计

m=0 时 `K_c(0,n)=c_c(n)` 为 Ramanujan 和，与 r 无关。
由单位示性函数的 Möbius 展开和有限几何级数，精确得到

\[
 c_c(n)=\sum_{h\mid(c,n)}h\mu(c/h).
 \tag{ramanujan-exact}
\]

具体地，对 x 模 c 插入 `sum_(d|gcd(x,c))mu(d)`；令 x=dy，
内层为 c/d 或0，非零条件正是 c/d 整除 n，再设 h=c/d。
当 n!=0，因 c<=3C，

\[
 \sum_{c\le3C}\frac{|c_c(n)|}{c}
 \le\sum_{h\mid |n|}\sum_{k\le3C/h}\frac1k
 \le\tau(|n|)H_{\lfloor3C\rfloor}.
\]

去掉 `(c,r)=1` 仅在取绝对值之后进行。记
`T_N=max_(1<=n<=N)tau(n)`。于是 Fourier 零频 H_0 满足

\[
 |\mathcal H_0|\le
 D|\widehat w_2(0)|\|w_1\|_\infty T_N H_{\lfloor3C\rfloor}
           \sqrt{2NR}\,\|b\|_2
 \ll_{w,\eta}(CNR)^\eta D\sqrt{NR}\,\|b\|_2.
 \tag{fourier-zero-bound}
\]

特别，这里没有多余的 `S^(-1/2)` 改善；本节始终是 S=1。

### 4.2 尾项不是被直接丢弃

分部积分给任意整数 L>=2 的界
`|hat w_2(t)|<=A_L(1+|t|)^(-L)`。
对整数 M>=1，在 (completed-actual) 中取 |m|>M 的尾项。
只用 `|K_c(A,B)|<=c`、c 范围的项数至多3C，以及

\[
 \sum_{m>M}(1+mD/(3C))^{-L}
 \le\frac{3C}{D(L-1)}(1+MD/(3C))^{1-L},
\]

就得到

\[
 |\mathcal H_{|m|>M}|
 \ll_{w,L}C^2\sqrt{NR}\,\|b\|_2(1+MD/(3C))^{1-L}.
 \tag{actual-tail}
\]

取 `Z=2CDNR`、`M=ceil((C/D)Z^delta)`，通过选择 L，可使尾项
相对于所写多项式前因子得到任意固定 Z 负幂。
这些零频和尾项估计均已证明，不使用 DI 谱定理，甚至不需要 Weil 界。

## 5. 剩余谱输入及从它到不完全和的推导

这一节**明确使用尚未自证的 DI82 Theorem 11**。这是区别于前四节的
逻辑边界。该定理的 S=1 版本控制

\[
 \sum_{r\asymp R}\sum_{n\asymp N}\sum_{m\in I}
 b(n,r)\sum_{(c,r)=1}g(c,m,n,r)K_c(m\bar r,\pm n),
 \tag{remaining-spectral-object}
\]

其中 I 是 `m asymp M` 中的一个整数区间，m 系数是其示性函数，
而不是任意 m 系数。g 为尺度归一化导数受控的光滑权重，c 支撑在
常数倍 C 区间。其界为
`<<_eta (CMNR)^eta F(C,M,N,R) sqrt(M)||b||_2`，其中可取

\[
 F(C,M,N,R)^2=
 R\frac{(RC^2+MN+MC^2)(RC^2+MN+NC^2)}{RC^2+MN}
       +C^3\sqrt{R(R+N)}.
 \tag{DI11-S1}
\]

统一常数可吸收 dyadic 端点的固定倍数和复权重的实部、虚部分解。
来源中的 Theorem 11 对 Theorem 10 的第二项作改进；其证明 p.279--280
仍调用 Kuznetsov 公式、常规谱大筛和 exceptional-spectrum 估计。
本节没有证明或省略这些谱步骤。

下面给出从这个准确输入推到本任务需要的不完全和估计的全过程。
先将 r 和 |n| 分成 dyadic 区间，正负 n 分开，固定其中一块。
零延拓保持 ||b|| 不增。单点1可用尺度1/2的区间处理，最后用尺度1
的上界吸收；所有参数的固定倍数仅改变常数。

对非零 m 也分成正负 dyadic 区间。负 m 换成正指标 k 时，
`K_c(-k bar r,n)=conjugate(K_c(k bar r,-n))`；把该块整体共轭即可
应用同一定理，因此不需要不同的负 m 谱假设。

在 `m asymp M,c asymp C` 上提出 D/C，剩余实际权重是

\[
 g(c,m)=\frac Cc w_1(c/C)\widehat w_2(mD/c).
 \tag{actual-spectral-weight}
\]

可乘固定尺度 cutoff 以满足定理的 compact support 条件，并让它们
在实际求和支撑上等于1；m 系数仍是区间示性函数。
若 w_1 的支撑跨过原定理的单个 `[C,2C]` 区间，用有限个尺度与 C
可比的光滑分割覆盖 `[C/2,3C]`，每块分别应用；分割的归一化导数
有固定界，块数固定。以下仍以 C 记可比尺度，统一常数吸收这一分割。
令 t=MD/C。因为 hat w_2 是 Schwartz 函数，链式法则逐次给出

\[
 |c^i m^j\partial_c^i\partial_m^j g(c,m)|
 \le C_{i,j,A,w}(1+t)^{-A}
 \tag{uniform-weight-derivatives}
\]

对任意 i,j,A>=0 成立，常数与 C,D,M 无关。
事实上左边展开成有界尺度 cutoff 因子与
`x^k hat w_2^(l)(x)` 的有限和，x=mD/c 与 t 相比在固定倍数内。
n,r cutoff 的归一化导数也有固定界。因此可以在应用 DI11 前
提出 `(1+t)^(-A)`；没有把高频权重的导数损失隐入一个依赖参数的常数。

于是一个 m 块对 H 的贡献至多

\[
 \ll_{w,\eta,A}\frac DC(CMNR)^\eta
        (1+MD/C)^{-A}\sqrt M F(C,M,N,R)\|b\|_2.
 \tag{completed-block}
\]

为严密合并所有 m 块，令 `M_0=C/D`，只把它用在下面显式函数比较中，
不要求它是整数，也不把一个空整数区间交给谱定理。
写 `X=RC^2+MN`，则 (DI11-S1) 的常规部分为

\[
 R\left[X+C^2(M+N)+\frac{MNC^4}{X}\right].
\]

每一项都是 M 的非减函数；当 M 放大为 tM、t>=1，每项至多放大 t。
其中唯一的有理项使用
`tM/(RC^2+tMN)<=tM/(RC^2+MN)`。exceptional 项与 M 无关。
所以

\[
 \frac{\sqrt M F(C,M,N,R)}{\sqrt{M_0}F(C,M_0,N,R)}
 \le\begin{cases}\sqrt{M/M_0},&M\le M_0,\\M/M_0,&M\ge M_0.\end{cases}
 \tag{dyadic-sum-control}
\]

又有 `CM_0NR=C^2NR/D <= Z^2`（Z=2CDNR），故 (CMNR)^eta
可由 `Z^(2eta) max(1,M/M_0)^eta` 控制。
将 (completed-block) 按 dyadic M 求和，低端是收敛的平方根几何级数，
高端取 A>2+eta 后也绝对收敛。因此所有非零 m 的总贡献为

\[
 \ll_{w,\eta}Z^{2\eta}\frac DC\sqrt{M_0}
                  F(C,M_0,N,R)\|b\|_2.
\]

这里同时处理了 D>C、M_0<1 的情形；低端若为空就不求和。
这也提供了不截断 m 时的合法合并；第4.2节另给出了有限截断的明确误差。

最后作尺度代入，不省略通常写作“简单计算”的步骤。对 F^2 的常规项，

\[
 \begin{aligned}
 \frac{D^2}{C^2}M_0 F_{\rm reg}(C,M_0,N,R)^2
 &=CDR^2+RN+C^2R+CDRN+
      \frac{D^2M_0^2 NRC^2}{RC^2+M_0N}\\
 &\le C(R+N)(C+DR)+D^2NR,
 \end{aligned}
\]

因为最后分式不超过 `D^2 M_0^2 N=C^2N`，且 D>=1 使 RN<=D^2NR。
exceptional 项则精确变为 `C^2D sqrt(R(R+N))`。
加上 (fourier-zero-bound)，再把 r,n 的有限 dyadic 块合并并吸收
对数、约数损失，得到

\[
 |\mathcal H|\ll_{w,\epsilon}(CDNR)^\epsilon
       I(C,D,N,R)\|b\|_2,
 \quad I^2=C(R+N)(C+DR)+C^2D\sqrt{R(R+N)}+D^2NR.
 \tag{incomplete-from-DI11}
\]

合并时可取各 dyadic 块的 N,R 上界为全局 N,R，因为 I^2 的各项
均非减；块数为 `O(log(2N)log(2R))`，每块 ||b|| 不超过全局范数。
先把上述 eta 取为 epsilon 的充分小固定倍数，即得到所写 epsilon。

## 6. 实际 DI84 矩形界和 Conrey 接合

回到第2节系数，取 `N=2UV,R=V^2`，删去 n=0 后用
(incomplete-from-DI11) 和 (coefficient-energy)。Cauchy--Schwarz
的**外层** CD 因子仍保留。由 n=0 与 n!=0 两部分可得

\[
 \mathcal T\ll_\epsilon(CDUV)^{1/2+\epsilon}
 \left\{(CD)^{1/2}+(U+V)^{1/4}
 [CD(U+V)(C+V^2)+UV^2D^2]^{1/4}\right\}.
 \tag{DI84-actual-derived}
\]

核查第二项的代数：忽略固定倍数2，N 取 UV、R 取 V^2 时

\[
 I^2\le C_w V\{CD(U+V)(C+V^2)+UV^2D^2\}.
\]

第一项 `C V(U+V)(C+DV^2)` 被右边控制，因为 D>=1；
第二项用 `sqrt(V(U+V))<=U+V`；最后项本来就是 `D^2UV^3`。
把此式和 `||b||^2 << (UV)^epsilon U^2V(U+V)` 代入
`T_nonzero^4 << (CD)^2 I^2 ||b||^2`，恰得 (DI84-actual-derived)
中的第二项。第2节零 determinant 项给第一项，调和和损失吸入 epsilon。

对 `c<=C,d<=D` 的版本，再将这两个外层变量分成 dyadic 区间；
参数扩大只增加右端，对数损失同样吸收。这与原刊 DI84 Lemma 1
在固定整数参数 rho=1 时的界一致。
换回第1节的实际变量映射，正好恢复前篇 (DI-map)，从而前篇的
七单项式估计和余项应用不需要修改。这里没有把新指数微调作为交付目标。

## 7. 勘误、源证据与尚未完成的谱步骤

DI82 原刊 Theorem 12 的 (1.57)，p.237，最后项为 `D^2 N R S^(-1)`。
Bombieri--Friedlander--Iwaniec 2019 的 Lemma 2.1 将它改为 `D^2NR`，
并指出对应 p.281 的 (9.11) 应从 `D sqrt(NR/S)` 改成 `D sqrt(NR)`。
本篇第4.1节独立重算得到后者在 S=1 的值。

本任务的分母始终是 c，r=v_1v_2 进入被取逆的乘积 rd；没有另一个
乘在分母上的 s 变量。因此 DI82 的 S 固定为1（用 dyadic 区间
支撑一个整数 s=1 时尺度可取1/2，只影响固定常数），不是 V、g
或某个平均模数。本篇不会将这个结论外推到任意 S 的应用。
所以本次勘误不改变当前 Conrey 的 DI-map 或已有指数预算。

已查看的原刊证据：

- DI84，*Power mean-values for Dirichlet's polynomials and the Riemann
  zeta-function, II*，Lemma 1，pp.310--311，含平方展开、能量估计和
  对 DI82 Theorem 12 的调用：[原刊 PDF](https://www.impan.pl/shop/en/publication/transaction/download/product/104164)。
- DI82，*Kloosterman Sums and Fourier Coefficients of Cusp Forms*，
  Theorems 10--12，pp.236--237，以及 §9.1--9.2，pp.278--282：
  [定理部分](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0020.pdf)、
  [证明部分](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0028.pdf)。
- Bombieri--Friedlander--Iwaniec，*Some corrections to an old paper*，
  §2，pp.1--2：[作者勘误](https://arxiv.org/abs/1903.01371)。

下一步需要实际证明的仍是 (remaining-spectral-object) 的 DI11 界。
按原刊 §9.1，它依赖两个不能由本篇推出的部分：
常规谱的 Kuznetsov 展开和大筛，以及针对区间 m 系数的 exceptional
谱加权估计。这里没有假设所有谱都 tempered，也没有把 exceptional
项删掉；它正是 (DI11-S1) 的 `C^3 sqrt(R(R+N))` 项。
完成算术/补全层，不等于这些谱步骤已经被证明。

## 8. 验收范围

本篇新增的无条件局部证明是前四节，以及第5--6节从明确 DI11
输入到实际矩形界的推导；它不提供 DI11 自身的证明。
独立审查应核对 determinant 符号、gcd 格点计数、两种零项、D/c
归一化、负 m 共轭、区间系数条件、Schwartz 导数的统一性及最终尺度代数。

最终提交须重跑 Python 回归、目标分类、chain-gap 与 diff 检查，
日志随 PR 记录；有限枚举仅作诊断。无 Lean/Lake/契约修改，未获
独占资源窗口前不启动 Lean，不能用本次回归或历史日志宣称原生终点成立。
