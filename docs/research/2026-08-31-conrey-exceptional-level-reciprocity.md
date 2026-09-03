# Conrey 的 DI 谱路线：实际层数互换与一般系数异常谱平均

先说结论：本篇把前序实际 Kuznetsov 和小尺度差核接到层数互换，
证明一般系数的平均层数异常谱大筛。换层后的两组 Mellin 扭曲、
小异常参数、三类普通谱误差，以及换层后进入高密度区的归纳分支
都保留。不是把原刊 Lemma 8.1 或 Theorem 6 当成新的输入。

冻结基点 d571ee40522e2a9fc09a470a97c4ef83ba98a87c。
只新增纸面证明，无 Lean、Lake 或契约变更。区间系数强化与
完整 DI11 仍待完成，不宣布原生 Conrey 严格 >2/5。

## 1. 实际对象、系数独立性及目标

Gamma_0(q) 上的实际正交归一 Maass 基、测度 dxdy/y^2、尖点
infinity 的缩放 I、Fourier 系数 rho_(j,q)(n)，均沿用
[实际固定层数异常谱证明](2026-08-31-conrey-fixed-level-exceptional-sieve.md)。
异常项为 r_(j,q)=i nu_(j,q)，0<nu_(j,q)<=1/4；r=0 属于普通谱。
所有 q 的系数行 a_n 是同一行复数，支撑在整数 N<n<=2N，N>=1。
本篇不允许 a_n 随 q 任意变化。

对 Y>=1、Q>=1，定义半开层数区间的实际平方和

\[
 D(Q,Y;a)=\sum_{Q\le q<2Q}\sum_{j\ {\rm exceptional}}^{(q)}
         Y^{2\nu_{j,q}}\left|\sum_n a_n\rho_{j,q}(n)\right|^2,
 \qquad M(Q,Y,N)=\sup_{\|a\|_2=1}D(Q,Y;a).
 \tag{actual-level-block}
\]

空系数空间时取 M=0。M 是有限维系数空间上实际正算子的范数，
不是待证公理。已证普通 Maass 大筛和3/16谱隙立即给

\[
 M(Q,Y,N)\ll_\eta\sqrt Y\,(Q+N^{1+\eta}),\qquad
 M(Q,Y,N)\le\max(1,\sqrt{Y/Z})M(Q,Z,N)\quad(Y,Z\ge1).
 \tag{ordinary-level-bound-and-comparison}
\]

第一式逐 q 求和，因1/cos(pi nu)>=1；第二式逐个非负谱项使用
0<2nu<=1/2。故 M 的上确界确实有限，且 n^(it) 扭曲不改变
允许的系数集合或其范数。每个谱权重只依赖特征值，故结果也
不依赖同一特征空间中的正交基选择。

本篇证明：对任意 epsilon>0，Q,N>=1、X>0，

\[
 \boxed{\sum_{q\le Q}\sum_{j\ {\rm exceptional}}^{(q)}
        X^{4\nu_{j,q}}\left|\sum_n a_n\rho_{j,q}(n)\right|^2
   \ll_\epsilon (QN)^\epsilon(Q+N+NX)\|a\|_2^2.}
 \tag{actual-level-averaged-exceptional-sieve}
\]

当 X>=1，N 项可省略。中间变量是 Y=X^2，因此中间预算应为
Q+N sqrt(Y)，不能把 Y 和 X 混同。本式是当前 infinity 尖点的
DI Theorem 6 型结论，不是区间系数的 Theorem 7 型强化。

## 2. Mellin 扭曲后的差核：零质量不再自动保留

取前篇固定的非负 b 属于 C_c^infty((1,2))，integral b(u)du/u=1。
固定 kappa=1/64，delta=kappa/Y，令

\[
 \Phi_\delta(x)=b(x/\delta)-b(x/(2\delta)),\qquad
 \Phi_{\delta,t}(x)=x^{it}\Phi_\delta(x)\quad(t\in\mathbb R).
\]

前篇的 [一致差核证明](2026-08-31-conrey-compensated-small-scale-kernel.md)
给 hat(Phi_delta)(i nu)>=c delta^(-2nu)，同时普通谱代价一致有界。
但 t!=0 时一般 integral Phi_(delta,t)dx/x!=0，不能直接套用
不含对数的结论。

为此令

\[
 F_t(v)=\int_1^2 b(u)u^{it}\cos(vu)\frac{du}{u},\qquad
 G_t(v)=F_t(v)-2^{it}F_t(2v).
\]

G_t 为复值偶 Schwartz 函数，但 G_t(0) 可以不为0。实际余弦
表示逐字给出

\[
 \widehat\Phi_{\delta,t}(r)
       =2\delta^{it}\int_0^\infty\cos(2rs)G_t(\delta\cosh s)ds,
\]

\[
 \check\Phi_{\delta,t}(r)
       =2\delta^{it}\int_0^\infty\cos(2rs)G_t(\delta\sinh s)ds.
 \tag{twisted-cosine-representations}
\]

对任意整数 A>=0，存在整数 B_A，仅依赖 A，使

\[
 |\widehat\Phi_{\delta,t}(r)|+|\check\Phi_{\delta,t}(r)|
 \ll_{b,A}(1+|t|)^{B_A}(1+\log Y)(1+|r|)^{-A}
                              \quad(r\in\mathbb R).
 \tag{twisted-real-transform-bound}
\]

证明：对 u 的任意固定阶分部积分，把 F_t、G_t 的相应 Schwartz
半范数界为 (1+|t|) 的一个固定幂。在 s>=1 置 v=delta cosh s
或 delta sinh s，ds 与 dv/v 可比。零阶振幅在 delta<v<1
只有 O(1) 界，故其 L1 多出 log(1/delta)=log64+logY。
任意正阶 s 导数则消掉常数；由于 G_t 偶性，
v G_t'(v)=O(v^2)，而 h>=2 时 v^h G_t^(h)(v)=O(v^2)。
所以这些导数的 L1 只多出上述 t 的固定幂，不含 logY。
s<=1 由链式法则直接控制；两个振幅都是光滑偶函数，所有奇数
阶边界导数在0为0。对 r>=1 反复分部积分，再用零阶 L1
处理 |r|<=1，得到所述界。全过程只用固定阶的 b 半范数。

整数 l>=1 时，|x^(it)|=1 给出与前篇相同的

\[
 |\widetilde\Phi_{\delta,t}(l)|
           \le2e^{4\delta^2}(2\delta)^l/l!.
 \tag{twisted-holomorphic-bound}
\]

在异常谱中，令 alpha=2nu。对固定0<tau<1/4 分成两段：

- 0<nu<=tau：前篇安全一般上界及紧支撑的绝对质量给
  |hat(Phi_(delta,t))(i nu)|<=C(1+logY)Y^(2tau)，一致于实 t。
- tau<nu<=1/4：J 的幂级数给实际积分核

\[
 k_\alpha(x)=c(\alpha)x^{-\alpha}+O_\tau(1),\qquad
 c(\alpha)=\frac{\pi2^{\alpha-1}}
                     {\sin(\pi\alpha/2)\Gamma(1-\alpha)},
                   \quad0<x\le1/16.
 \tag{exceptional-leading-kernel}
\]

这里负幂支的首个余项为 O_tau(x^(2-alpha))，正幂支为
O_tau(x^alpha)，均有界；1/sin(pi alpha/2)由 tau 控制。
因此

\[
 \widehat\Phi_{\delta,t}(i\nu)
 =c(\alpha)\delta^{it-\alpha}
    (1-2^{it-\alpha})\int_1^2b(u)u^{it-\alpha}\frac{du}{u}
       +O_\tau(1).
 \tag{twisted-exceptional-leading-term}
\]

首项绝对值<=C_tau Y^alpha，误差独立于 t,Y。上述小参数界不能
仅用带导数假设的一般上界去推 x^(it) 的一致 t 控制；这里实际
使用点态 |k_alpha(x)|<=C(1+|log x|)x^(-alpha)，再积
|Phi_delta|dx/x。该点态界也由 J 的两支幂级数相减及其 alpha=0
可去极限得到：首项差商受 C(1+|log x|)x^(-alpha) 控制，余项
再多 x^2。故不会暗中引入 t 因子或最小正异常参数的倒数。

## 3. 精确几何互换及全部支撑

固定实非负 f 属于 C_c^infty((1/2,4))，且 f=1 于 [1,2]。
f 与所有导数均只固定一次。对每个 q，在实际同尖点 Kuznetsov
中使用 Phi_delta，乘 bar(a_m)a_n 求和，再乘 f(q/Q)。
差核的异常正下界和三类普通谱预算给

\[
 D(Q,Y;a)\le C\left|\mathcal G(Q,Y;a)\right|
                  +O_\eta((Q+N^{1+\eta})\|a\|_2^2),
 \tag{first-trace-inequality}
\]

其中

\[
 \mathcal G=\sum_{q,d\ge1}\frac{f(q/Q)}{qd}
       \sum_{m,n}\overline{a_m}a_n
         \operatorname{Kl}_{qd}(m,n)
            \Phi_\delta\!\left(\frac{4\pi\sqrt{mn}}{qd}\right).
 \tag{exact-double-geometric-sum}
\]

这里全纯系数仍为1/pi，连续谱仍遍历全部不等价 Eisenstein
尖点；没有新增或删除测试核公式已配平的对角项。

q 位于 (Q/2,4Q)，m,n 位于 (N,2N]，x 位于 (delta,4delta)。
若某项非零，令 C=NY/Q，则一定有

\[
              d\in I(C):=[16\pi C,1024\pi C]\cap\mathbb Z_{\ge1}.
 \tag{exact-switched-level-support}
\]

确实下界来自 sqrt(mn)>N、q<4Q、x<4delta；上界来自
sqrt(mn)<=2N、q>Q/2、x>delta，且 kappa=1/64。
这些是宽松闭区间支撑，不将实数层数强行取整。q,d,m,n 的和
全部有限，所以此处交换 q,d 无收敛问题。

对每个 d，置

\[
 h_{d,m,n}(x)=f\!\left(\frac{4\pi\sqrt{mn}}{dQx}\right)\Phi_\delta(x).
\]

则按 q 求和的几何式正是 Gamma_0(d) 的同尖点公式：模数为
dq，系数1/(dq)。不能把 d 当连续参数，也不能仍使用 q 的谱。
这一步是对实际群再用一次已经证明的 Kuznetsov，而不是引用
一个抽象“换层估计”。

## 4. Mellin 分离与相反扭曲的配对

令 chi(t)=integral_0^infinity f(v)v^(it)dv/v。对任意 L，
|chi(t)|<=C_(f,L)(1+|t|)^(-L)，由 log v 坐标分部积分得到。
Fourier 反演给

\[
 h_{d,m,n}(x)=\frac1{2\pi}\int_{\mathbb R}\chi(t)
       \left(\frac{dQ}{4\pi}\right)^{it}
              m^{-it/2}n^{-it/2}\Phi_{\delta,t}(x)dt.
 \tag{exact-Mellin-separation}
\]

特别注意：两个指标上的扭曲同号，不能直接把求和写成平方。
若 A_(j,d)(t)=sum_n a_n n^(it)rho_(j,d)(n)，Maass 项的实际乘积是

\[
                  \overline{A_{j,d}(t/2)}A_{j,d}(-t/2).
 \tag{opposite-twist-pairing}
\]

连续谱中同样保留 n^(ir) 并在两个因子另加相反 t/2；全纯谱
保留 n^(-(k-1)/2)。因这些扭曲模长为1，三种普通大筛在
Cauchy--Schwarz 后的系数范数都仍为 ||a||_2。

先处理普通谱：取第2节 A=4（全纯用 factorial 界），在 r 或 k
的二进区间上求和。对每个 t,d，其绝对预算不超过

\[
 C_\eta(1+|t|)^B(1+\log Y)(1+N^{1+\eta}/d)\|a\|_2^2,
 \tag{switched-regular-budget}
\]

B 是一个固定整数。选 chi 的衰减阶 L>B+6，t 积分绝对收敛。
因为 d 属于 I(C)，非空时 C>=1/(1024pi)，且

\[
 \#I(C)\ll C,\qquad\sum_{d\in I(C)}d^{-1}\ll1,
 \tag{finite-level-count}
\]

总预算为 O_eta((1+logY)(C+N^(1+eta))||a||^2)。I(C) 为空时
它就是0。没有从这个固定比支撑产生 log q 或尖点数损失。

对小异常参数0<nu<=tau，使用第2节的点态上界、普通 Maass
大筛 R=1 及相同 Cauchy--Schwarz，得到
O_eta((1+logY)Y^(2tau)(C+N^(1+eta))||a||^2)。

对 tau<nu<=1/4，代入 (twisted-exceptional-leading-term)。其中
O_tau(1) 项仍按普通大筛估计，贡献 O_tau(C+N^(1+eta))||a||^2。
主项使用1/cos(pi nu)<=sqrt2及 |首项|<=C_tau Y^(2nu)，并保留
实际双扭曲乘积。逐 d,j 的不等式

\[
 2|\overline{A(t/2)}A(-t/2)|\le |A(t/2)|^2+|A(-t/2)|^2
\]

才把它改成两个异常谱平方和。把 t 换成2t，并利用 chi 任意阶
衰减，得到以下完全来自实际公式的递推：对任意 eta>0，

\[
 \boxed{D(Q,Y;a)\le C_\eta\int_{\mathbb R}\frac1{(1+t^2)^2}
    \sum_{d\in I(NY/Q)}\sum_{j\ {\rm exceptional}}^{(d)}
       Y^{2\nu_{j,d}}\left|\sum_n a_n n^{it}\rho_{j,d}(n)\right|^2dt
   +C_\eta(NY)^\eta(Q+N+NY/Q)\|a\|_2^2.}
 \tag{actual-level-reciprocity}
\]

精确的 epsilon 分配可如下选：以上普通大筛先用 eta/10，
tau=min(eta/10,1/16)；logY+1<=C_eta Y^(eta/10)，所以小参数
的全部 Y 幂不超过 Y^(3eta/10)，N 幂不超过 N^(eta/10)。
把余量放宽到 (NY)^eta。第一轮的普通谱 Q+N^(1+eta/10)
也被同一预算控制。固定 kappa 的幂及 tau 的倒数只进入 C_eta。

第2节对 t 的多项式界、chi 的快速衰减、每个谱方向的累积
大筛，以及有限 d 支撑共同给出绝对主化；因此从 Mellin 积分
到全纯、Maass、连续谱的各次换序都有依据。此前未完成的
一般大尺度测试核估计不在这里被偷偷当作输入。

## 5. 从实际递推到有限层数归纳

现在仅在 Q=2^k、k>=0 的层数尺度上归纳。把 I(C) 用与其相交
的标准整数二进块 [R,2R)、R=1,2,4,... 覆盖，记这些 R 为 R(C)。
它们至多10个，且

\[
                   R\le K C,\qquad K=1024\pi.
\]

若 I(C) 为空则 R(C) 为空。由于 n^(it) 扭曲保持范数，取单位
系数上确界，并把 integral (1+t^2)^(-2)dt 吸入常数，得

\[
 M(Q,Y,N)\le C_\eta\sum_{R\in R(NY/Q)}M(R,Y,N)
             +C_\eta(NY)^\eta(Q+N+NY/Q).
 \tag{finite-reciprocity-recursion}
\]

这是已证明的实际算子范数不等式，不另假设一个递推接口。
特别不能把新的 N 自动视为小于新层数 R；下面分别处理。

固定0<sigma<=1/8，取 eta=sigma^2/100。证明存在 A_sigma，使
所有二进 Q>=1 和1<=N<=Q^(1-sigma) 均有

\[
 Y_Q=(Q^{1-\sigma}/N)^2\ge1,\qquad
                       M(Q,Y_Q,N)\le A_\sigma Q^{1+\sigma}.
 \tag{critical-scale-induction}
\]

选足够大的 Q_0(sigma)。有限个二进 Q<=Q_0 直接由
(ordinary-level-bound-and-comparison) 控制，且 N<=Q_0、Y_Q<=Q_0^2；
增大 A_sigma 后基例对所有允许实 N 一致成立。

设 Q>Q_0，且结论已对所有更小二进尺度成立。此时

\[
 C=NY_Q/Q=Q^{1-2\sigma}/N\le Q^{1-2\sigma},
 \qquad R\le KC\le Q/2,
 \tag{strict-level-contraction}
\]

最后一个不等式通过令 KQ_0^(-2sigma)<=1/2 保证，故归纳确实
严格下降。在递推中对每个 R 分两种情况。

### 5.1 换层后仍处于低密度区

若 N<=R^(1-sigma)，则 Y_R=(R^(1-sigma)/N)^2>=1，归纳可用。
由于 R<Q，有 Y_Q>=Y_R。由3/16比较，

\[
 \begin{aligned}
 M(R,Y_Q,N)
  &\le (Q/R)^{1-\sigma}A_\sigma R^{1+\sigma}\\
  &=A_\sigma Q^{1-\sigma}R^{2\sigma}\\
  &\le A_\sigma K^{2\sigma}
                 Q^{1+\sigma-4\sigma^2}N^{-2\sigma}\\
  &\le A_\sigma K^{2\sigma}Q^{1+\sigma-4\sigma^2}.
 \end{aligned}
 \tag{contracted-low-density-contribution}
\]

这里 Q^(-4sigma^2) 是吸收固定递推常数的真正余量；不能只说
换层更小而忽略常数。

### 5.2 换层后进入高密度区

若 N>R^(1-sigma)，上述归纳假设不适用。改用已证普通大筛，

\[
 \begin{aligned}
 M(R,Y_Q,N)
  &\ll_\eta Q^{1-\sigma}(R/N+N^\eta)\\
  &\le C_\eta\{K^\sigma Q^{1-2\sigma^2}
                                      +Q^{1-\sigma+\eta}\}.
 \end{aligned}
 \tag{contracted-high-density-contribution}
\]

第一项使用 R/N<R^sigma、R<=KQ^(1-2sigma)/N 和 N>=1；
第二项使用 N<=Q。这覆盖 R<N 的情形，没有延伸归纳假设。
若 I(C) 为空，两种贡献均不存在。

### 5.3 递推误差及闭合

因 NY_Q=Q^(2-2sigma)/N<=Q^2，且 N,C<=Q，误差为

\[
                  C_\eta(NY_Q)^\eta(Q+N+C)
                                  \le3C_\eta Q^{1+2\eta}.
\]

eta=sigma^2/100 保证2eta<sigma/2。递推至多10项。
进一步增大 Q_0，使低密度系数
10 C_eta K^(2sigma)Q^(-4sigma^2)<=1/4；高密度贡献及上式误差
各不超过 Q^(1+sigma)/4。所有这些要求只依赖 sigma，因为其
相对幂均严格负。取 A_sigma>=1，代回递推得到至多
(A_sigma/4+1/4+1/4)Q^(1+sigma)<=A_sigma Q^(1+sigma)。
归纳闭合。

这个证明给出有限阈值的存在，不声称 Q_0 或 A_sigma 数值小，
也不用浮点实验充当对所有参数的归纳。

## 6. 任意 Y、累积层数及 X<1

对二进 Q，先设 N<=Q^(1-sigma)。由谱权重比较和已证临界尺度，

\[
 M(Q,Y,N)\le A_\sigma\{Q^{1+\sigma}
                                      +N\sqrt Y\,Q^{2\sigma}\}
      \le A_\sigma(QN)^{2\sigma}(Q+N\sqrt Y).
 \tag{arbitrary-Y-low-density}
\]

这里 Y<Y_Q 时直接用单调性，Y>=Y_Q 时用平方根比例，合并后
才得到两个加项。

若 N>Q^(1-sigma)，不需要临界归纳。普通界给

\[
 M(Q,Y,N)\ll_\eta\sqrt Y(Q+N^{1+\eta})
       \le C_\eta N\sqrt Y\,(Q^\sigma+N^\eta)
       \ll_\sigma(QN)^{2\sigma}(Q+N\sqrt Y),
 \tag{arbitrary-Y-high-density}
\]

因为 Q<NQ^sigma、eta<sigma。于是对所有 N,Y>=1 得到同一界。
给定目标 epsilon，取 sigma=min(epsilon/4,1/8)，有2sigma<=epsilon。

对于任意实 Q>=1，用 Q 以下的二进块覆盖所有整数1<=q<=Q，
最后一个块可以多包含一些层数，因谱项非负这是合法上界。
由几何级数

\[
 \sum_{\substack{R=2^k\\R\le Q}} R^{1+2\sigma}\ll_\sigma Q^{1+2\sigma},
 \qquad
 \sum_{\substack{R=2^k\\R\le Q}} R^{2\sigma}\ll_\sigma Q^{2\sigma},
\]

累积异常谱和不超过 C_epsilon(QN)^epsilon(Q+N sqrtY)||a||^2。
此处没有留下一个未处理的 logQ；sigma 的几何级数常数进入
C_epsilon。置 Y=X^2 得到 X>=1 的目标。

当0<X<1，X^(4nu)<=1，直接逐层累积普通大筛得到
O_epsilon((QN)^epsilon(Q+N))||a||^2，亦被第1节目标控制。
因而 (actual-level-averaged-exceptional-sieve) 对全部 X>0 成立。

## 7. 原刊对照、验收边界与下一步

本次逐页核对 DI pp.271--274 Section 8.2 的 (8.4)--(8.12)。
原刊选择的支撑与本篇不同，因此本篇换层区间使用明确的
[16pi C,1024pi C]，不把 pi 或支撑倍数静默消掉。
原刊的小参数与高参数切分在这里被保留，且补入 Mellin 扭曲
后零质量丢失所需的普通谱对数预算。

本篇不依赖原刊 p.270 (8.2) 的字面零参数一致性陈述，也不
把 p.274 的简写视为自动覆盖 N>R^(1-sigma)：第5.2节已经
单独给出这个换层后高密度分支。原刊作为比对来源为
[DI Section 8 scan](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0027.pdf)。

已完成的数学输入链是：实际全谱公式、实际小尺度差核、Mellin
扭曲预算、准确层数互换、有限下降归纳、一般系数平均层数大筛。
不是把本篇结论加入一个条件接口后宣布目标完成。

仍未完成：

1. 区间系数强化：对应 DI Theorem 7 的 Q+sqrt(N)X，而非本篇
   一般系数的 Q+NX；需额外的不完全 Kloosterman 平均估计。
2. 一般变化尺度测试核与变量分离后的完整 DI11 S=1 预算，
   特别是 C^3 sqrt(R(R+N)) 异常项。
3. 接回算术 completion 与均方证明链，再于专属资源窗口完成
   Lean 验证。当前不启动构建，不把纸面证明称为机器验证。

临时有限诊断只检查几何支撑、模数互换、扭曲共轭和归纳指数
恒等式；Python 回归只守护仓库。不以它们替代无限谱换序和
全参数数学证明。源 SHA 与集成树验收仍分开，源交付后冻结。

### English summary

This note proves the level-averaged exceptional large sieve for one
complex coefficient sequence shared across levels. A compensated test
is Mellin-separated after interchanging the two factors of the modulus.
The opposite twists are paired by Cauchy--Schwarz, and the small-parameter
and regular-spectrum terms are retained in the error. A strictly
contracting dyadic induction handles both density ranges at the new
level and yields (QN)^epsilon(Q+N+NX) for weight X^(4nu). The interval
coefficient improvement and the full DI11/Conrey conclusion remain open.
