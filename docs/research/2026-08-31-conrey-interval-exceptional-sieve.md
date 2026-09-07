# Conrey 的 DI 谱路线：实际区间系数异常谱强化

先说结论：本篇证明区间系数的平均层数异常谱大筛，将一般系数
预算里的 NX 改进成 sqrt(N)X。新输入是一篇已完整证明的模逆
正包络平均，而不是再加入一个待证的谱估计接口。区间 Mellin
扭曲用 Hilbert 空间分部求和处理；换层后的高密度分支单独估计。

冻结基点 abe8df60359f7008e2d317007bd5b969c7429513。
仅新增纸面证明。完整 DI11 及原生 Conrey 严格 >2/5 仍未完成；
本篇不启动 Lean 或依赖加载。

## 1. 实际谱平方和与精确结论

谱对象及归一化沿用
[实际层数互换证明](2026-08-31-conrey-exceptional-level-reciprocity.md)：
Gamma_0(q)，实际正交归一 Maass 基，测度 dxdy/y^2，infinity
尖点的缩放矩阵 I，Fourier 系数 rho_(j,q)(n)。异常参数满足
r_(j,q)=i nu_(j,q)，0<nu_(j,q)<=1/4；r=0 为普通谱。

设 N>=1，I 为 [N,2N] 中任意整数区间，同一个 I 用于所有 q。
允许空区间。对 Q,Y>=1 定义实际非负平方和

\[
 D(Q,Y;I)=\sum_{Q\le q<2Q}\sum_{j\ {\rm exceptional}}^{(q)}
       Y^{2\nu_{j,q}}\left|\sum_{n\in I}\rho_{j,q}(n)\right|^2,
 \qquad L(Q,Y,N)=\frac1N\max_I D(Q,Y;I).
 \tag{actual-interval-level-block}
\]

有限支撑中只有有限多个整数区间。普通 Maass 大筛及3/16谱隙
保证每个 D 有限，并给

\[
 L(Q,Y,N)\ll_\eta\sqrt Y(Q+N^{1+\eta}),\qquad
 L(Q,Y,N)\le\max(1,\sqrt{Y/Z})L(Q,Z,N)\quad(Y,Z\ge1).
 \tag{interval-ordinary-and-comparison}
\]

这里 #I<=N+1<=2N，且 1/cos(pi nu)>=1；没有把有限最大值
本身设成一个假设。

本篇证明：对所有 epsilon>0、Q,N>=1、X>0，

\[
 \boxed{\sum_{q\le Q}\sum_{j\ {\rm exceptional}}^{(q)}
 X^{4\nu_{j,q}}\left|\sum_{n\in I}\rho_{j,q}(n)\right|^2
       \ll_\epsilon(QN)^\epsilon(Q+N+\sqrt N\,X)N.}
 \tag{actual-interval-exceptional-sieve}
\]

这不是任意复系数结论，也不声称能加任意实数的 e(n omega)
而保持同一预算。X>=1 时中间变量是 Y=X^2，因此相应项是
sqrt(NY)，不是 N sqrt(Y)，也不是 sqrt(N)Y。

### 1.1 闭下端点的实际扩展

前篇写支撑 (N,2N]。这里允许 [N,2N]，需要明确验证输入：

1. 三类普通谱大筛此前已经对实尺度 U>=1/2 证明。把任意
   [N,2N] 系数行分成 (N/2,N] 与 (N,2N] 两段，对平方和使用
   |A+B|^2<=2|A|^2+2|B|^2。这两个尺度 U=N/2,N 均允许，
   系数范数平方相加；所得预算仍为 C_eta(R^2+N^(1+eta)/q)。
   特别包含 N=1 时的 n=1。
2. 实际 Kuznetsov 公式对所有正整数 m,n 成立，有限系数求和
   不使用严格下端点。前篇几何支撑与核导数估计仅需
   N<=m,n<=2N，因此原有宽松闭区间 [16pi NY/Q,1024pi NY/Q]
   在这里继续有效。
3. Mellin 分离的两个相反扭曲、普通谱绝对主化、小异常参数
   切分及高参数首项，均只用上述普通大筛和相同几何支撑。
   故重走前篇第3--4节的有限和及绝对收敛积分，得到相同的
   实际层数互换，常数可增大但不出现新的误差项。

这是对已有证明输入逐项的端点扩展，不是把原先字面范围
未覆盖的 n=N 静默纳入结论。

## 2. 新的几何估计及高密度备用界

固定前篇非负 f 属于 C_c^infty((1/2,4))，f=1 于 [1,2]；
b 与 delta=1/(64Y)、Phi_delta 均沿用前篇。实际第一轮 trace 给

\[
 D(Q,Y;I)\le C|\mathcal G(Q,Y;I)|
                        +C_\eta(Q+N^{1+\eta})\#I,
\]

\[
 \mathcal G=\sum_{q,d\ge1}\frac{f(q/Q)}{qd}
      \sum_{m,n\in I}\operatorname{Kl}_{qd}(m,n)
                        \Phi_\delta(4\pi\sqrt{mn}/(qd)).
 \tag{actual-interval-first-trace}
\]

异常谱正下界、所有 Eisenstein 尖点连续谱、全纯及普通 Maass
谱的预算都来自前篇已证实际公式；没有补入独立对角项。

将实际模数置为 c=qd，精确改写为

\[
 \mathcal G=\sum_c\frac{w_Q(c)}c\sum_{m,n\in I}
   \operatorname{Kl}_c(m,n)\Phi_\delta(4\pi\sqrt{mn}/c),
 \qquad w_Q(c)=\sum_{q\mid c}f(q/Q).
\]

|w_Q(c)|<=||f||_infinity tau(c)，且非零项均有
64pi NY<=c<=512pi NY。应用
[模逆正包络证明第4节](2026-08-31-conrey-interval-kloosterman-envelope.md)
的实际带权小尺度预算，并用 #I<=2N，得

\[
 \boxed{L(Q,Y,N)\ll_\eta (NY)^\eta(Q+N+Y).}
 \tag{raw-interval-bound}
\]

任意给定 eta 的约数及包络损失可以各用 eta/2；普通谱项
N^(1+eta) 被 (NY)^eta N 吸收。几何预算除以 N 后是 Y+N，
正是一般系数逐点估计不能提供的改进。

对所有 Y>=1，把 (raw-interval-bound) **用在 Z=Q+N**，然后
用谱权重比较，不把含 Y^eta 的原式直接留在最终预算里：

\[
 \boxed{L(Q,Y,N)\ll_\eta [N(Q+N)]^\eta
                       (Q+N+\sqrt{Y(Q+N)}).}
 \tag{optimized-interval-bound}
\]

确实 raw(Z)<=2C_eta[N(Q+N)]^eta(Q+N)，乘
max(1,sqrt(Y/(Q+N)))，再用 max(1,a)<=1+a 即得。
特别当 N>Q 时，

\[
       L(Q,Y,N)\ll_\eta N^{2\eta}(N+\sqrt{NY}).
 \tag{high-density-interval-bound}
\]

这个备用界对全部 Y 一致；epsilon 因子中已无 Y。
它将处理换层后新层数 R 小于 N 的分支。

## 3. 区间 Mellin 扭曲：Hilbert 空间 Abel 恒等式

不能因为 |n^(it)|=1 就称扭曲后的系数仍是区间指示函数。
对固定 Q,Y，以 (q,j) 为坐标定义谱 Hilbert 空间向量

\[
 v_n=(Y^{\nu_{j,q}}\rho_{j,q}(n))_{Q\le q<2Q,j\ {\rm exceptional}}.
\]

每个 v_n 范数有限，由普通谱大筛保证。令
V(s)=sum_(n in I,n<=s)v_n。每个前缀仍是 [N,2N] 的整数区间，
所以 ||V(s)||<=sqrt(N L(Q,Y,N))。

逐个有限 n 求和并用微积分基本定理，有精确向量恒等式

\[
 \sum_{n\in I}n^{it}v_n
   =(2N)^{it}V(2N)-it\int_N^{2N}V(s)s^{it-1}ds.
 \tag{actual-Hilbert-Abel}
\]

积分为有限维张成空间内的通常积分；也可视为 Bochner 积分，
其范数被常数/s 主化。即使 n=N 为一个端点原子，其右边的
系数仍精确为 (2N)^(it)-it integral_N^(2N)s^(it-1)ds=N^(it)。
于是三角不等式给

\[
 \sum_{Q\le q<2Q}\sum_{j\ {\rm exceptional}}^{(q)}
 Y^{2\nu_{j,q}}\left|\sum_{n\in I}n^{it}\rho_{j,q}(n)\right|^2
    \le(1+|t|\log2)^2\,N L(Q,Y,N)
    \ll(1+t^2)N L(Q,Y,N).
 \tag{actual-interval-twist-bound}
\]

这里平方不能漏掉，且同一个最大值控制所有端点。

## 4. 区间的实际有限层数递推

用第1.1节已扩展的实际互换公式，系数取 1_I：

\[
\begin{aligned}
 D(Q,Y;I)\le{}&C_\eta\int_{\mathbb R}\frac1{(1+t^2)^2}
  \sum_{d\in[16\pi NY/Q,1024\pi NY/Q]}\sum_{j\ {\rm exceptional}}^{(d)}
    Y^{2\nu_{j,d}}\left|\sum_{n\in I}n^{it}\rho_{j,d}(n)\right|^2dt\\
 &+C_\eta(NY)^\eta(Q+N+NY/Q)\#I.
\end{aligned}
 \tag{actual-interval-reciprocity}
\]

d 始终取正整数；区间为空时对应和为0。令 R(C) 为与该
[16pi C,1024pi C] 中整数相交的标准二进层数块 [R,2R) 的
左端点集合。它至多10项，且 R<=KC，K=1024pi。
对每个二进块应用 (actual-interval-twist-bound)，利用
integral_R (1+t^2)^(-1)dt=pi，并除以 N、对 I 取有限最大值，得

\[
 \boxed{L(Q,Y,N)\le C_\eta\sum_{R\in R(NY/Q)}L(R,Y,N)
              +C_\eta(NY)^\eta(Q+N+NY/Q).}
 \tag{finite-interval-reciprocity}
\]

这是实际谱对象的已证递推，不是一个新条件接口。这里也说明
原先 Mellin 权重 (1+t^2)^(-2) 足以支付区间分部求和代价；
没有把不可积的常数函数当作 t 积分主化。

## 5. 强化临界尺度及严格下降归纳

固定 0<sigma<=1/8，取 eta=sigma^2/100。证明存在 A_sigma，
使所有二进 Q>=1、所有实数 1<=N<=Q 均满足

\[
 Y_Q=Q^{2-2\sigma}/N\ge1,
 \qquad L(Q,Y_Q,N)\le A_\sigma Q^{1+\sigma}.
 \tag{interval-critical-induction}
\]

与一般系数情况相比，临界尺度的分母现在是 N 而非 N^2。
这正对应最终 sqrt(N)X 的改进。

选足够大的有限 Q_0(sigma)。对有限个二进 Q<=Q_0，
N<=Q_0、Y_Q<=Q_0^2，普通界 (interval-ordinary-and-comparison)
使基例对所有允许的实 N 一致有界；增大 A_sigma 即可。
以下设 Q>Q_0，且结论已对全部更小二进层数成立。

在当前临界尺度，

\[
               C=NY_Q/Q=Q^{1-2\sigma},\qquad
               R\le KQ^{1-2\sigma}\le Q/2.
 \tag{interval-strict-level-contraction}
\]

最后一个不等式由 KQ_0^(-2sigma)<=1/2 保证。因此归纳引用的
层数确实严格较小；但 N 不必小于 R，必须分两种情况。

### 5.1 N<=R：归纳可用的低密度分支

此时 Y_R=R^(2-2sigma)/N>=1，归纳假设可用于 (R,N)。
Y_Q/Y_R=(Q/R)^(2-2sigma)，故

\[
\begin{aligned}
 L(R,Y_Q,N)&\le(Q/R)^{1-\sigma} A_\sigma R^{1+\sigma}\\
           &=A_\sigma Q^{1-\sigma}R^{2\sigma}\\
           &\le A_\sigma K^{2\sigma}Q^{1+\sigma-4\sigma^2}.
\end{aligned}
 \tag{interval-low-density-contraction}
\]

Q^(-4sigma^2) 是支付固定递推常数的明确余量。

### 5.2 N>R：不延伸归纳假设的高密度分支

改用第2节新证明的 (high-density-interval-bound)，得到

\[
\begin{aligned}
 L(R,Y_Q,N)&\ll_\eta N^{2\eta}(N+\sqrt{NY_Q})\\
           &=O_\eta\bigl(N^{2\eta}(N+Q^{1-\sigma})\bigr)\\
           &\ll_\eta Q^{1+2\eta},
\end{aligned}
 \tag{interval-high-density-contribution}
\]

因为本次临界归纳允许 N<=Q。若只用一般系数普通谱界，
这个强化临界尺度下不足以获得所需的同样预算；新包络输入
在这里确实被使用，并未从证明中消失。

### 5.3 误差、阈值选择及闭合

NY_Q=Q^(2-2sigma)<=Q^2，且 N,C<=Q，故递推误差至多
3C_eta Q^(1+2eta)。每种分支至多10项。进一步增大 Q_0，使

\[
 10C_\eta K^{2\sigma}Q^{-4\sigma^2}\le1/4;
\]

把至多10项的高密度贡献及递推误差各界成 Q^(1+sigma)/4。
这些要求可以同时满足，因为 2eta<sigma，且所有相对幂严格负；
涉及的常数只依赖 sigma。取 A_sigma>=1，则递推右边至多

\[
             (A_\sigma/4+1/4+1/4)Q^{1+\sigma}
                           \le A_\sigma Q^{1+\sigma}.
\]

归纳闭合。没有要求 Q_0 或 A_sigma 小，也不以有限数值实验
代替这个对所有实 N、所有二进 Q 的证明。

## 6. 任意 Y、累积层数及初始区间

对二进 Q，若 N<=Q，利用临界结论及权重比较得

\[
\begin{aligned}
 L(Q,Y,N)&\le A_\sigma
           \{Q^{1+\sigma}+\sqrt{NY}\,Q^{2\sigma}\}\\
         &\le A_\sigma(QN)^{2\sigma}(Q+\sqrt{NY}).
\end{aligned}
 \tag{interval-arbitrary-Y-low-density}
\]

Y<=Y_Q 用单调性，Y>Y_Q 才乘 sqrt(Y/Y_Q)。
若 N>Q，第2节直接给

\[
 L(Q,Y,N)\ll_\eta N^{2\eta}(N+\sqrt{NY})
                 \ll_\sigma(QN)^{2\sigma}(Q+N+\sqrt{NY}).
 \tag{interval-arbitrary-Y-high-density}
\]

两式覆盖全部 N,Y>=1。取 sigma=min(epsilon/4,1/8)，则
2sigma<=epsilon；将 q<=Q 用左端点 R<=Q 的标准二进块覆盖，
用 sum R^(1+2sigma)<<_sigma Q^(1+2sigma) 及
sum R^(2sigma)<<_sigma Q^(2sigma)，得

\[
 \sum_{q\le Q}\sum_{j\ {\rm exceptional}}^{(q)}
 Y^{2\nu_{j,q}}\left|\sum_{n\in I}\rho_{j,q}(n)\right|^2
           \ll_\epsilon(QN)^\epsilon(Q+N+\sqrt{NY})N.
\]

不留下额外的 log Q。置 Y=X^2 处理 X>=1；若0<X<1，
X^(4nu)<=1，直接累积普通 Maass 大筛，给
O_epsilon((QN)^epsilon(Q+N)N)。因此第1节结论对全部 X>0 成立。

还可以得到原刊 Theorem 7 的初始区间形式：对 Z>=1，

\[
 \sum_{q\le Q}\sum_{j\ {\rm exceptional}}^{(q)}X^{4\nu_{j,q}}
       \left|\sum_{1\le n\le Z}\rho_{j,q}(n)\right|^2
               \ll_\epsilon(QZ)^\epsilon(Q+Z+\sqrt Z\,X)Z.
 \tag{actual-initial-interval-corollary}
\]

具体把 [1,Z] 的整数分成 [1,2]、(2,4]、(4,8] 等与 [1,Z]
相交的非空区间；第一块尺度 N=1，后续尺度 N=2,4,...，
每块在允许的闭区间 [N,2N] 内。令这些尺度为 N_h<=Z。
在所有 q<=Q 的异常谱 Hilbert 空间使用三角不等式，平方根
预算不超过常数乘

\[
 (QZ)^{\epsilon/2}\sum_h
       \{\sqrt Q\,N_h^{1/2}+N_h+\sqrt X\,N_h^{3/4}\}
 \ll_\epsilon(QZ)^{\epsilon/2}
       \{\sqrt{QZ}+Z+\sqrt X\,Z^{3/4}\}.
\]

各指数严格正，因此都是几何级数，不用按块数的 Cauchy
而引入 log Z。平方后用 (a+b+c)^2<=3(a^2+b^2+c^2) 即得。
Z=1 也由第1.1节的端点扩展覆盖。

## 7. 原刊对照、交付边界及余项

本篇逐页对照 DI Section 8.3，pp.275--278 的 Theorem 14、
Theorem 7 证明及 (8.13)--(8.17)：
[原刊扫描](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0027.pdf)。
证明采用当前已冻结的实际谱归一化和差核，不逐字搬用原刊的
测试函数或未证明的大尺度输入。第2节明确在 Z=Q+N 取 raw
界，第5节给完整的两种密度分支及严格下降余量；这些等式
本身是验收依据，不依赖简写的参数选择。

本次闭合的是 **实际区间系数异常谱平均**。仍未闭合：

1. 一般变化尺度测试核、变量分离以及完整 DI11 S=1 的全部
   参数预算，尤其其 C^3 sqrt(R(R+N)) 异常谱项的实际装配。
2. 把完整 DI11 接回已写出的算术 completion 和 Conrey 均方
   主项链；当前区间筛估计不能代替这段装配。
3. 专属资源窗口下的后续 Lean 验证及最终集成树验收。

因此不宣布原生严格 >2/5 已完成，也不把已通过的 Python
回归、有限算例或独立纸面审查称为 Lean 证明。当前源交付与
最终 main 集成验证由不同证据负责；发布后源 SHA 冻结。

### English summary

This note proves the interval-coefficient, level-averaged exceptional
large sieve with budget (QN)^epsilon(Q+N+sqrt(N)X)N for weight X^(4nu).
A positive modular-inverse envelope supplies the improved geometric
bound. Hilbert-space Abel summation controls Mellin twists uniformly
over interval prefixes. A critical-scale induction at Y=Q^(2-2sigma)/N
handles both density ranges after level reciprocity; the dense branch
uses an optimized bound with no Y in the epsilon factor. Closed lower
endpoints and the initial interval starting at n=1 are included explicitly.
The full DI11 assembly and native strict >2/5 conclusion remain open.
