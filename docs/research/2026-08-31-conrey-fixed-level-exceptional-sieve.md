# Conrey 的 DI 谱路线：实际固定层数的加权异常谱大筛

先说结论：本篇完成当前 S=1 路线所需 infinity、0/1 尖点的
固定层数 X 放大异常谱界。证明使用已构造的实际 Maass 系数、
已证明的 Kuznetsov 公式，以及本次相邻尺度差核；没有把 DI
Theorem 5 当成输入。跨层数平均、区间系数的强化及完整 DI11
参数预算仍是后续，所以不能据此宣布原生 Conrey 严格 >2/5。

冻结基点 7905ef19c761d08396d462a8a9a19f8acd75ab18。
本篇只新增纸面证明，不更改冻结源树，不启动 Lean。

## 1. 精确定理及已经建立的输入

q>=1 是整数，Gamma=Gamma_0(q)，曲面测度 dxdy/y^2，不除面积。
尖点 mathfrak a 属于 {infinity,0,1}，sigma_infinity=I，
sigma_0=W_q，sigma_1=T_1 W_q。0与1同属一个尖点类。
实际正交归一 Maass 基的展开是

\[
 u_j(\sigma_{\mathfrak a}z)
  =\sqrt y\sum_{n\ne0}\rho_{j\mathfrak a}(n)
                               K_{ir_j}(2\pi|n|y)e(nx).
\]

异常项指0<lambda_j<1/4，即 r_j=i nu_j、0<nu_j<=1/4。
lambda=1/4、r=0 放入普通实谱。令 N>=1 为实数，复数系数 a_n
只支撑在整数 N<n<=2N，X>=1。定义

\[
 \mathcal E_{\mathfrak a}(X;a,q)
   =\sum_{j\ \mathrm{exceptional}} X^{2\nu_j}
                     \left|\sum_n a_n\rho_{j\mathfrak a}(n)\right|^2.
\]

本篇证明，对每个 epsilon>0，

\[
 \boxed{\mathcal E_{\mathfrak a}(X;a,q)
 \ll_\epsilon
    \left(1+\sqrt{\frac{NX}{q}}\right)
    \left(1+\sqrt{\frac{N^{1+\epsilon}}q}\right)\|a\|_2^2.}
 \tag{actual-fixed-level-weighted-exceptional-sieve}
\]

常数不依赖 q,N,X、异常参数或系数。不是任意尖点版本，不能
对其他尖点擅自使用1/q。X 指权重尺度，核尺度另记 delta。

输入均为本纸面链已有证明，不是待补假设：

1. [实际离散 Maass 大筛及3/16谱隙](2026-08-31-conrey-maass-poincare-discrete-sieve.md)。
2. [实际全尖点连续谱大筛](2026-08-31-conrey-eisenstein-continuous-sieve.md)。
3. [实际 Petersson 与全纯大筛](2026-08-31-conrey-petersson-holomorphic-spectral-proof.md)。
4. [实际同号、异号及跨尖点 Kuznetsov](2026-08-31-conrey-actual-signed-kuznetsov.md)。
5. 本次配套的 [小尺度差核](2026-08-31-conrey-compensated-small-scale-kernel.md)。

前三种大筛对 R>=1 的累积谱质量都给
(R^2+N^(1+eta)/q)||a||^2，任意 eta>0。Maass 权重为
1/cosh(pi r_j)，连续谱保留全部不等价 Eisenstein 尖点；
全纯权重为 Gamma(k)/(4pi)^(k-1)，系数为
n^(-(k-1)/2)a_(f,mathfrak a)(n)。不合并不同尖点的连续谱索引。

## 2. 三类非异常谱对差核的统一预算

令 B=N/q，取本次 Phi_delta，0<delta<=1/16。
将实际同号 Kuznetsov 乘 bar(a_m)a_n 并对 m,n 求和。
实际几何表达为

\[
 \mathcal K_\delta
  =\sum_{m,n}\overline{a_m}a_n
        \sum_{\substack{c\ge1\\q\mid c}}
        \frac{\operatorname{Kl}_c(m,n)}c
                 \Phi_\delta(4\pi\sqrt{mn}/c).
 \tag{actual-geometric-quadratic-form}
\]

同尖点0/1具有同样的 c 及 Kloosterman 和，来自实际 Fricke
共轭。这不是跨尖点 d sqrt(q) 模数；此处必须用同尖点以得到
谱平方和。由于紧支撑且离开0，对每对 m,n，c 和实际有限。

异常项恰为

\[
 \mathcal A_\delta
  =\sum_{j\ \mathrm{exceptional}}
       \frac{\widehat\Phi_\delta(i\nu_j)}{\cos(\pi\nu_j)}
                  \left|\sum_n a_n\rho_{j\mathfrak a}(n)\right|^2.
 \tag{actual-exceptional-square}
\]

普通 Maass 项同式但 r_j 实；连续项为1/pi乘
sum_c integral hat(Phi_delta)(r)|sum_n a_n n^(ir)
varphi_(c,mathfrak a,n)(1/2+ir)|^2 dr；全纯项为

\[
 \frac1\pi\sum_{\substack{k\ge2\\k\ \mathrm{even}}}
     i^k\widetilde\Phi_\delta(k-1)
     \frac{\Gamma(k)}{(4\pi)^{k-1}}
     \sum_{f\in B_k(q)}
       \left|\sum_n a_n n^{-(k-1)/2}a_{f\mathfrak a}(n)\right|^2.
\]

保留这里的1/pi，而不是原刊另一个全纯归一化。三种非异常项
的总和记为 R_delta。公式是准确等式
K_delta=A_delta+R_delta；没有另加或删去对角项，沿用已证明
测试核 Kuznetsov 的完整版本（其对角与离散 Bessel 部分已配平）。

对普通 Maass 和连续谱，先取 |r|<=1，再取
2^h<|r|<=2^(h+1)。用差核四次衰减及累积大筛，绝对值和由

\[
 C_b\left\{1+\frac{N^{1+\eta}}q+
   \sum_{h\ge0}2^{-4h}
              \left(2^{2h+2}+\frac{N^{1+\eta}}q\right)\right\}\|a\|_2^2
 \ll_{b,\eta}(1+BN^\eta)\|a\|_2^2
\]

控制。全纯项的 factorial 衰减同样给对 k 的绝对可和主化，
例如先用其蕴含的 C_b(1+k)^(-4) 再做相同二进区间求和。
所以

\[
                         |R_\delta|\ll_\eta(1+BN^\eta)\|a\|_2^2.
 \tag{uniform-regular-spectral-budget}
\]

这一步没有 log(1/delta)，没有最小 nu 的倒数；非异常谱不被
当成非负后直接丢弃，而是实际估计其绝对值。

## 3. 低密度区：让几何和准确为空

设 B<=b_0=1/(256pi)，并取

\[
                           \delta=16\pi B\le1/16.
 \tag{support-choice}
\]

对任何出现的 m,n，sqrt(mn)<=2N，c>=q，故
4pi sqrt(mn)/c<=8pi B=delta/2。由于 Phi_delta 支撑在
(delta,4delta)，几何和逐项为0，而不是一个小误差。
于是 A_delta=-R_delta。又0<nu_j<=1/4，cos(pi nu_j)在
[1/sqrt2,1]，差核的正下界给

\[
 \sum_{j\ \mathrm{exceptional}}\delta^{-2\nu_j}
        \left|\sum_n a_n\rho_{j\mathfrak a}(n)\right|^2
             \ll_\eta(1+BN^\eta)\|a\|_2^2.
 \tag{geometric-cutoff-amplification}
\]

注意差核不是非负测试函数，但它在整个异常参数区间上的 hat
确为正；这是上一步可以推出不等式的原因。

对任意 X>=1 及0<=2nu<=1/2，有准确比较

\[
 X^{2\nu}=\delta^{-2\nu}(X\delta)^{2\nu}
          \le\delta^{-2\nu}\max(1,\sqrt{X\delta}).
\]

因此低密度区中

\[
 \mathcal E_{\mathfrak a}(X;a,q)
 \ll_\eta(1+\sqrt{BX})(1+BN^\eta)\|a\|_2^2.
\]

这里的固定因子 sqrt(16pi) 进入绝对常数。取 eta=epsilon/2，
因 B<=b_0<1，
BN^(epsilon/2)=sqrt(B)sqrt(BN^epsilon)<=sqrt(BN^epsilon)。
恰得到第1节两个括号的目标界，不引入 X^epsilon 或 q^epsilon。

## 4. 其余密度区及端点

对 B>b_0，不要求 delta=16pi B 仍可作小尺度核。
直接由3/16谱隙及 R=1 的普通 Maass 大筛，

\[
 \mathcal E_{\mathfrak a}(X;a,q)
     \le X^{1/2}\mathcal E_{\mathfrak a}(1;a,q)
     \ll_\eta X^{1/2}(1+BN^\eta)\|a\|_2^2.
\]

最后一步中普通大筛的 1/cos(pi nu_j)>=1，因此确实控制
未除 cos 的 E(1)。取 eta=epsilon/2，目标右侧展开后至少
包含 sqrt(BX) 和 B sqrt(X)N^(epsilon/2)。又 B>b_0 保证
sqrt(X)<=b_0^(-1/2)sqrt(BX)。因此本区间也得到目标界。
这与第3节一起覆盖全部 q,N,X。

- X=1 不需要极限，两个区间的比较仍成立。
- r=0 放在实谱预算中，用差核的一致界，不把0当正异常参数。
- q=1 没有用“两个尖点不同”作为前提；同尖点公式仍有其已
  配平的对角部分。即使不调用 q=1 无异常谱的额外事实，证明
  的第4节仍适用。
- a_n 可以复数、可以为0，也可以只在子区间上非零。没有把
  复系数的平方替换为未共轭的二次式。
- N 可为实数；输入大筛已处理实尺度，此处只用 n<=2N。
- 全部求和交换都有第2节给出的绝对主化；不需要随 delta
  变化的隐含谱质量常数。

## 5. 对 DI11 与最终 Conrey 的实际推进边界

本篇建立的是 DI Theorem 5 的当前尖点版本，而不是引入
“假设加权大筛成立”的新接口。具体完成的是固定 q 的
X^(2nu_j) 平方和及其正确的 q,N,X 预算。

仍需继续：

1. 对层数 q 求和后的互换及递推，完成实际平均层数异常谱界。
2. 对区间 m 系数的强化，取得 DI Theorem 7 型 sqrt(N)X 项，
   不是用一般系数的 NX 项替代它。
3. 一般变化尺度/有限导数测试核、分离变量与 DI11 的完整
   S=1 参数预算；特别保留其额外异常谱项
   C^3 sqrt(R(R+N))，不能只重复同层大筛。
4. 把这些输入接回已经建立的算术 completion 和后续均方链，
   最后在专属资源窗口中作 Lean 验证。

因此，本次局部结果可单独审查交付；完整原生 Selberg/Conrey
目标是否可宣布，仍按未完成输入清单判断，不按 PR 标签或
Python 通过数判断。原刊 p.232 (1.38)、pp.270--271 Section 8.1
用于比对输出范围；本篇第2--4节给出了独立的实际证明。

### English summary

For the actual width-one cusps infinity and 0/1 of Gamma_0(q), this note
proves the fixed-level exceptional large sieve with weight X^(2nu):
(1+sqrt(NX/q))(1+sqrt(N^(1+epsilon)/q)) times the coefficient norm squared.
A compensated small-scale test has uniformly bounded regular-spectrum
cost and positive exceptional transform. Choosing its support above all
possible geometric arguments makes the Kloosterman sum exactly zero.
The proved 3/16 gap then extends the one-scale amplification to every
X>=1. Varying-level averaging, the interval-coefficient improvement,
the full DI11 budget, and native Conrey >2/5 remain open in this chain.
