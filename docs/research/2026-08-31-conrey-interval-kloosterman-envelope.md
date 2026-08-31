# Conrey 的区间输入：模逆正包络与不完全 Kloosterman 平均

先说结论：本篇直接证明区间 Kloosterman 和所需的模数平均，
并且先控制一个与区间端点无关的正包络。因此后续二维分部求和
可以同时处理所有前缀矩形，不需要把上确界错误地移出求和。
证明只用有限 Fourier 展开、模逆关系和约数界，不把 DI 的一般
大尺度谱估计或 Theorem 14 当作新假设。

冻结基点 abe8df60359f7008e2d317007bd5b969c7429513。
本篇是纸面证明，不增加 Lean、Lake 或条件契约。

## 1. 实际和与正包络

置 e(x)=exp(2 pi i x)。整数 c>=1 的实际完整和为

\[
 \operatorname{Kl}_c(m,n)
   =\sum_{u\bmod c}^{*}e((mu+n\bar u)/c),
 \qquad u\bar u\equiv1\pmod c.
 \tag{actual-complete-sum}
\]

c=1 采用 Kl_1(m,n)=1 的通常约定。这里不存在 1/c 的归一化；
1/c 只在后面的 Kuznetsov 几何式中出现。

若 H>=1，定义周期非负函数

\[
 D_H(x)=\min\{H,(2\|x\|)^{-1}\}\quad(x\notin\mathbb Z),
 \qquad D_H(x)=H\quad(x\in\mathbb Z).
\]

任意含至多 H 个整数的整数区间 I 满足

\[
 \left|\sum_{m\in I}e(mx)\right|\le D_H(x).
 \tag{interval-geometric-envelope}
\]

确实，平移起点只产生单位相位；长度 L 的等比数列绝对值
不超过 min(L,1/|sin(pi x)|)，而 |sin(pi x)|>=2||x||。
空区间的左边为0。H 可以为实数。

现在定义实际有限正和

\[
 B_c(H,K)=\sum_{u\bmod c}^{*}D_H(u/c)D_K(\bar u/c)
       \quad(c\ge2),\qquad B_1(H,K)=HK.
 \tag{positive-inverse-envelope}
\]

对任意两个整数区间 I,J，若 #I<=H、#J<=K，则

\[
 \boxed{\left|\sum_{m\in I}\sum_{n\in J}
                       \operatorname{Kl}_c(m,n)\right|
                    \le B_c(H,K).}
 \tag{all-rectangles-envelope}
\]

证明是在 (actual-complete-sum) 中先交换三个有限和，再逐 u
使用 (interval-geometric-envelope)。同一个 B_c 控制任意平移、
任意长度不超过给定上界的矩形；特别包括一个固定矩形的全部
前缀。它不是依赖所选端点的事后估计。

## 2. 正包络的模数平均

对任意 epsilon>0、实数 C,H,K>=1，有

\[
 \boxed{\sum_{C\le c<2C}B_c(H,K)
                 \ll_\epsilon C^{2+\epsilon}+CHK.}
 \tag{dyadic-positive-envelope-average}
\]

其中 c 取正整数，隐含常数与 H,K 完全无关。

### 2.1 有符号模逆代表及真正的例外

对 c>=2，给 u 和其模逆各选唯一的代表

\[
        -c/2<u\le c/2,\qquad -c/2<v\le c/2.
\]

它们均非0，且 uv=1 mod c。因为 c<2C，所以 |u|,|v|<C；
而包络的每个乘积恰为

\[
       \min(H,c/(2|u|))\min(K,c/(2|v|)).
 \tag{signed-inverse-weight}
\]

先分出 uv=1。这只有 (u,v)=(1,1),(-1,-1) 两种整数对，
每个 c 至多两项，每项不超过 HK，故总贡献 O(CHK)。
某些小模数只能出现其中一项，无碍上界。c=1 也单独计入 HK。

不能把 uv=1 纳入下一步的约数计数：每个 c 都整除0。
与此不同，uv=-1 给 uv-1=-2，属于正常的非零约数分支。

### 2.2 非零 uv-1 的约数计数

对其余项，把 |u|、|v| 分别放入二进区间 [U,2U)、[V,2V)，
其中 U,V 为不超过 C 的非负整数次2幂。每个这样的有符号盒子
至多 O(UV) 个整数对。固定一对 uv!=1 后，可用的 c 必须满足

\[
       c\mid |uv-1|,\qquad 1\le |uv-1|\le C^2+1.
\]

因此这样的 c 至多 tau(|uv-1|) 个。对任意 eta>0，标准初等界
tau(a)<=A_eta a^eta 给至多 O_eta(C^(2eta)) 个。
为使输入完整，约数界可由素数幂分解直接证明：当
p>=2^(1/eta)，k+1<=2^k<=p^(eta k)；对有限多个较小素数，
sup_(k>=0)(k+1)p^(-eta k) 有限。把这些有限常数相乘即可。

在当前盒子里，(signed-inverse-weight) 不超过
min(H,C/U)min(K,C/V)。所以盒子的全部非例外贡献不超过

\[
 C_\eta C^{2\eta}UV\min(H,C/U)\min(K,C/V)
                         \le C_\eta C^{2+2\eta}.
 \tag{one-box-bound}
\]

这里允许把实际代表及互素限制放宽，因为所有权重非负。
盒子至多 O(log^2(2C)) 个。取 eta=epsilon/4，再把对数吸收
进 C^(epsilon/2)，得到 O_epsilon(C^(2+epsilon))。
合并 uv=1 与 c=1 的贡献，证明 (dyadic-positive-envelope-average)。

这个证明没有用 Weil 界，也没有对模数逐个估计后再丢失平均。
例外整数双曲线 uv=1 正是 CHK 项的来源。

这一项不能删去：若 C>=3 为整数且 H=K=C，则每个
C<=c<2C 的两对 (1,1),(-1,-1) 实际贡献 c^2/2，故其和
至少 C^3/2。它不可能被一个统一的 O(C^(2+epsilon)) 包住
（取0<epsilon<1）。这也提供了删除 uv=1 分支的精确反例。

### 2.3 累积形式及矩形和的推论

将 1<=c<=C 用标准二进区间覆盖，由几何级数得到

\[
 \sum_{c\le C}B_c(H,K)\ll_\epsilon C^{2+\epsilon}+CHK.
 \tag{cumulative-positive-envelope-average}
\]

最后一个块可多覆盖一些模数，因为所有项非负。
特别地，对整数 M,N>=1，以及任意各含不超过 M,N 个整数的
区间 I,J，

\[
 \sum_{c\le C}\left|\sum_{m\in I,n\in J}\operatorname{Kl}_c(m,n)\right|
     \ll_\epsilon C^{2+\epsilon}+CMN
     \ll_\epsilon(CMN)^\epsilon C(C+MN).
 \tag{actual-incomplete-Kloosterman-average}
\]

这给出当前路线需要的 DI Theorem 14 型输入，同时保留更强的
正包络版本。即使 I,J 随 c 改变，只要长度上界相同也仍成立。
但没有声称系数可换成任意复数，或添加任意实线性相位。

## 3. 二维 Abel：端点与混合导数全部保留

设 N>=1，I,J 为 [N,2N] 中的整数区间，h 属于
C^2([N,2N]^2)。记

\[
 A_c(s,t)=\sum_{\substack{m\in I,\ m\le s\\n\in J,\ n\le t}}
                         \operatorname{Kl}_c(m,n).
\]

前缀各含至多 N+1<=2N 个整数，故
|A_c(s,t)|<=B_c(2N,2N)。有限和的二维分部求和精确给

\[
\begin{aligned}
 \sum_{m\in I,n\in J}\operatorname{Kl}_c(m,n)h(m,n)
 ={}&A_c(2N,2N)h(2N,2N)\\
 &-\int_N^{2N}A_c(s,2N)h_s(s,2N)ds\\
 &-\int_N^{2N}A_c(2N,t)h_t(2N,t)dt\\
 &+\int_N^{2N}\int_N^{2N}A_c(s,t)h_{st}(s,t)dt\,ds.
\end{aligned}
 \tag{exact-two-dimensional-Abel}
\]

即使下端点 N 本身为整数且属于 I 或 J，等式仍成立：逐个
固定 (m,n) 展开右边，它的系数就是二维微积分基本定理给出的
h(m,n)。不遗漏下端点原子，也不需要另外的端点为零假设。

定义实际变差预算

\[
\begin{aligned}
 V_N(h)={}&|h(2N,2N)|
 +\int_N^{2N}|h_s(s,2N)|ds
 +\int_N^{2N}|h_t(2N,t)|dt\\
 &+\int_N^{2N}\int_N^{2N}|h_{st}(s,t)|dt\,ds.
\end{aligned}
\]

于是

\[
 \left|\sum_{m\in I,n\in J}\operatorname{Kl}_c(m,n)h(m,n)\right|
                          \le V_N(h) B_c(2N,2N).
 \tag{weighted-rectangle-envelope}
\]

这是先有逐 c 的、控制所有前缀的正包络，再对 c 求和；不是
从“每个固定端点的平均界”无理由推“所有端点上确界的平均界”。

## 4. 实际小尺度核的带权几何预算

沿用前序固定 b>=0、b 属于 C_c^infty((1,2))、integral b(u)du/u=1。
给 Y>=1 置 delta=1/(64Y)，Phi_delta(x)=b(x/delta)-b(x/(2delta))。
对 m,n in [N,2N]，核非零要求

\[
                   64\pi NY\le c\le512\pi NY.
 \tag{actual-modulus-support}
\]

这是从 delta<=4pi sqrt(mn)/c<=4delta 得到的宽松闭支撑。
令 h_c(s,t)=Phi_delta(4pi sqrt(st)/c)，并写
G(u)=b(u)-b(u/2)、u=4pi sqrt(st)/(c delta)。在上述整个 c 范围及
[N,2N]^2 内均有 1/2<=u<=8，且

\[
 (h_c)_s=\frac{uG'(u)}{2s},\qquad
 (h_c)_t=\frac{uG'(u)}{2t},\qquad
 (h_c)_{st}=\frac{u^2G''(u)+uG'(u)}{4st}.
\]

因此 V_N(h_c)<=C_b，一致于 N,Y,c。由第3节，实际带核矩形
绝对值 <=C_b B_c(2N,2N)。

更一般，若 |w(c)|<=A tau(c)，则第2节和支撑的固定倍数给

\[
 \boxed{\left|\sum_c\frac{w(c)}c
      \sum_{m\in I,n\in J}\operatorname{Kl}_c(m,n)
                       \Phi_\delta(4\pi\sqrt{mn}/c)\right|
         \ll_{b,A,\epsilon}(NY)^\epsilon(NY+N^2).}
 \tag{actual-weighted-small-scale-budget}
\]

证明中 c 与 NY 可比，tau(c)<<_(epsilon/2)c^(epsilon/2)，
而固定倍数支撑上的 B_c 总和
<<_(epsilon/2)(NY)^(2+epsilon/2)+(NY)N^2。
除以 c 的尺度 NY，得到所述预算；第二项的额外幂也可放宽到
(NY)^epsilon。这一步没有丢掉 Kuznetsov 原有的1/c。

## 5. 来源与证明边界

原刊对照为 Deshouillers--Iwaniec，Section 8.3，pp.275--277，
[原刊扫描](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0070/LOG_0027.pdf)。
原刊从 Fourier 正主化和先前谱估计推出 Theorem 14；本篇在
当前所需区间对象上给出完整的模逆/约数计数证明，不依赖尚未
完成的一般变化尺度谱输入。不声称这是新的文献结论。

下一篇把 (actual-weighted-small-scale-budget) 接到实际 trace
公式，证明区间系数异常谱强化。本篇自身不证明完整 DI11、
Conrey 均方主项或最终严格 >2/5，也不声称已作 Lean 验证。

### English summary

The incomplete Kloosterman average is proved through a positive envelope
for all interval rectangles. Signed modular inverses satisfy c | uv-1;
the nonzero case is counted by divisors, while uv=1 contributes CHK.
This yields a uniform envelope average C^(2+epsilon)+CHK. Two-dimensional
Abel summation retains all boundary and mixed-derivative terms, giving
the actual compensated-kernel budget (NY)^epsilon(NY+N^2), including
the geometric 1/c factor. No additional spectral theorem is assumed.
