# 全局 Ramanujan principal：一般外层计数与无限尺度补偿

白话结论：原第二次 Poisson 的精确恒等式保留，但不能把它的无限
K 分解直接当作对数多个包。极小 K 的原整数格为空，却有连续零频；
其全部非零频必须先合并成这个零频的负数。本文支付该补偿、大尺度
尾和非驻相全频尾，并把 WC≈M 的顶面计数改成一般 WC≲min(M,S)。
所得是**全局** D+J_Ram≪T^(1+ε)，不是任一局部 principal 的同界。
完整 centered gate、twisted moment 和零点排除仍未证明。

## PT1. 来源、替换范围和命题

定义源为 49cfacd70c60372757280177c7b63fd4f7760817；审计基线为
7cf2e7d43c4365e38e2aa708d1a250694b698bec 的
[原稿](2026-08-24-mobius-weighted-off-diagonal.md) (2.5)、(9.690)、
(9.975)–(9.980)。本文替换 (9.983) 对无限全 K 的未限定用法及
(9.984) 后“只有对数多个包”的直接推断，不撤回那些有限恒等式。
本命题不使用 §9.144 的二次 resonant projector，也不把其估计
改称一个线性和的估计。

取 T≥2，2≤N≤T³，原 W∈C_c^∞((1,2))、原 AFE 权 V_t 和原 dyadic
分割 F_K(y)=F(y/K)，K∈2^Z；F 支持在 [1/2,2]，局部重叠有界，
Σ_K F_K(y)=1 (y>0)。允许有符号 F，但 Σ_K|F_K(y)| 有界。
所有常数可依赖 W、F 的有限多个半范数。使用原全阶导数界
\[
 x^jT^k|\partial_x^j\partial_t^kV_t(x)|
       \ll_{A,j,k}(1+x/T)^{-A}.                         \tag{PT1}
\]
这不是仅给定 J=6 的任意核类；任意小尾可调用所需有限高阶原权导数。

q₀ 为原 gcd；q₀,r,s 均平方自由，(q₀,r)=(q₀,s)=(r,s)=1，q₀r,q₀s≤N。
因此原 μ(q₀)²=1；平方因子 q₀ 的原系数为0，不纳入显示的和。
继承的 **s 平方自由条件必须保留**，即 s=uwc 的 u,w,c 两两互素且
平方自由；(9.975) 中没有 μ(c)，不能用其显示系数自动排除平方因子。
所有下述和保留原 μ、p_N、F_R、F_S；上界仅利用它们的模长预算。

令 J_Ram^(2),≠0 按 PT3 的求和次序定义。则对任意 ε>0，
\[
 |D+J_{\rm Ram}|=|J_{\rm Ram}^{(2),\ne0}|
                 \ll_{\epsilon,W,F}T^{1+\epsilon}.     \tag{PT2}
\]
结论包括原 q₀ 聚合、全部正负 δ 和全部 K,M，不假设 H、L 内部关系。
这里 J_Ram 包括原 Poisson h=0 项与所有 h≠0 的 Ramanujan 投影。
它既不是一个固定 H/L 箱，也不是 FP3 中 μ(q)/φ(q) 项的局部和。

## PT2. 完整系数与唯一 deleted origin

置 m=nwc，y=(ncr+x)/(uc)，y₀=nr/u，n≥1。原函数为
\[
 \Psi(x)={F_M(m)F_K(y)\over\sqrt{my}}
   \int W(t/T)V_t(my)\exp(it\log(y/y_0))\,dt,
 \qquad y>0,                                           \tag{PT3}
\]
并在 y≤0 延拓为0。固定 K,M 时是光滑紧支函数。
原 (9.975) 在 Ψ 前的系数化简为
\[
 B_{q_0,r,u,w,c}=
 {2\mu(r)\mu(u)\mu(w)w\over q_0\varphi(s)\sqrt{rs}}
      p_N(q_0r)p_N(q_0s)F_R(r)F_S(s).                  \tag{PT4}
\]
尤其因子2已经包括两个 AFE 方向，不再加一次。
采用 \(\widehat\Psi(\xi)=\int\Psi(x)e(-\xi x)dx\)，逐包有
\[
 \sum_{x\ne0,(x,u)=1}\Psi(x)
 ={1\over u}\sum_k c_u(k)\widehat\Psi(k/u)
             -{\bf1}_{u=1}\Psi(0).                    \tag{PT5}
\]
完整 K 零模由原 Mellin 零点消去：
\[
 \sum_K\widehat\Psi(0)=
 {ucF_M(m)\over\sqrt m}\int W(t/T)y_0^{-it}
       m^{-s_t}{G_t(s_t)g_t(s_t)\over s_t}dt=0,
 \quad s_t=\tfrac12+it.                               \tag{PT6}
\]
对固定 m,T，积分绝对收敛：y=0 端的 majorant 为 y^(-1/2)，
无穷端由 PT1 支付。这也给 Σ_K|hatΨ(0)|<∞，故分割与积分可换序。
G_t(s_t)=0 是原 AFE 的特性，不能移植到任意 Fourier/Mellin 权。

deleted origin 仅 u=1 存在。逐平方自由 s，
\(\sum_{w\mid s}w\mu(w)=\mu(s)\varphi(s)\)，且此时
m₂=ns,m₁=nr。与 PT4 相乘后，PT5 的 deleted origin 正好为 −D。
这解释 PT2 左边的 **D+J_Ram**，而不是声称 J_Ram 自身逐块很小。

## PT3. 先完整零模，再大 M 的有符号还原

先固定有限的 q₀,r,s,u,w,c,n,M，按 PT5 作 k 和，再对 K 合并；
每个固定 K 的 k 和是 Schwartz 可和的。**不先对无限 K 的 k≠0
双重和取绝对值。** PT6 后有
\[
 \sum_K{1\over u}\sum_{k\ne0}c_u(k)\widehat\Psi(k/u)
 =\sum_K\left\{\sum_{x\ne0,(x,u)=1}\Psi(x)
                       +{\bf1}_{u=1}\Psi(0)\right\}. \tag{PT7}
\]
下文证明左侧按此顺序收敛；也可先取有限 K 后令端点趋无穷。
右侧是原格加 deleted-origin 补偿，不能把两边称为逐频绝对等式。

在右侧原格，j=ncr+x 是正整数，故
\[
 y={j\over uc}\ge {1\over uc}\ge {1\over N},\qquad
 my={nwj\over u}\ge {m\over N}.                       \tag{PT8}
\]
包括 x=0 的补偿也满足该正格条件。抛开单位条件给合法 majorant。
在 PT1 中留出两次衰减，所有 n,j 的绝对和有
\[
 T\sum_{n,j\ge1}\sqrt{u\over nwj}
           (1+nwj/(uT))^{-2}
 \le T^3(u/w)^{5/2}\zeta(5/2)^2.                      \tag{PT9}
\]
若 M>T⁸，支持给 m>T⁸/2，所以 my/T≳T⁴。另取 A 次衰减后，
大 M 的**完整有符号** PT7 总费用≪_A T³N^(17/2)T^(-4A)。
这里刻意粗计 |B|≪N 和至多 N⁵ 个 q₀,r,u,w,c；R,S 分割有界重叠。
因此任给 D>0，取 A 足够大即为 O_D(T^(-D))。
大 M 不需要分别估计其连续零模与非零模。

余下只保留 1/2≤M≤T⁸，m≤2T⁸；n 的范围现为有限。
下面分别处理 K 的两端，之后才可说 K,M 都只有 O(log T) 个包。

## PT4. 小 K：空格不等于零 dual contribution

若 K<T^(-8)，2K<1/N。由 PT8，原离散格为空；y₀=nr/u≥1/N，
所以 Ψ(0) 也为0。**逐原行的准确公式是**
\[
 \sum_{k\ne0}c_u(k)\widehat\Psi(k/u)
                   =-\varphi(u)\widehat\Psi(0).         \tag{PT10}
\]
不能把右侧漏掉，也不能从空格推论 Σ|c_u(k)hatΨ(k/u)|=0。

在 hatΨ(0) 中置 y=Kz，z 在固定紧区间；相位导数为 t/z，模长≳T。
对 z 积分分部 J 次，PT1 与 F 的边界平坦性给
\[
 |\widehat\Psi(0)|
 \ll_J T^{1-J}uc\sqrt{K/m}(1+mK/T)^{-A}.               \tag{PT11}
\]
K 尾的 Σ√K≪T^(-4) 是几何和，不付无限个对数包。
用 φ(u)/u≤1、|B|≪N，及
\(\sum_{nwc\le2T^8}uc/\sqrt{nwc}\ll (u/w)T^4\)，
PT10 的全小 K 补偿≪_J N⁷T^(1−J)≤T^(22−J)。
取 J>D+23 即为 O_D(T^(-D))。这证明的是有符号合并后的尾。

## PT5. 大 K：原格与连续零模两笔都支付

若 K>T⁸，则 y>T⁸/2，m≥1，故 my/T≳T⁷。由 PT5，非零频的
**整体**为原格加 origin 减 (φ(u)/u)hatΨ(0)。前两笔用 PT9 并另取
A 次衰减，费用≪_A T³N^(17/2)T^(-7A)。

连续零模无需振荡即可得
\[
 |\widehat\Psi(0)|
 \ll_A T uc\sqrt{K/m}(1+mK/T)^{-A-2}.
                                                               \tag{PT12}
\]
留出 T^(-7A) 后，dyadic 和
Σ_K √K(1+mK/T)^(-2)≪√(T/m)。再对 n≤2T⁸/(wc) 求和只付调和
对数，故该笔全费用≪_A T^(3/2)N⁷log(2T)T^(-7A)。同样任意幂小。
PT5 不能仅通过“原 m₁ 整数的 AFE 尾”支付：此处 y 是分母 uc 的
有理格，PT8 正是保留该分母后的真实论证。

至此留下
\[
 1/2\le M\le T^8,\qquad T^{-8}\le K\le T^8.            \tag{PT13}
\]
对于小 T 的 dyadic 边缘常数只需扩大上述固定截断，所有端点均可
分配给保留区；不丢半开壳的整数1。

## PT6. 非驻相全 k 的可和预算

令 \(\lambda=KS/(MR)\)，固定宽紧区间 I⊂(0,∞)，使 λ∉I 时整个
支持上的 y/y₀ 与1固定分离。由 PT3，Fourier 因子为
\(e(k ncr/u)e(-kc y)\)，因此先在 t 积分分部，再对足够大的
|k|cK/T 在 y 积分分部，有对任意 J,B 的一致界
\[
 |\widehat\Psi(k/u)|
 \ll_{J,B}T^{1-J}uc\sqrt{K/M}
                    (1+|k|cK/T)^{-B},\qquad\lambda\notin I.
                                                               \tag{PT14}
\]
说明：小 |k| 时只用 t-IBP；大 |k| 时 y 相位导数以 |k|cK 为主，
其余相位导数 O(T)。PT1 控制所需混合导数，log(y/y₀) 的倒数及其
尺度导数在该域有界。所得常数不依赖保留区内的 R/S 或 M/K 比。

由 \(c_u(k)=\sum_{d\mid(u,k)}d\mu(u/d)\)，对任意 X>0，
\[
 \sum_{1\le k\le X}|c_u(k)|\le\tau(u)X,\qquad
 \sum_{k\ne0}|c_u(k)|(1+|k|/X)^{-B}\ll_B\tau(u)X.
                                                               \tag{PT15}
\]
第二式取 B>1，由分部求和得到，**也适用于 X<1**；不用错误的 O(X+1)。
在 PT14 中取 X=T/(cK)，再乘 PT4/u、φ(s)^(-1)≪_ε s^(-1+ε)，
及 PT8 原非空行的计数，得到每 W,C 层
\[
 \ll_{J,\epsilon}{T^{2-J+\epsilon}\over q_0 C}
                         \sqrt{RM\over SK}.           \tag{PT16}
\]
PT13 及 1/2≤R,S≲N 给根号≪T^(19/2)。所有剩余尺度只有对数多个，
Σ_{q₀≤N}1/q₀≪log(2N)，Σ_{C dyadic,C≥1/2}1/C≪1。
选 J 足够大后，PT16 的全部非驻相频率任意幂小。

## PT7. 驻相区与一般 WC≤min(M,S) 的计数

现 λ∈I，故 K≈MR/S。令
\[
 A_k=2\pi k ncr/u,\qquad X_0=n^2wcr/u.
\]
在 k>0、A_k≈T 时，变换 x=ncr(v−1)、t=A_kτ 给相位
\(A_k\{\tau\log v-(v-1)\}\)。唯一临界点 (1,1)，Hessian 行列式−1，
临界相位0。紧支二维驻相给
\[
 \widehat\Psi(k/u)=2\pi F_M(m)\sqrt{ucr/w}
             F_K(nr/u)W(A_k/T)V_{A_k}(X_0)
                  +O(T^{-1}\sqrt{ucr/w}).              \tag{PT17}
\]
所用标准公式可对照 [Jordan Bell 的驻相笔记 §2](https://jordanbell.info/LaTeX/mathematics/stationaryphase/)；
这里 Hessian 的 signature 为0，故没有额外复相位。下述统一性由
本处固定支集和 PT1 检查，不从该参考的一般表述中免费推得。
如临界点在支集外主项为0；用光滑延拓解释边缘，不作硬截断。
PT1 使幅度的所需尺度导数一致有界。k<0 及 A_k/T 离开固定正紧集
时，对联合梯度积分分部，和 PT14 一样保留可和的 k 权。因此
\[
 \sum_{k\ne0}|c_u(k)\widehat\Psi(k/u)|
 \ll_\epsilon T^\epsilon {T\over cK}\sqrt{ucr/w}.
                                                               \tag{PT18}
\]
若 T/(cK)<1，PT15 仍适用。PT18 **只用于 PT13 内的 λ∈I**，
不是一个可在所有极小 K 上再取绝对值的总命题。

把平方根与原系数消去是关键一步：
\[
 {2w\over q_0u\varphi(s)\sqrt{rs}}\sqrt{ucr/w}
                         ={2\over q_0u\varphi(s)}.     \tag{PT19}
\]
置 w≈W,c≈C,u≈S/(WC)，n≈M/(WC)。非空时各整数长度至少是固定
正数（用 [Z/2,2Z] 壳则 Z≥1/2），故计数中的 1+length 可吸收，
且只要求 WC≲min(S,M)，**不要求 WC≈M**。行数为
\[
 \#(r,u,w,c,n)\ll R\cdot{S\over WC}\cdot W C\cdot{M\over WC}
                         ={RSM\over WC}.              \tag{PT20}
\]
先逐行估计后再计数，不会因 s=uwc 的相关性低估；抛弃互素条件只
增加计数。PT18–PT20 给该完整 W,C 层
\[
 |J_{q_0;R,S,K,M;W,C}^{(2),\ne0}|
 \ll_\epsilon {T^{1+\epsilon}RM\over q_0SKC}
 \ll_\epsilon {T^{1+\epsilon}\over q_0C}.               \tag{PT21}
\]
当 WC≈M 时与旧 (9.984) 一致；当 WC≪M 时新增 n 长度不能遗漏。
Σ_C 1/C 为有界几何和，W,R,S,K,M 及 q₀ 调和和只付对数，取内部
ε 较小即可得到 PT2。驻相误差多 T^(-1)，同一计数支付。

PT7 对保留的有限 dyadic 包给全 k 绝对可和；PT4、PT5 对两端给
逐行有符号可和；PT3 给大 M 的完整有符号可和。这些明确的顺序及
majorant 允许最终取极限，没有使用未证明的原 off-diagonal 尾界。

## PT8. 覆盖、未覆盖与下游依赖

新增支付的是全局 principal 的一般 WC≪M 层、无限小/大 K 和
非驻相全 k 尾。最坏的保留 C=1 层达到 T 预算；本篇不把修补原
证明缺口包装成额外 e-Möbius saving 或新的非零谱节省。

原完整恒等式 I=D+J_Ram+C° 现在可在这一**同一全局分账**中使用
PT2 一次。只有某个有符号线性子族已逐系数证明是 C° 的一部分，
才可把其中心化上界与仍未估计的 C° 补集并列；不能将 PT2 赋给
该子族的 μ(q)/φ(q) 局部项。EE*、EC*、CE*、CC* 的联合能量问题
也没有因此消失。

对此移交，有限系数核对是明确的：平方自由 s，d=(s,hδ)，q=s/d 时，
\[
 {c_s(h\delta)\over\varphi(s)}={\mu(q)\over\varphi(q)}.   \tag{PT22}
\]
FP3 的 s=eq,h=eu,δ=ev 及 (uv,q)=1 给 d=e；canonical 的同一 masks
给 d=abe。因此在原权和外因子不变时，CS1 的 centered 核确为 C°
在该线性子族上的限制，不是另一种均值。若 A 选择这样的有限原包，
则准确有 I=J_Ram^(2),≠0+C°_A+C°_(A补集)。可单独支付已经证明的
C°_A，但该选择之外的所有 gcd、q₀、尺度和尾必须保留。PT22 只识别
分账，不把局部上界擅自汇总为所有 q₀/所有尺度的上界。

依赖核对：PR507 冻结 a24e1dca 的 CA2–CA13 使用原 FP1/Type 核、
加性大筛和全部 masks，自行支付其局部 principal，不使用 §9.147。
PR509 冻结 0d468dd0 的 CS15 只估计 centered FP3，CS17 保留局部
principal。本文不改变两者的定理或冻结 SHA；不自动认证它们的
全部外层/非内部移交，更不认证 XI 的共同 Π 或 amplified b 迁移。

附带有限脚本只检查 PT4/PT19 的系数、一般长度计数、Ramanujan
有限部分和、正有理格端点和“空格仍有非零频补偿”的反例。
它不证明 PT1、驻相、积分换序、无限尾或 PT2；这些依赖上述解析证明。

English summary: the global second-Poisson principal estimate requires
ordered scale summation. Empty small-K lattices retain an exact signed
zero-mode compensation. Rational-lattice tails and frequency-weighted
integration by parts justify the truncations. General W,C counting then
costs T/(q₀C). This repairs the global principal proof only.
