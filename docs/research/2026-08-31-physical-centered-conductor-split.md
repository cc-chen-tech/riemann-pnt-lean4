# 真实 FP3 中心化线性和：完整 Möbius 容斥与高低导子分割

白话结论：先保留 e、n 两个 Möbius 系数并完整展开互素条件，再把
e 侧的新整数与两个标签合成一个三因子产品。高有效导子用共同列
乘法大筛，低有效导子对两个光滑标签分别用 Pólya–Vinogradov。
所得中心化部分在平衡内部 E≥T^(7/4) 满足局部 T^(1+ε) 预算。
但原 principal 仍保留，当前单独绝对上界在 E<T² 不足；
所以这不是完整 FP3 的更低 E 覆盖，更不是 14/17 或 2/3 零点排除。

本篇只继承冻结 933bb6087d399d006c6963489b7e2cda22e2ba24 的
[产品稿 P1–P10](2026-08-31-physical-product-label-l2.md) 所用真实 FP3
原式及内部光滑条件。原定义仍是 MWKF-PHYS-v1；不改任何冻结父分支。
这里不使用 canonical a/b/e 扩展，也不使用旧 §9.144 的二次共振
projector 作为线性上界；两者不是同一对象。

## CS1. 在同一原式内同时定义 centered 与 principal

固定平方自由 q₀。原双整除族为
\[
 e\asymp E,\quad q\asymp Q,\quad s=eq,\ r=n,\ h=eu,\ \delta=ev,
 \quad EQ\asymp S,\qquad u,v\ne0,
\]
其中 e,q 平方自由，(e,q₀q)=(n,q₀eq)=(uv,q)=1。
所有原 mollifier 支持和光滑壳保留。记
\[
 W(n,e,q,u,v)=p_N(q_0n)p_N(q_0eq)
       \Psi(n/R,eq/S,ev/L,eu/H).
\]
采用包含整数1的半开 dyadic 约定；q=1 按唯一剩余类解释。
内部 HL≲RS/T，尺度在固定 T 幂范围内，q₀n,q₀eq≤N/2。
J≥6 的原半范数记为 \(\mathcal A_J\)。定义
\[
 \begin{split}
 \mathcal C&={2T\over q_0RS}\sum
 \mu(e)\mu(q)\mu(n)W
       \left\{e_q(-euv\bar n)-{\mu(q)\over\varphi(q)}\right\},\\
 \mathcal P&={2T\over q_0RS}\sum
                 {\mu(e)\mu(n)\over\varphi(q)}W,\qquad
 \mathcal O=\mathcal C+\mathcal P.                         \tag{CS1}
 \end{split}
\]
两个和的支持完全相同。P 中没有 μ(q)，因为原 μ(q) 与均值 μ(q)
相乘为1。C 在 q=1 时为0，不意味着原 q=1 行不存在。
这只是一次精确线性分解，不从任何二次能量中删除交叉项。

## CS2. 完整互素容斥先于 Cauchy

在尚未取绝对值时使用
\[
 {\bf1}_{(e,n)=1}=\sum_{f\mid(e,n)}\mu(f),\qquad
 e=fa,\quad n=fb.
\]
逐项有
\[
 \mu(f)\mu(fa)\mu(fb)
 =\mu(f)\mu(a)\mu(b){\bf1}_{(ab,f)=1},\qquad
 e_q(-fa uv\,\overline{fb})=e_q(-a uv\bar b).               \tag{CS2}
\]
右边 f,a,b 均平方自由（否则系数为0），并保留
\[
 (fab,q_0q)=1,\quad(ab,f)=1,\quad(uv,q)=1.
\]
**不再添加 (a,b)=1**；这会破坏完整容斥。这里 a,b 是 CS2 的商，
不是 canonical gcd 分配。f 也不是后面的有效导子或加性 Type gcd。
原 f=1、a=1、b=1 端点全部在；f≤2min(E,R)。

置
\[
 A=E/f,\quad B=R/f,\quad U=H/E,\quad V=L/E,\quad
 K=AUV=K_0/f,\qquad K_0=HL/E.                              \tag{CS3}
\]
实际权为
\[
 \Psi(fb/R,fa q/S,fa v/L,fa u/H).
\]
必须用五变量 \(b/B,a/A,q/Q,u/U,v/V\) 分离，不能直接照搬四变量
分离。第二至第四坐标分别为
\((EQ/S)(a/A)(q/Q),(a/A)(v/V),(a/A)(u/U)\)。
在固定紧盒上所有缩放和导数一致有界。内部 p_N(q₀fa q) 也纳入
光滑权，p_N(q₀fb) 可留在 b 的单变量系数。

若 Fourier 指标为 ν∈Z⁵，Abel–PV 所需的精确预算是
\[
 \sum_\nu |c_\nu|(1+|\nu_u|)(1+|\nu_v|)
        \ll \mathcal A_J.                                \tag{CS4}
\]
用 Sobolev–Parseval 与 Cauchy，其平方余因子是
\(\sum_\nu(1+|\nu_u|)^2(1+|\nu_v|)^2(1+|\nu|^2)^{-s}\)，
在 s>9/2 收敛；J≥6 足够。延拓 cutoff 的固定常数计入预算。
原连续积分支持不另作硬切割。a,b 的一维整数壳保留，u,v 的正负
壳以及零标签排除分别处理；空域为0，非空时 A,B,U,V≥1/2。

## CS3. 按真正的 primitive conductor 分解

对单位 x mod q，
\[
 e_q(x)-{\mu(q)\over\varphi(q)}
 ={1\over\varphi(q)}
      \sum_{\chi\bmod q,\ \chi\ne\chi_0}
                  \tau_q(\bar\chi)\chi(x).                \tag{CS5}
\]
每个 χ 唯一由 primitive χ* mod ℓ>1 诱导，q=cℓ 平方自由、
(c,ℓ)=1。此时
\[
 \tau_{c\ell}(\bar\chi)=
       \mu(c)\bar\chi^*(c)\tau_\ell(\bar\chi^*),\qquad
 \mu(q)\tau_q(\bar\chi)=
       \mu(\ell)\bar\chi^*(c)\tau_\ell(\bar\chi^*).         \tag{CS6}
\]
外 μ(q) 并未丢掉；特别是 \(\bar\chi^*(c)\) 不能删除。
平方自由偶模数也在此唯一分层中，不能虚构导子2的 primitive 角色。

对固定 f,c 和一个分离原子，中心化行准确为
\[
 {\mu(f)\over\varphi(c)}
 \sum_{\ell\asymp Q/c}{\mu(\ell)\beta_{c\ell}\over\varphi(\ell)}
 \sum_{\chi^*\bmod\ell}^{\rm primitive}
 \bar\chi^*(c)\tau_\ell(\bar\chi^*)\chi^*(-1)
                 A_\chi U_\chi V_\chi B_{\bar\chi}.
                                                               \tag{CS7}
\]
此处 ℓ>1，c、ℓ 平方自由，(c,fq₀)=(ℓ,fq₀c)=1；β 是分离
的模数因子，不含已经明确融合的 μ(q)。归一化后 |β|≤1，
原子外系数另由 CS4 支付。例如
\[
 \begin{split}
 A_\chi&=\sum_{(a,fq_0c)=1}\mu(a)\alpha_a\chi^*(a),&
 B_{\bar\chi}&=\sum_{(b,fq_0c)=1}\mu(b)x_b\bar\chi^*(b),\\
 U_\chi&=\sum_{u\ne0,(u,c)=1}y_u\chi^*(u),&
 V_\chi&=\sum_{v\ne0,(v,c)=1}z_v\chi^*(v).
 \end{split}
\]
各系数在 CS3 的一变量范围内，模长≤1；y、z 的 BV 费用见 CS4。
所有 ℓ-unit 条件由 primitive 角色的零延拓提供。
这些 a,b,u,v 序列对变化的 ℓ 共同，但不要求跨 f,c 共同。
此处 ℓ 是乘法角色的 primitive conductor，不是加性 Type k 的 gcd。

## CS4. 高导子：两个真正共同的 Dirichlet 多项式

给定 1≤Z≤Q，先估计 ℓ>Z。固定 f,c 后，把 \(A_\chi U_\chi V_\chi\)
合并为乘积 m=auv 的系数 t_m。原 c-unit 掩码与 (a,fq₀)=1 均在
系数定义中，且不依赖 ℓ。有 |m|≤8K；每个 m≠0 的表示数
≤2τ₃(|m|)，总表示数≤32K。因此
\[
        \sum_m|t_m|^2\ll_\epsilon T^\epsilon K.            \tag{CS8}
\]
两个符号区分别使用大筛（或在一个整数区间内零延拓）。
b 列平方范数≪B。通常的
[乘法大筛 Theorem 16.2](https://kskedlaya.org/ant/chap-largesieve2.html)
对共同系数给
\(\sum_{\ell\asymp L}\sum_{\chi^*}|X_\chi|^2
\ll (L^2+\text{长度})\|\text{系数}\|_2^2\)。
因 L≈Q/c，|τℓ|=√ℓ，CS7 的系数绝对值≪T^ε/√(cQ)。
在 (ℓ,χ*) 上一次 Cauchy 得
\[
 {T^\epsilon\over\sqrt{cQ}}
       \sqrt{BK(B+Q^2/c^2)(K+Q^2/c^2)}.                  \tag{CS9}
\]
不假设 Q²≤B,K；大 f 时该假设不成立。将 CS9 展开为四个平方根，
并对 c≤2Q/Z 求和，得到
\[
 T^\epsilon\{BK/\sqrt Z+
       \sqrt Q(B\sqrt K+K\sqrt B)+Q^{3/2}\sqrt{BK}\}.     \tag{CS10}
\]
所用 c 幂分别为 −1/2、−3/2、−3/2、−5/2。
第一个部分和≪√(Q/Z)，其余收敛。
对 f 求和后高导子费用为
\[
 T^\epsilon\left\{
 {RK_0\over\sqrt Z}
 +\sqrt Q(R\sqrt{K_0}+K_0\sqrt R)
 +Q^{3/2}\sqrt{RK_0}\right\}.                            \tag{CS11}
\]
f 幂分别为 −2、−3/2、−3/2、−1；末项原有 log(2min(E,R))，
仅在已声明固定幂尺度下吸收进 T^ε。

## CS5. 低导子：两个光滑标签先做 PV

现在固定 f,c、primitive χ* mod ℓ>1。保留完整 c-unit mask，
\[
 \sum_{(u,c)=1}b_u\chi^*(u)
   =\sum_{j\mid c}\mu(j)\chi^*(j)
                        \sum_m b_{jm}\chi^*(m).
                                                               \tag{CS12}
\]
每个权 b(jm) 的 BV 范数由原 Fourier 标签因子的
1+|ν_u| 控制，不随 j 增长。原正负有限区间的端点用 Abel 求和保留。
经典 Pólya–Vinogradov 给内和
≪BV(b)√ℓ log(2ℓ)，v 标签同理。因此
\[
 |U_\chi V_\chi|
 \ll T^\epsilon(1+|\nu_u|)(1+|\nu_v|)\ell.               \tag{CS13}
\]
所有 τ(c)² 及对数均已计入 T^ε。这里没有对 μ(a)、μ(b) 使用 PV；
它们只给 |Aχ Bχ|≪AB。
对 ℓ≈L≤Z、c≈Q/L，利用
\(\sum_{c\asymp Q/L}1/\varphi(c)\ll T^\epsilon\)，
以及 primitive 角色数≤φ(ℓ)，CS7–CS13 给
\[
 \ll T^\epsilon AB\sum_{\ell\asymp L}\ell^{3/2}
 \ll T^\epsilon AB L^{5/2}.
 \quad\hbox{合并所有低层及 f 后为 }T^\epsilon ER Z^{5/2}.
                                                               \tag{CS14}
\]
没有删除 imprimitive cofactor，也没有把 principal 当作 PV 的输入。
所用仅是经典 PV，参见
[Granville–Soundararajan 文中回顾](https://arxiv.org/abs/math/0503113)；
不使用其更强的结构性结果。

## CS6. 原物理预算、真正改善和仍未估计的项

合并 CS4 的 projective 费用，恢复唯一外权，得到
\[
 \boxed{
 |\mathcal C|\ll_\epsilon{\mathcal A_J T^{1+\epsilon}\over q_0RS}
 \left\{
 {RHL\over E\sqrt Z}+ER Z^{5/2}
 +\sqrt Q\left(R\sqrt{HL/E}+{HL\over E}\sqrt R\right)
 +Q^{3/2}\sqrt{RHL/E}\right\}.}                           \tag{CS15}
\]
这估计 CS1 的整个中心化 FP3 线性和，允许所有平方自由 q、全部
primitive/imprimitive 角色与所有 f，不是固定导子模型。
有限高度使用显式 divisor/BV/log 预算，不免费把 T^ε 设为1。

在 q₀=1，R=S≈T³，H=L≈T^(5/2)，E≈T^η，
3/2≤η≤5/2，Q≈T^(3−η) 时，取
\[
 Z=(HL/E^2)^{1/3}\asymp T^{(5-2\eta)/3}\in[1,Q]
\]
（端点常数以截断到 [1,Q] 处理）。CS15 的指数分别为
\[
 {13\over6}-{2\eta\over3},\quad
 {13\over6}-{2\eta\over3},\quad
 2-\eta,\quad 3-{3\eta\over2},\quad {7\over2}-2\eta .
                                                               \tag{CS16}
\]
第一项在此区间主导，故 η≥7/4 足以给
\(|\mathcal C|\ll\mathcal A_J T^{1+\epsilon}\)；
例如 η=19/10 时为 T^(9/10+ε)。原产品稿在该参数的总绝对
界为 T^(11/10+ε)，但**不能据此称原 O 也变成 T^(9/10)**：
\[
 |\mathcal P|\ll_\epsilon{\mathcal A_J T^{1+\epsilon}\over q_0RS}
                           {RHL\over E},
 \qquad\text{平衡指数 }3-\eta.                            \tag{CS17}
\]
η=19/10 时它仍是11/10。要控制原 O，必须另支付 P，或者把它
与原全局 principal/AFE 对角及剩余 signed 项精确重组。旧全局
Ramanujan 声称不自动成为单个 FP3 子层的界。

η=19/10 的原域确实渐近非空：沿产品稿同一 Bertrand 构造，取
互异素数 e≈Y¹⁹、q≈Y¹¹，S=R=eq，N=8S，T=(8S)^(1/3)≈Y¹⁰，
Kz=Mz=√T，H=L=S/√T。取 u=v=⌈H/e⌉≈Y⁶<q，及素数
n∈(S,2S)，则所有单位条件、h/δ 原壳、mollifier 内部支持成立。
连续 x=3√T/4 时 (xn+δ)/s∈[√T/2,2√T]（充分大 Y）。
只需相邻有限 dyadic 子盒，不声称任意给定 F/W 的积分必非零。

CS15 未覆盖其他 canonical 分配、原 q₀ 聚合、非内部物理箱和尾项，
也未证明一般 e-Möbius 方差。全部未估计补集和 cross 项保留。
这里的新用途是：在明确的真实线性子族中，把待付费用集中到
principal，而不是继续要求同等强度的非零谱估计。

English summary: inclusion-exclusion separates the two Mobius variables
before estimates. A primitive-conductor split combines a joint product
large sieve at high conductors with two smooth-label PV bounds at low
conductors. The centered FP3 scalar has balanced threshold E≥T^(7/4);
the original principal is retained and prevents a full-family conclusion.
