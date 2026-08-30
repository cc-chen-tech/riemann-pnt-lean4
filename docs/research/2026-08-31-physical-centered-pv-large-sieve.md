# 中心化 FP3：PV 后保留两条共同 Möbius 列

白话结论：两个光滑标签用 PV 后，不必把其余两个角色和逐项取
绝对值。它们仍是对有效导子共同的两条系数列，可以一起用乘法大筛。
改进低导子端，再接已有高导子端，使同一真实中心化 FP3 子族的
平衡门槛从 E≥T^(7/4) 降到 E≥T^(4/3)。
这里没有证明新的 Möbius 符号专属估计；principal 仍未支付，
所以不声称完整 FP3、14/17 或 2/3 的证明。

只继承冻结 0d468dd0c1b074bc7e879d0318c90c3d5da11f79 的
[CS1–CS17](2026-08-31-physical-centered-conductor-split.md)。
不修改该父稿，不把旧二次 resonant projector 当成这里的线性和。

## PL1. 精确对象、共同列和原权均不改变

原对象仍是 CS1 的 C，原外权为 2T/(q₀RS)，并保留 O=C+P。
固定平方自由 q₀，s=eq、r=n、h=eu、δ=ev，e≈E、q≈Q，
EQ≈S，(e,q₀q)=(n,q₀eq)=(uv,q)=1，e、q 平方自由。
只处理原内部光滑箱 HL≲RS/T、q₀n,q₀eq≤N/2，
所有尺度限于固定 T 幂，J≥6，半范数为原 A_J。

先完整展开 (e,n)=1，e=fa、n=fb。CS2 的系数为
μ(f)μ(a)μ(b)1_(ab,f)=1；不能重新添加 (a,b)=1。
令 A=E/f、B=R/f、U=H/E、V=L/E，f≤2min(E,R)。
在固定 f,c 的 CS7 中，q=cℓ，ℓ>1 是真正 primitive conductor，
而非加性 Type gcd。平方自由 c、ℓ 互素，并保留
(c,fq₀)=(ℓ,fq₀c)=1。两条列准确为
\[
 A_\chi=\sum_{(a,fq_0c)=1}\mu(a)\alpha_a\chi^*(a),\qquad
 B_{\bar\chi}=\sum_{(b,fq_0c)=1}\mu(b)x_b\bar\chi^*(b).       \tag{PL1}
\]
系数模长≤1，支撑长度 O(A)、O(B)，非空时 A,B≥1/2。
它们对变化的 ℓ 共同，但不要求跨 f,c 共同。
ℓ-unit 由角色的零延拓提供，不另塞进系数使它随 ℓ 改变。

原联合权仍按 b/B、a/A、q/Q、u/U、v/V 五变量分离：
原 Ψ 的四个坐标是 b/B、(EQ/S)(a/A)(q/Q)、
(a/A)(v/V)、(a/A)(u/U)。内部 taper 也在此原权内。
原 smooth 非矩形支持不替换为硬联合截断。两个标签的 BV 费用
仍由 CS4 的
\[
 \sum_\nu |c_\nu|(1+|\nu_u|)(1+|\nu_v|)\ll\mathcal A_J
                                                               \tag{PL2}
\]
支付；五维 Sobolev–Cauchy 需要 s>9/2，J≥6 足够。
没有新维度或新的导数损失。正负标签分开，u,v=0 排除。

## PL2. PV 之后再对两列作一次共同大筛

固定一个原子及 f,c、L<ℓ≤2L，ℓ>1。CS12 的标签容斥保留
(uv,c)=1，经典 PV 与 Abel 求和给
\[
 |U_\chi V_\chi|
 \ll \tau(c)^2\ell\log^2(2\ell)\,
             (1+|\nu_u|)(1+|\nu_v|).                      \tag{PL3}
\]
不对 μ(a)、μ(b) 使用 PV。原 Gauss 系数的模长为
√ℓ/(φ(c)φ(ℓ))，所以乘 PL3 后，剩余精确归一化为
\[
 {\sqrt\ell\over\varphi(c)}
             {\ell\over\varphi(\ell)}.
\]
β_(cℓ)、μ(ℓ)、barχ*(c) 和 χ*(-1) 都仍在原 CS7；
这里只用它们模长≤1，未将 barχ*(c) 从原恒等式删去。

关键是在 (ℓ,primitive χ*) 上保留共同列并用带权 Cauchy：
\[
 \sum_{\ell\asymp L}{\ell\over\varphi(\ell)}
              \sum_{\chi^*}|A_\chi B_{\bar\chi}|
 \le
 \left(\sum_{\ell\asymp L}{\ell\over\varphi(\ell)}
              \sum_{\chi^*}|A_\chi|^2\right)^{1/2}
 \left(\sum_{\ell\asymp L}{\ell\over\varphi(\ell)}
              \sum_{\chi^*}|B_{\bar\chi}|^2\right)^{1/2}.
                                                               \tag{PL4}
\]
允许模数子集可以向所有 primitive 角色扩大，因为此时各项非负。
共轭 primitive 角色仍 primitive。按
[Kedlaya Theorem 16.2](https://kskedlaya.org/ant/chap-largesieve2.html)，
两因子平方分别≪A(A+L²)、B(B+L²)。因而固定 f,c 的本层费用为
\[
 \ll {\tau(c)^2\log^2(2L)\sqrt L\over\varphi(c)}
       \sqrt{AB(A+L^2)(B+L^2)}
       (1+|\nu_u|)(1+|\nu_v|).                            \tag{PL5}
\]
这是 PV 与大筛先后用于不同因子，不是重复使用同一抵消。
PV 的经典输入参见
[Granville–Soundararajan 的式 (1.1)](https://arxiv.org/html/math/0503113v1)。
没有使用 Cochrane–Shi 或假设任意三标签权满足其四次矩。

## PL3. 全部 imprimitive cofactor、全部容斥层

q 在一个固定 dyadic 壳时，本层 c 在 O(1) 个 Q/L 大小的壳内。
对 c 取绝对值后分别付费，不在不同 c 间假装系数共同。
例如 c∈[C,2C)、C≥1/2，令 D=max_(c≤2C)τ(c)，则
\[
 \sum_{C\le c<2C}{\tau(c)^2\over\varphi(c)}
 \le D^3\sum_{C\le c<2C}{1\over c}\le2D^3.                \tag{PL6}
\]
用 c/φ(c)≤τ(c)，空壳为0。所有允许模数的互素限制仍在原和；
上界扩大到整壳只增加非负项。故 PL6 在固定幂尺度为 T^ε，
没有额外 Q/L 成本；有限高度则保留这个 divisor 预算。

由 PL5–PL6，固定 f 的低端费用≪
\[
 \sqrt L\{AB+L(A\sqrt B+B\sqrt A)+L^2\sqrt{AB}\}T^\epsilon.
\]
这里使用完整展开
\[
 LAB(A+L^2)(B+L^2)
 =L(AB)^2+L^3(A^2B+AB^2)+L^5AB,                         \tag{PL7}
\]
从未假设 L²≤A,B。大 f 和 a=1、b=1 均在内。
对 1<ℓ≤Z 的 dyadic L 求和，再对全部 f 求和，得到
\[
 \boxed{\mathcal L(Z)\ll T^\epsilon
 \{ER\sqrt Z+(R\sqrt E+E\sqrt R)Z^{3/2}
                  +\sqrt{ER}Z^{5/2}\}.}                 \tag{PL8}
\]
f 幂分别为 −2、−3/2、−1；最后的 log(2min(E,R)) 吸收在 T^ε，
其余部分和收敛。ℓ=1 不适用 PV，始终留在 P；
平方自由 q=2 没有非主 primitive 部分，不能虚构导子2。

## PL4. 与原高导子端拼接，新的平衡区域

保留 CS11 的整个高端，1≤Z≤Q，恢复原唯一外权与 PL2：
\[
 |\mathcal C|\ll{\mathcal A_JT^{1+\epsilon}\over q_0RS}
 \left\{
 {RHL\over E\sqrt Z}
 +\sqrt Q\left(R\sqrt{HL/E}+{HL\over E}\sqrt R\right)
 +Q^{3/2}\sqrt{RHL/E}
 +ER\sqrt Z+(R\sqrt E+E\sqrt R)Z^{3/2}
 +\sqrt{ER}Z^{5/2}\right\}.                              \tag{PL9}
\]
上下两段是互不重叠的 conductor 分割，不相乘两个 saving。
若只要全 PV–大筛版，取 Z 覆盖最高 q（例如 Z=2Q），直接使用
PL8 而不再加高端。字面取 Z=Q 不保证 q≤2Q 的高端为空。

现在固定 q₀=1，R=S≈T³、H=L≈T^(5/2)，E≈T^η，
Q≈T^(3−η)，4/3≤η≤2。取
\[
 z=\log_T Z={5\over2}-{3\eta\over4},\qquad 0\le z\le3-\eta.
\]
常数端点按原壳截断处理。PL9 八项的物理指数依次为
\[
 {7\over4}-{5\eta\over8},\
 2-\eta,\
 3-{3\eta\over2},\
 {7\over2}-2\eta,\
 {5\eta\over8}-{3\over4},\
 {7\over4}-{5\eta\over8},\
 {1\over4}-{\eta\over8},\
 {11\over4}-{11\eta\over8}.                              \tag{PL10}
\]
故最大值准确为
\[
 F(\eta)=\max\left(3-{3\eta\over2},
                         {7\over4}-{5\eta\over8}\right)\le1.
                                                               \tag{PL11}
\]
两项在 η=10/7 相交；η=4/3、7/5、3/2、2 时，
F 分别为 1、9/10、13/16、1/2。
η>2 的已有界直接可用，故这里只登记新的 [4/3,2] 区域。
在这些估计下 η<4/3 时原高端项 3−3η/2 仍超预算；
这只是本估计不足，不是原式反例或无法改善的障碍。

η=7/5 的真实域渐近非空：取互异素数 e≈Y¹⁴、q≈Y¹⁶，
R=S=eq、N=8S、T=(8S)^(1/3)≈Y¹⁰，H=L=S/√T。
u=v=ceil(H/e)≈Y¹¹<q，n 取 (S,2S) 中的素数，则
所有原 gcd、mollifier 与 h/δ 壳成立。连续 x=3√T/4 时，
(xn+δ)/(S√T)∈[1/2,2] 对充分大 Y 成立。
这是原允许域的非空性，不声称任意给定权的积分非零。

## PL5. 交付边界

principal 仍按 CS17 给 T^(3−η+ε)，η=7/5 时为 T^(8/5+ε)，
远未付 T 预算。全局 principal/AFE 重组即使成立，也不自动
成为这个局部 P 的同样上界。这里不迁移或使用该尚在审核的结果。
其他 canonical allocations、q₀ 外壳、非内部箱、尾和所有补集保留。
有限脚本只检查恒等式、共同列、有限大筛数值算例及指数账本，
不替代 PV、大筛或无穷光滑分离的解析证明。没有 Lean 新增。

English summary: after two smooth-label PV bounds, apply the primitive
multiplicative large sieve jointly to the remaining two common columns.
The improved low-conductor estimate combines with the frozen high end
to give the centered FP3 threshold E≥T^(4/3). The principal is retained;
there is no full-family or zero-free conclusion.
