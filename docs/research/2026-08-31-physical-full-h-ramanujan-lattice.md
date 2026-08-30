# 完整 h 滤波整数格：低阶点核与共同产品列大筛

白话结论：先精确重组全部 h，再对真正的整数格作共同产品列大筛，
在 H7 的平衡尺度下可于 E≥T^(5/4) 支付指定 FP3 内部子族的中心化部分；
无需双标签 Poisson 的双无限尾。
这不降低 E 门槛，也不证明 Re ρ≤2/3。既有 PR514 保持冻结。

English summary: an exact all-h filtered lattice and one primitive large-sieve
step bound the specified balanced centered FP3 family at E≥T^(5/4), with a six-derivative
point-weight budget. No stronger zero-free result or global-tail claim is made.
上游定义固定 49cfacd70c60372757280177c7b63fd4f7760817 的
(2.5)、(4.4)–(4.5)，物理索引固定 7cf2e7d4 的 FP1–FP4。
本文对象是固定 AFE、δ 光滑包内的完整 h 滤波子族，不是 DP 的一个 H 包。
以下给出完整有限重组、统一点核预算与解析估计；有限测试只辅助核对，
不替代解析证明。本文不调用 DP 的单 H 包结论。

## H1. 精确对象与换序

固定平方自由 q₀；原 FP3 取 r=n、s=e q、h=e u、δ=e v，
e∈[E,2E)、q∈[Q,2Q)、Q=S/E，且
\[
 \mu^2(eq)=1,\quad (q,q_0)=(n,q_0eq)=(e,q_0q)=(v,q)=1 .
\]
原 μ(n)μ(e)μ(q)、mollifier taper、R/S/AFE cutoff 全部保留。
δ 包从 FP1 插入原 F(|δ|/L)，不继承旧硬 H/L 壳。
只选整个支持满足 q₀n,q₀eq≤N/2 的内部包，不能另外插入联合硬角点。

令
\[
 A_{n,e,q,v}(x)=
 \frac{F_M(x)F_K(y)}{\sqrt{xy}}
 \int W(t/T)V_t(xy)(y e q/(nx))^{it}\,dt,\qquad
 y=\frac{nx+ev}{eq}.
\]
它在 x>0,y>0 外置零。固定上述有限标签及 AFE 尺度后，
A∈C_c^\infty(R)。δ cutoff 可在外保留。采用
\(\widehat A(\xi)=\int A(x)e(-x\xi)\,dx\)。
去掉 H cutoff 后，h=e u 的原核恰为 \(\widehat A(u/q)\)。
固定层 Fourier 快衰减保证 u 和绝对收敛；完整非负重叠 H partition
可在该层重组。不据此声称跨全部 AFE 尺度的统一尾已被支付。

## H2. 全 h 中心化 Poisson

对 q>1，
\[
 \sum_{(u,q)=1}
 \left[e_q(-euv\bar n)-\frac{\mu(q)}{\varphi(q)}\right]
 \widehat A(u/q)
 =\sum_{m\in\mathbb Z}C_q(n,e,v;m)A(m),
\]
\[
 C_q(n,e,v;m)=c_q(nm+ev)-\frac{\mu(q)}{\varphi(q)}c_q(m).
\]
证明：按 u=a+qj 分组，普通 Poisson 给
\(\sum_j\widehat A(j+a/q)=\sum_m A(m)e_q(-am)\)；
再对单位 a 求和，利用 n 为单位及 Ramanujan 和为实数。
没有遗漏的 q 因子。q>1 时 u=0 自动不在单位集合；q=1 的原
centered 密度逐项为零，单独处理。

m 是正整数；y=(nm+ev)/(eq) 只是没有整性约束的实参数
（固定整数标签后为有理数），不能补上 e 整除或 y 为整数的条件。
完整 h 是受限 h 层的 Ramanujan 滤波，不等于恢复完整原 AFE 整数格。

素数 p 时
\[
 C_p=p1_{(m,p)=1}
       \left[1_{nm+ev\equiv0\;(p)}-\frac1{p-1}\right].
\]
合数不得用此式删除所有非单位 m。所有 m 剩余类的和，以及
固定 m 对单位 n 或单位 v 的和都严格为零；这不证明 Möbius 加权消去。

## H3. 唯一外权与真正的点核半范数

定义实际归一化点权
\[
 \Omega(e/E,n/R,m/M,v/V,q/Q)=
 \frac{RSM}{T\sqrt{neq}\,eq}\,
 p_N(q_0n)p_N(q_0eq)F_R(n)F_S(eq)F(|ev|/L)A_{n,e,q,v}(m),
 \qquad V=L/E.
\]
因此本族精确等于
\[
 \mathscr C^{\rm all\,h}_E=
 \frac{2T}{q_0RSM}
 \sum_{e,q,n,m,v}\mu(e)\mu(q)\mu(n)\Omega\,C_q(n,e,v;m).
\]
上式保留 H1 全部单位条件。逐点 |A(m)|≲T/√(MK)，所以
Ω 的尺度因子为 √(MR/(KS))，在 core 内有界；1/M 不可删除。

本稿使用新五变量点核预算
\[
 \mathcal B_J=\max_{|\alpha|\le J}\|\partial^\alpha\Omega\|_\infty
\]
（在固定紧集上加固定光滑外 cutoff）。它不是旧 DP 的 A_sm30。
内部假设包括 KS≈MR、TL/(MR)≲1、KM≲T，所有比例均用固定常数；
由上游 (2.5) 的 V_t 导数界和链式法则，B_J 对固定 J 一致有界。
缩放后的 log 相位为
\(T\log(1+(L/(MR))\,x_e x_v/(x_n x_m))\)，
故不能在 TL/(MR) 很大时继续免费使用同一预算。
F_K 使 y/K 远离零，F_M 使 m/M 远离零，延零没有新硬边缘。

e、q 的离散 dyadic 限制及各标签固定投影区间可保留在独立因子中。
E≥1，m∈[M/2,2M]，|v|∈[V/4,2V]；M<1/2 或 V<1/2
时相应整数和为空。非空时长度计数 O(M)、O(V) 不需虚构 +1。

## H4. 粗绝对计数的准确边界

若 R≥Q，则
\[
 \sum_{n,m,v}|C_q(n,e,v;m)|\ll_\epsilon RMV\,T^\epsilon.
\]
对首项用 |c_q(z)|≤Σ_{d|q,d|z}d。由于 ev 为 d-unit，
d|nm+ev 强制 m 为 d-unit，n 在唯一模 d 剩余类；
q<2Q≤2R 给 O(R/d) 个 n。中心项用 |c_q(m)|≤φ(q)。
聚合后得到 \(O(\mathcal B_0 T^{1+\epsilon}L/(q_0E))\)。
平衡指数为 7/2−η；这只是一种粗上界。
不能把它与 DP 单 H 包当成同对象的严格优劣比较。

## H5. 非单位 m 与完整有效导子

令 g=(m,q)、l=q/g，则平方自由性给
\[
 C_q=\mu(g)\left[c_l(nm+ev)-\frac1{\varphi(l)}\right].
\]
l=1 时为零。l>1 时 (nmev,l)=1，令 w=nm/(ev) mod l。
有限群上的精确展开是
\[
 c_l(w+1)-\frac1{\varphi(l)}
 =\frac1{\varphi(l)}
   \sum_{\substack{\psi\bmod l\\\psi\ne\psi_0}}
      \operatorname{cond}(\psi)\psi(-w).
\]
证明：逐素数 p 的非主 Fourier 系数为 p·barψ(−1)，
主系数为1；CRT 乘积后，非主系数为 cond(ψ)·barψ(−1)，
减去单位常数恰好删除唯一 principal。

对每个非主字符写 l=cℓ、χ primitive mod ℓ>1。
此处需对全部 cℓ=l 求和，不是把一个字符块称作整个 C_q。
于是 q=g cℓ、m=gz，原外 μ(q) 与 μ(g) 融合为 μ(c)μ(ℓ)。
例如 q=6,m=4,n=e=v=1 时 C_q=3/2，不能添加 (z,g)=1。
另一核对式为
\[
 \mu(q)C_q=\sum_{d\mid(q,nm+ev)}\mu(d)d-c_q(m)/\varphi(q).
\]

## H6. 完整 e/n 容斥与共同列

平方前完整容斥 (n,e)=1，令 e=fa、n=fb：
符号精确为 μ(f)μ(a)μ(b)，保留 (ab,f)=1；不要求 (a,b)=1。
固定 f,g,c 后 g,c 平方自由，且 (g,c)=(gc,q₀)=(f,q₀gc)=1；
可用字符模数只取平方自由 ℓ、(ℓ,fgcq₀)=1。
全部独立系数掩码为
\[
 (ab,fq_0gc)=1,\qquad (z,c)=1,\qquad (v,gc)=1.
\]
a,b,z,v 的 ℓ-unit 条件由 primitive χ 的零延拓保持。
没有 (z,g)、(z,f)、(v,f) 或 (a,b) 条件。

固定归一化长度
\[
 A=E/f,\ B=R/f,\ Z=M/g,\ V=L/E,\ \Lambda=Q/(gc).
\]
五变量 \(\Omega(fa/E,fb/R,gz/M,v/V,gc\ell/Q)\)
恰为 \(\Omega(a/A,b/B,z/Z,v/V,\ell/\Lambda)\)，预算相同。
固定紧集 Fourier 展开并作 Sobolev–Cauchy，H³ 已足够五维绝对可和；
取 B_6 为安全统一预算，无额外 BV 权或双无限 Poisson 尾。
真实标量 Fourier 系数及模数因子 μ(ℓ)χ(−g) 均保留。
每个 atom 的字符积为 \(B_\chi Z_\chi A_{\bar\chi}V_{\bar\chi}\)。
这里 \(A_{\bar\chi}=\sum_a\alpha_a\bar\chi(a)\)，Fourier 系数
α_a 保持原值；它一般不是 \(\overline{A_\chi}\)。V 同理。
大筛时 χ↦barχ 是 primitive 集合的置换，不共轭原线性和的系数。
用 BZ 与 AV 两个整数乘积列，不通过相位修改线性和。
正负 v 分成两个有符号 atom，只产生固定倍数。

## H7. 一次大筛与三个外层之和

乘积表示数的除数界给两列平方范数
\(\ll T^\epsilon BZ\)、\(\ll T^\epsilon AV\)。
行因子为 \(\ell/(\varphi(c)\varphi(\ell))\)，恰与
[Kedlaya Theorem 16.2](https://kskedlaya.org/ant/chap-largesieve2.html)
的 primitive 大筛权匹配。一次 Cauchy 后得到
\[
 \frac{\mathcal B_6T^\epsilon}{\varphi(c)}
 \sqrt{\frac{RML}{f^2g}
       \left(\frac{RM}{fg}+\Lambda^2\right)
       \left(\frac Lf+\Lambda^2\right)}.
\]
不限制单个 f 为小量。非空支持给 f≤2min(E,R)、g≤2M、gc≤2Q；
先保留固定 f,g,c 的公共列，再取外层绝对值。
四项展开分别为
\[
 \frac{RML}{f^2g\varphi(c)},\
 \frac{RM\sqrt L Q}{f^{3/2}g^2c\varphi(c)},\
 \frac{L\sqrt{RM}Q}{f^{3/2}g^{3/2}c\varphi(c)},\
 \frac{\sqrt{RML}Q^2}{fg^{5/2}c^2\varphi(c)}.
\]
使用 1/φ(c)≤τ(c)/c，所有 f,g,c 的和只产生对数损失。
所有尺度为 T 的固定幂范围时，完整局部界为
\[
 |\mathscr C^{\rm all\,h}_E|
 \ll_\epsilon\frac{\mathcal B_6T^{1+\epsilon}}{q_0RSM}
 [RML+RM\sqrt L Q+L\sqrt{RM}Q+\sqrt{RML}Q^2].
\]
平衡 R=S=T³、M=K=T^(1/2)、L=T^(5/2)、E=T^η 时四项物理指数：
\[
 \frac12,\quad\frac94-\eta,\quad\frac74-\eta,\quad\frac72-2\eta.
\]
故在 η≥5/4 达到 T^(1+ε) 预算，但没有更低 E 的新覆盖。
与 DP 不同，它估计完整 h 滤波子族、固定 L/AFE 包；不能以此
悄悄替换 DP 单 H 包定理，不能支付 global principal 或跨 AFE 尾。

## H8. 证明及发布边界

此结果与 DP 保留相同的 5/4 指数门槛，但对象是完整 h 滤波族，
不是单个 H 包的更强界。省去双 Poisson 尾，使用 B₆ 点核预算，
不意味着可把 DP 的 A_sm30 在原命题中直接替换为 B₆。

固定 q₀、R/S/AFE/L 内部包；其他 canonical gcd 分配、包补集、
global principal 和跨 AFE 的统一尾仍需分别支付。q₀壳尚未求和，
也未使用平方自由 e 的新有符号分布定理。全局 14/17、2/3 结论未完成。

配套有限检查：
`scripts/check_physical_full_h_ramanujan_lattice.py`。
它检查原系数、完整非单位/导子下降、全部 f/g/c 复权重组、
关键错误掩码的负例、归一化及四项有理费用。
Schwartz 数值例只检查符号和 Poisson 常数，不作为物理换序证书。
