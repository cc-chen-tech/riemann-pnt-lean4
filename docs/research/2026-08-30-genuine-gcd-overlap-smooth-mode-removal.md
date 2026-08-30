# 真正 gcd 的交叠重组：可快速删去的行与剩余大交叠层

白话结论：真正 gcd 因子不能只按行数收费，也不能因为其中一个
变量变长就丢掉单位掩码。保留两者后，可以严格删去一部分 gcd
原子；困难进一步集中到两个平滑变量同时被大因子整除的交叠项。
这一步沿用已有容斥机制，新增的是它与真实共同频率平均的定量
对接，不是新的零点定理，也没有证明交叠项已成为可控主项。

**范围。** 下面的解析估计用于[上篇 (C1)–(C2)](2026-08-30-common-frequency-parseval-conductor-average.md)
的共同系数、统一光滑核、本原投影模型。先证明准确的有限重组，
再证明非零 Poisson 模式的方向性衰减。最大尺度的账本只适用于
声明的模型：额外 Type-frequency 周期因子、完整 AFE/reflection、
外标量、主字符及非零行列式总和仍不能免费吸收。没有修改 Lean。

## 1. 使用已有 gcd 机制，而不是重新命名未证估计

只读核查来源 worktree `docs-mobius-weighted-offdiagonal-20260824`，
commit `3d8f97fc8e1c7cf178b647ebd4f0b5307925eeba`，文件
`docs/research/2026-08-24-mobius-weighted-off-diagonal.md`：

- §9.138，(9.915)–(9.916)：真正 gcd 的唯一分配及剩余互素掩码；
- §9.144，(9.955)–(9.958)：固定 gcd 原子后的共同系数，以及
  真正 gcd 无逆 totient 权的重装配成本；
- §9.23，(9.111)–(9.113)：旧反向 Poisson 已保留每个单位掩码
  容斥项及其伸缩。因此本节有限容斥不是此前从未出现的机制；
- §5，(5.13)–(5.15)，及 §9.88、§9.136：物理光滑核的统一
  半范数、坐标分离与 reciprocity，外归一化仍为原来的
  \(2T/(qRS)\)。本篇不再次使用或删除该因子。

在平方自由支持上，置 \(v=dq\)、\((d,q)=1\)。原条件
\(d=(|h\delta|,v)\) 准确等价于
\[
 d\mid h\delta,\qquad(h\delta,q)=1.
\tag{O1}
\]
原唯一分配 \(d_1=(|h|,d),d_2=d/d_1\) 给
\(h=d_1h_1,\delta=d_2\delta_1,(h_1,d_2)=1\)。最后一个掩码
不能在利用长 \(h_1\) 的平滑衰减时删去：其容斥含有大除数。

对每个平方自由 \(d\)，有另一种准确但**非互斥**的表示：
\[
 \boxed{\mu(d){\bf1}_{d\mid h\delta}
 =\sum_{\substack{abe=d\\a,b,e\ \text{pairwise coprime}}}
   \mu(a)\mu(b){\bf1}_{ae\mid h}{\bf1}_{be\mid\delta}.}
\tag{O2}
\]
逐素数证明就是
\(-{\bf1}_{p\mid h\delta}=-{\bf1}_{p\mid h}
-{\bf1}_{p\mid\delta}+{\bf1}_{p\mid h,p\mid\delta}\)。
乘开即得 (O2)。即使某素数分配给 \(a\)，它仍可能整除
\(\delta\)；\(e\) 不是实际 \((h,\delta,d)\) 的互斥标签。
不能将三项都取正号，也不能对这三个项分别推断原和的下界。

置
\[
 h=aeu,\qquad\delta=bew,\qquad
 \boxed{h\delta/d=euw.}
\tag{O3}
\]
交叠变量 \(e\) 不再携带 \(\mu(e)\)，但 \(\mu(a)\mu(b)\)
和其他原始 Möbius 权仍在。特别是 \(a=b=1,e=d\) 是一个
无 \(\mu(d)\) 的容斥项，**不是已证明的正 residual main term**。

## 2. 与共同频率族兼容，且不丢任何已声明掩码

先考虑 \(q=gck\)，其中 \(g,k\) 平方自由，\(g,c,k,d\) 两两
互素，\(g>1,c>1\)。所有 \(c\) 在同一 dyadic 区间内变化，
其他标签固定。原行保留
\({\bf1}_{(h\delta,q)=1}{\bf1}_{(n,dq)=1}\)，比例变量为
\(h\delta/(dn)\)，共频族为 \(f_c(t)e_g(\nu u_ct)\)。
此处 \(u_c\in U(g)\) 是频率速度，与 (O3) 的整数 \(u\) 无关。

代入 (O2)–(O3) 后，\(e\) 是模 \(gc\) 的单位。因此
\(f_c(t)\) 变为 \(f_c(et)\)，速度变为 \(eu_c\)，行标签
\(x\) 变为 \(e^{-1}x\)。这些都是合法的单位置换；函数模长
和“与 \(\nu\) 无关”的条件保持。共同系数可以保留
\[
 a_n^{(d,k)}=a_n^0\,{f1}_{(n,dk)=1}.
\tag{O4}
\]
它允许随固定 \(d,k\) 变化，但不随变化的 \(c,\nu\) 变化。
特别是不能丢掉 \((n,d)=1\)，也不能新增 \((uw,d)=1\)。

余下 \(k\) 单位掩码分别用 \(r_h,r_\delta\mid k\) 容斥。
进一步置 \(u=r_hu',w=r_\delta w'\)，则准确乘子和长度为
\[
 t=e r_hr_\delta\,u'w'/n,\qquad
 H_*={H\over ae r_h},\quad L_*={L\over be r_\delta},\qquad
 \boxed{H_*L_*={HL\over de r_hr_\delta}\ge {HL\over de k^2}.}
\tag{O5}
\]
系数为 \(\mu(a)\mu(b)\mu(r_h)\mu(r_\delta)\)，新乘子仍为
模 \(gc\) 的单位。两个标签原子和至多付 \(\tau(k)^2\) 范数
成本；每个 \(d\) 有 \(3^{\omega(d)}\) 个 (O2) 原子，是亚幂次
而非另一个长度为 \(d\) 的和。真正 \(d\) 的数量本身仍须收费。

此重组对非分离的紧支撑光滑核也成立：将核代入原变量后，采用
\(H_*,L_*\) 归一化，保持同一半范数预算。硬端点不因此变光滑。
两侧配对时固定各自 \(a,b,e,r_h,r_\delta\)，行标签的单位置换
不改变 (C14) 的双向占据界，不能让本侧系数依赖对侧导子。

## 3. 保留两个小模式尺度，而不是只保留面积

设 \(A,B>0\)、整数 \(J\ge M+2\)、\(M\ge0\)，且
\(\mathfrak C(g)=\sum_{r\mid g}\varphi(r)/r^2\)。有
\[
 \boxed{\sum_{j,l\ne0}(g,j,l)(1+|j|/A)^{-J}(1+|l|/B)^{-J}
 \ll_J AB\mathfrak C(g)
       \min(1,A^M)\min(1,B^M).}
\tag{O6}
\]
证明完全保留模式。对任意 \(x>0\)，积分比较与级数比较给
\[
 U_J(x):=\sum_{n\ne0}(1+|n|/x)^{-J}
 \le {2J\over J-1}\,x\min(1,x^{J-1}).
\tag{O7}
\]
第一种比较给 \(2x/(J-1)\)；\(x\le1\) 时第二种比较给
\(2\zeta(J)x^J\le2Jx^J/(J-1)\)。再代入
\((g,j,l)=\sum_{r\mid g,j,l}\varphi(r)\)，模式和变为
\(\sum_{r\mid g}\varphi(r)U_J(A/r)U_J(B/r)\)。利用 \(r\ge1\)
即得 (O6)。其右侧还至多为
\(C_J AB\mathfrak C(g)\min(1,(AB)^M)\)，但这一合并界较弱。

在 (C2) 中取 \(c\in(R,2R]\)，记 \(Q_*=2gR\)。复用原来的
共同频率 Parseval、本原 Gauss 消失和 progression 大筛，只在
最后的模式和使用 (O6)，得到
\[
 \boxed{
 {1\over g}\sum_\nu\sum_c\|W_c^{(\nu)}\|_2^2
 \ll_{F,M}\mathfrak C(g)^2\log^2(2N)\,
 gR(N+gR^2)\|a\|_2^2\,
 \min\!\left(1,({Q_*\over H_*})^{2M}\right)
 \min\!\left(1,({Q_*\over L_*})^{2M}\right).}
\tag{O8}
\]
固定因子 2 已显式包含，不能在有限高度计算里当作 1。
共同频率平均的 saving 未再使用一次：这里替换 (C11)，保留
(C10) 和同一个 Poisson 前因子。两条 Poisson 轴因本原投影
精确为零，所以没有额外的 \(+1\)；主字符 \(c=1\) 不适用。

由此，若 \(H_*/Q_*\) 或 \(L_*/Q_*\) 超过 \(T^{\rho_0}\)，
\(\rho_0>0\) 固定，则行范数可以获得任意预定的负幂次。
准确量词为：对目标幂次先选足够大的固定 \(M\)，并控制该
\(M\) 所需的混合导数。仅有固定低阶正则性时不能声称任意幂次。
允许的行数、系数范数、项目分离和外权成本也须已有多项式上界。

## 4. 物理顶面长度给方向性剩余区域

采用明确顶面模型，而非由 \(HL\le T^5\) 推出错误的下界：
\[
 H\asymp T^{3-\upsilon},\quad L\asymp T^{2+\upsilon},\quad
 0\le\upsilon\le\tfrac12,\quad
 d\asymp T^\eta, e\asymp T^\xi, k\asymp T^\kappa.
\tag{O9}
\]
另记 \(a\asymp T^{\alpha_a},b\asymp T^{\alpha_b}\)，
\(\eta=\alpha_a+\alpha_b+\xi\)。若已合法适配的 Type-frequency
下降指数是 \(0\le\delta_{\rm tf}\le1/2\)，有效模数为
\[
 Q_*\asymp T^{3-\eta-\delta_{\rm tf}-\kappa}.
\tag{O10}
\]
\(\delta_{\rm tf}=0\) 时第 2 节直接提供所需掩码适配。
\(\delta_{\rm tf}>0\) 时原 §9.151 的 inactive Type 相位和其
单位条件还在：**只有它们也已合法纳入 (C1) 或付费分解后**，
才能使用下面的尺度推论。不能把一个有限域周期相位当作具有
统一实变量导数的光滑因子。

由 (O5) 两个方向分别得到
\[
 {H_*\over Q_*}\gg T^{\alpha_b+\delta_{\rm tf}-\upsilon},\qquad
 {L_*\over Q_*}\gg T^{\alpha_a+\delta_{\rm tf}+\upsilon-1}.
\tag{O11}
\]
两个 inactive \(k\) 缩放恰好各自抵消模数中的 \(\kappa\)。
若 \(x=\alpha_b+\delta_{\rm tf}-\upsilon\)，
\(y=\alpha_a+\delta_{\rm tf}+\upsilon-1\)，行范数 gain 为
\(\ll_M T^{-M(x_++y_+)}\)。对任意固定 \(\rho_0>0\)，
\(\max(x,y)>\rho_0\) 的部分可快速删去。剩余 collar 必须满足
\[
 \boxed{\alpha_b\le\upsilon-\delta_{\rm tf}+\rho_0,\qquad
        \alpha_a\le1-\upsilon-\delta_{\rm tf}+\rho_0.}
\tag{O12}
\]
特别是
\[
 \boxed{\xi\ge\eta+2\delta_{\rm tf}-1-2\rho_0.}
\tag{O13}
\]
仅用乘积长度也可证明：\(H_*L_*/Q_*^2\gg
T^{-1+\eta-\xi+2\delta_{\rm tf}}\)。但它丢掉 (O12) 的方向信息。
例如 \(a=b=1,e=d\)、\(\delta_{\rm tf}\le1/2\) 时乘积判据不
给 saving；若 \(\delta_{\rm tf}>\upsilon\) 有固定余量，第一
方向仍给 saving。不能把前一句扩大成所有方向都无衰减。

物理光滑核如何支付高阶要求：在共同四维紧环面上写
\(\Psi=\sum_{\mathbf m}\widehat\Psi(\mathbf m)e(\mathbf m\cdot z)\)。
对总次数为 \(D\) 的多项式导数权，有
\[
 \sum_{\mathbf m}|\widehat\Psi(\mathbf m)|(1+|\mathbf m|)^D
 \ll_{s,D}\|\Psi\|_{H^s},\qquad s>D+2.
\tag{O14}
\]
这是加权 Cauchy 及四维格点求和。原 (5.14) 在其光滑 core
对每个固定阶给对数成本，故可用于这一有限阶提升。若使用扩大
core 的 \(T^{O(\epsilon_0)}\) 成本，须先选导数阶，再选足够小的
\(\epsilon_0\)。原硬端点或尚未适配的其他权不由 (O14) 自动覆盖。

## 5. 支付真正 gcd 行数后：两个区域通过，一个混合区域仍留下

为检验上篇不含真正 gcd 的 \(T^{12}\) 模型能否延伸，设
\[
 N_i=T^3,\quad\|a_i\|_2^2\ll T^{3+\epsilon},\quad
 g=T^\gamma,\quad 0\le\gamma\le1,\quad
 c_i\asymp T^{\sigma_i},\quad
 \sigma_i=3-\eta_i-\delta_i-\gamma-\kappa_i\ge0.
\tag{O15}
\]
\(\sigma_i=0\) 只允许仍满足 \(c_i>1\) 的固定/亚幂次本原导子。
记 \(L,S\) 为 \(\sigma_L\ge\sigma_S\) 的两侧，不再指平滑长度。
固定所有 gcd 标签时，(C2) 的两侧能量指数为
\[
 E_i=\gamma+\sigma_i+\max(3,\gamma+2\sigma_i)+3.
\tag{O16}
\]
再支付 \(d_i\asymp T^{\eta_i}\) 的行数、\(g\asymp T^\gamma\)
的行数，以及双向占据代价，得到绝对配对指数
\[
 B=\eta_L+\eta_S+\gamma+
     \tfrac12(E_L+E_S+\sigma_L-\sigma_S).
\tag{O17}
\]
这里 \(k_i\) 仍用原直接点值的 \(1/\varphi(k_i)\) 权和
(C13)，不是再收费 \(T^{\kappa_i}\)。表中 \(\delta_i\) 是
已适配的 Type-frequency 指数，\(0\le\delta_i\le1/2\)。

| 哪个项控制大筛长度 | (O17) 的准确值 | 结论 |
|---|---|---|
| 两侧均 \(\gamma+2\sigma_i\ge3\) | \(12-\eta_L-2\delta_L-\delta_S-2\kappa_L-\kappa_S\) | \(\le12\) |
| 两侧均 \(\gamma+2\sigma_i\le3\) | \(12-\delta_L-\kappa_L-\delta_S-\kappa_S-\sigma_S\) | \(\le12\) |
| 长侧 \(\ge3\)，短侧 \(\le3\) | \(21/2-\eta_L+\eta_S+\gamma/2-2\delta_L-2\kappa_L\) | 可能 \(>12\) |

两侧阈值相等时公式相容。混合区域若 \(B>12\)，则
\[
 \eta_S>\tfrac32+\eta_L-\tfrac\gamma2+2\delta_L+2\kappa_L\ge1.
\tag{O18}
\]
结合删区引理，超过账本目标且尚未快速消失的部分必须同时满足
(O18) 和短侧的 (O12)–(O13)。这不是“所有 gcd 行都可支付”。

一个准确的模型账本见证为
\[
 \gamma=1,\quad\eta_L=0,\quad\eta_S=19/10,\quad
 \delta_i=\kappa_i=0,\quad
 \sigma_L=2,\quad\sigma_S=1/10.
\tag{O19}
\]
它给 \(B=129/10>12\)。短侧取 \(\upsilon=1/2\)、\(e=d\)，
则 \(H_*=L_*=T^{3/5}\)、\(Q_*\asymp T^{11/10}\)，两个方向
都不提供快速衰减。这个例子只证明**上述上界账本**仍有剩余；
它不是算术和下界，也没有证实完整实际行列式支持包含这个盒子。
不能利用它宣称原物理定理错误，亦不能反过来删除这个模型区域。

后续的[全共同模数联合大筛](2026-08-30-global-common-modulus-conductor-average.md)
在额外的跨 g 共同系数条件下将该账本降至 \(62/5\)，仍大于12。
本篇的逐 g 估计及其较弱共同性范围不因此改写。

## 6. 此轮得到什么，尚欠什么

得到的是一个可与共同频率大筛组合的局部删区引理，并给出真正
gcd 重装配的准确混合障碍。原唯一分配的巨大单位掩码除数没有
消失，而是显式成为 (O2) 中的交叠变量。方向性限制 (O12) 比
仅看 \(HL\) 更有信息；无掩码的“长变量快速衰减”不能取代它。

接下来仍需在原有符号、端点、相位及归一化下，控制 (O12)
以内且满足 (O18) 的交叠和，或证明实际支持/外权把它排除或
降到所需大小。把 \(e=d\) 的正容斥系数叫作主项不提供该上界。
另外，\(c=1\)、inactive Type 周期因子及完整 AFE/reflection
仍有独立对接义务。没有证明 pre-Cauchy 全长素数色散、完整
coupled-kernel、\(14/17\) 或 \(2/3\)。

## 7. 验证记录

新增 `scripts/check_genuine_gcd_overlap_smooth_modes.py` 的 20 项
检查通过，并由独立审阅者重跑 20/20。覆盖有符号交叠、非互斥
反例、原 gcd 条件、完整带权有限行重组、共频速度与标签伸缩、
所有已声明单位掩码、有限模式有理数上界和三种指数账本。
有限模式检查不替代 (O6)–(O8) 的无限和解析证明。

本轮重跑此前 13 个相关脚本的 251 项，新增 20 项，以及既有
覆盖检查 10 项，共 281 项通过。文件级独立数学审计未发现
局部声明范围内的问题，特别核对了两方向 collar、混合区域的
\(129/10\) 账本及 Type 周期因子的未证适配边界。没有修改或
运行 Lean，没有运行全仓 baseline，没有改动引用的来源 worktree。

## English summary

The squarefree genuine-gcd mask has an exact signed overlap expansion:
mu(d)1_(d|h delta) is the sum of mu(a)mu(b)1_(ae|h)1_(be|delta)
over pairwise coprime abe=d. This is inclusion-exclusion, not a disjoint
partition or a positive main term. Keeping the n-unit mask and both
inactive-k masks gives effective product length HL/(de r_h r_delta).
The full nonzero Poisson-mode sum retains separate small-scale factors,
strengthening common-frequency Parseval by min(1,(Q/H*)^(2M)) times
min(1,(Q/L*)^(2M)) in energy. On the stated smooth top-face model, the
remaining collar has alpha_b <= upsilon-delta_tf+rho0 and
alpha_a <= 1-upsilon-delta_tf+rho0. Genuine-gcd counts are affordable in
the two unmixed large-sieve regimes, but an explicit mixed-regime budget
still exceeds 12. Its large overlap layer, the principal sector, actual
Type-frequency periodic factors and complete physical assembly remain
unproved. No zero-free theorem is claimed.
