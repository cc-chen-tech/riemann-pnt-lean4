# 共同零频没有删除共同相位：恢复 Type 字符导子与最小范数 lift

白话结论：继续沿 \(h\delta\) 平均追查时，发现从共同 Fourier 零频
到单层素模 incidence 的转换漏掉了一个算术相位。它不是平滑权，
不能免费分离。本节补回全部共同频率的相位，给出其零频分离成本的
精确值，并用一个最小范数 lift 修复短侧能量比较。旧的 short-Type-I
companion 删格没有因此获得证明，必须恢复到未删的物理和中。

**状态。** 有限恒等式、Gauss 核的精确分离范数、最小范数 lift 以及 §6 的
共同零频低导子子空间覆盖已证明。
完整物理 coupled-kernel gate 和 \(\theta=3\) twisted moment 仍开放。
本节优先于主笔记 §§9.173、9.177–9.178、9.183、9.193 中与之冲突的
物理识别和覆盖断言。§§9.168–9.172 的完整 \(U,V\) 定义和有限 Fourier
恒等式不受影响；§9.184 最近修正的归一化大筛定理也不受影响。

## 1. 从原共同 Fourier 行逐项消元

设 \(g>1\) 平方自由、\(p\) 为与 \(g\) 互素的素数，\(C\in U(g)\)。
先固定一个原平滑分离 atom，但**不要分离以下算术相位**。记
\(m=h\delta\)，\(b(n)\) 已含原 \(\mu(n)\) 或一个精确 Type 系数；
全部原有限支持和单位条件 \((mn,gp)=1\) 保留。公共外标量
\(\mu(gp)\) 可放回两边，下面省略它。未乘相位的 CRT ratio 行为

\[
 Z(s,x)=\sum_{h,\delta,n} f(h)\ell(\delta)b(n)
  {\bf1}_{m+sn\equiv0\ (g)}
  {\bf1}_{m+xn\equiv0\ (p)}.
\tag{CG1}
\]

主笔记 (9.1113) 的行相位为 \(e_g(C\overline{ps})\)。
在 \(s=pz\) 坐标上，**完整**共同 Fourier 行是

\[
 V_p^{(\nu)}(x)=
 \sum_{z\in U(g)}
 e_g(C\overline{p^2z}-\nu z)\,Z(pz,x).
\tag{CG2}
\]

这里 \(\nu\) 是共同 \(g\)-坐标的 Fourier 频率，不是原 AFE 的
\(h\)，也不是 canonical reflection 零核的名称。右行的相位若使用
相反号，应将其实际有符号的 \(C\) 代入，不能另删共轭。

对每个原 \((h,\delta,n)\)，第一个 incidence 恰有一个
\(z=-m\overline{pn}\)。故不取绝对值、不使用 Cauchy，即得

\[
 \boxed{
 V_p^{(\nu)}(x)=
 \sum_{h,\delta,n}f(h)\ell(\delta)b(n)
 e_g(-C\bar p\,n\bar m+\nu\bar p\,m\bar n)
 {\bf1}_{m+xn\equiv0\ (p)}.}
\tag{CG3}
\]

求和有限且是一一消元，没有 floor、尾项或端点误差。对每个单位
\((m,n)\) 又恰有一个 \(x=-m\bar n\pmod p\)。因此 active 中心化
\(V^\circ=V-\varphi(p)^{-1}\sum_xV(x)\)，在 \(x=D\bar q\) 上恰为

\[
 \boxed{
 V_p^{(\nu),\circ}(D\bar q)=
 \sum_{h,\delta,n}f(h)\ell(\delta)b(n)
 e_g(A\,n\bar m+B\,m\bar n)
 \left({\bf1}_{p\mid qm+Dn}-\frac1{p-1}\right),\quad
 A=-C\bar p,\ B=\nu\bar p.}
\tag{CG4}
\]

所有原 \(h,\delta\) 及其乘积均在同一个和内。固定-order active
字符投影可在 (CG4) 后再线性扣除，不能通过忽略 \(g\)-相位实现。

**遗漏位置。** (9.1139) 的 \(V^{(0)}\) 明确包含 (CG2) 的相位，
而 (9.1156)–(9.1160) 未显示 (CG3) 的共同 multiplier。它们仍是
单层分离模型的正确恒等式，但不能直接当作该 \(V^{(0)}\) 的物理展开。
若把 multiplier 吸进一般 \(w_p(m,n)\)，则必须保留 \(m,n\) 的耦合；
不能随后又声称 \(w_p=f_p(m)g_p(n)\)。

最小见证取 \(g=5,p=7,C=3,\nu=0,m=n=1\)，系数为 1：
\(z=2,\ x=6\)，相位为 \(e_5(1)\)，故
\[
 V^\circ(6)=\tfrac56e_5(1),\qquad
 V^\circ(x)=-\tfrac16e_5(1)\quad(x\ne6).
\tag{CG5}
\]
无相位模型得到的是 \(5/6\) 和 \(-1/6\)，不是同一个行。
这是物理识别的有限反例，不是原 Selberg 估计的反例。

## 2. 零频核的分离成本恰为平方根量级

取素数 \(g\) 和 \(A\in U(g)\)，设
\[
 K_A(a,b)=e_g(A b\bar a),\qquad a,b\in U(g).
\]
直接对 \(b\) 求和得
\[
 K_AK_A^*=gI-J.
\tag{CG6}
\]
其奇异值为 \(1\)（一次）及 \(\sqrt g\)（\(g-2\) 次）。

准确说明“不能免费分离”：定义
\[
 \|K\|_{\pi,\infty}
 =\inf\left\{\sum_j|c_j|:
 K(a,b)=\sum_jc_j u_j(a)v_j(b),\
 \|u_j\|_\infty,\|v_j\|_\infty\le1\right\}.
\]
核范数三角不等式及
\(\|u_jv_j^{\mathsf T}\|_*\le g-1\) 给出下界。
另一方面乘性 Fourier 展开为
\[
 K_A(a,b)=\sum_{\eta\bmod g}c_\eta(A,0)
             \overline{\eta(a)}\eta(b),\quad
 c_\eta(A,B)=\frac1{\varphi(g)}
    \sum_{t\in U(g)}e_g(At+B\bar t)\overline{\eta(t)}.
\tag{CG7}
\]
当 \(B=0\) 时，主字符系数模长为 \(1/(g-1)\)，其他系数模长为
\(\sqrt g/(g-1)\)，恰好达到核范数下界。因此
\[
 \boxed{\|K_A\|_{\pi,\infty}
       =\frac{1+(g-2)\sqrt g}{g-1}\asymp\sqrt g.}
\tag{CG8}
\]

这比“矩阵满秩”更强：它限制的是规范化后的分离成本，而不只是项数。
它仅排除先分离此核再取 atom 绝对值的免费步骤；**不意味着真实
双行和必损失 \(\sqrt g\)**。真实和仍可利用共同字符、\(h\delta\)、
两侧 Möbius 和全部共同频率的联合抵消。

对平方自由合数 \(g\)，CRT 给出局部矩阵的张量积；同一论证给出
\[
 \|K_A\|_{\pi,\infty}
 =\prod_{\ell\mid g}
   \frac{1+(\ell-2)\sqrt\ell}{\ell-1}.
\tag{CG9}
\]
其中 \(\ell=2\) 因子为 1，未忽略偶模边界。

## 3. 真正的字符导子以及完整 Type 分解

对任意 \(\nu\)，(CG7) 是
精确展开，并且 Parseval 给出
\[
 \sum_{\eta\bmod g}|c_\eta(A,B)|^2=1.
\tag{CG10}
\]
当 \(B\ne0\) 时它是 mixed Kloosterman 字符系数，不能把
\(B=0\) 的每项 Gauss 模长原样套上。零频时
\(c_\eta(A,0)=\eta(A)c_\eta(1,0)\)，特别保留
\(\eta(-C)\overline{\eta(p)}\) 的 active-level 依赖。

用主笔记 (9.1284) 展开 active incidence 后，\(m\) 上的字符是
\[
 \Xi=\chi_p\overline{\eta},\qquad
 \Xi(m)=\Xi(h)\Xi(\delta),
\tag{CG11}
\]
而 \(n\) 上是 \(\overline\Xi(n)\)。若
\(\chi_p\ne\chi_{p,0}\)、\(\operatorname{cond}(\eta)=f\mid g\)，则
\[
 \boxed{\operatorname{cond}(\Xi)=pf.}
\tag{CG12}
\]
原单位掩码 \((h\delta n,gp)=1\) 没有消失；以原始导子 \(pf\)
书写时，仍须保留 \(g/f\) 的单位掩码。

这些标准导子与 Gauss 事实可对照
[Montgomery–Vaughan, Chapter 9, Lemma 3 and Gauss-sum theorems](https://personal.science.psu.edu/rcv4/568s20/568chapter9.pdf)。
本节的核范数结论由 (CG6)–(CG8) 直接证明，不是从该来源引入的新谱估计。

对一个完整平滑 atom 定义
\[
 F_{\Xi}=\sum_{h,\delta}f(h)\ell(\delta)\Xi(h)\Xi(\delta),
 \qquad G_{\Xi}^\alpha=\sum_n\lambda_\alpha(n)
                 \widetilde b(n)\overline{\Xi(n)}.
\]
则 (CG4) 的完整字符式包含
\[
 \frac1{\varphi(p)}\sum_{\chi_p\ne\chi_{p,0}}
 \chi_p(-q\bar D)
 \sum_{\eta\bmod g}c_\eta(A,B)F_{\chi_p\bar\eta}
                                      G_{\chi_p\bar\eta}^{\alpha}.
\tag{CG13}
\]
不是仅有 \(\eta=1\) 的 \(F_{\chi_p}G_{\chi_p}\)。

在 \(n>\max(U,V)\) 上可原样使用精确分解
\[
 \lambda_{\rm I}(n)=-\sum_{bcr=n;\ b\le U,c\le V}\mu(b)\mu(c),
 \qquad
 \lambda_{\rm II}(n)=\sum_{bcr=n;\ b>U,c>V}\mu(b)\mu(c).
\tag{CG14}
\]
每块的字符为 \(\overline{\Xi(bc)}\overline{\Xi(r)}\)，不是
\(\bar\chi_p(bcr)\)。小项 \(\mu(n){\bf1}_{n\le\max(U,V)}\) 不得删除。
两侧同时代入，得到带 \(\eta_1,\eta_2\) 的九个有序 Type 块；
\(h_i,\delta_i\)、\(c_{\eta_i}(A_i,B_i)\) 及外侧互素/符号数据保持在
同一个 signed 和内。原伴随素因子若已从 \(n\) 拆出，也必须保留。

**覆盖修正。** §9.177 的 PV 行 (9.1198) 对固定原始字符仍有效，
但一般应使用 \((pf)^{1/2}\)，并处理剩余单位掩码。只把 active
指数 \(\sigma\) 填入旧式是不够的。对旧极端短侧
\(\sigma_S=3/2,\ \log_T f=1,\ U=V=T^{1/2}\)，伴随长度
\(T^{1/2}\) 时，固定字符的平滑组 PV 指数由 \(7/4\) 变成
\(9/4\)。对共同字符再作分离还需付 (CG8) 的范数，除非另有联合估计。

因此旧的 \(\varpi\le1/2\) companion physical coverage、由此删格的
PCDI-SREM 及已扣除的 \(\eta_{\rm I,S}\) 均暂停使用。未另证前，
物理和恢复这些格子，并以完整 \(\eta_{\rm imb}\) 为目标。
审计器只在明确提供“共同相位确已消除且原 conductor/单位掩码仍适用”
这一额外证书时，才允许输出旧无相位模型的覆盖；默认保留格子。
已有非物理测试向量不能提供此证书。

## 4. 短侧范数的精确修复：取 graph-span 最小 lift

另一个必须与 (CG3) 一起修复的步骤是 §9.183 的能量比较。
单纯的 \(b=F\otimes G\) 不是 ratio-profile 能量的子能量：
模 5 取 \(F=(1,-1,0,0)\)、\(G=(1,1,1,1)\)，则每条 ratio
卷积都为零，而 \(\|F\otimes G\|_2^2=8\)。

这个问题不需要新的分析假设。设 \(q\) 为短素数，
\(R:U(q)\to\mathbb C\) 是**实际**中心化短行，含 (CG3) 的相位；
\(\sum_xR(x)=0\)，\(n_q=\varphi(q)\)。定义
\[
 b_{\min}(u,v)=\frac1{n_q}R(-u\bar v),\qquad
 K_c(u,v)={\bf1}_{v=cu}-\frac1{n_q}.
\tag{CG15}
\]
采用 \(\langle b,K\rangle=\sum\bar bK\) 约定，直接计数得到
\[
 \boxed{\langle b_{\min},K_c\rangle
       =\overline{R(-\bar c)},\qquad
       \|b_{\min}\|_2^2=\frac{\|R\|_2^2}{n_q}.}
\tag{CG16}
\]
\(b_{\min}\) 在 \(\operatorname{span}\{K_c\}\) 中；任意具有同样
所有 pairings 的 lift 与它之差正交于这个 span，故其范数不小于
(CG16)。这证明了“最小”，不是选择一个便利的上界。

令 \(C(p)\) 为**含共同 multiplier 的**实际长行系数。完整固定
packet 的交叉和恰有
\[
 \begin{aligned}
 S&=\sum_p C(p)\overline{R(-D\bar p)}
   =\left\langle b_{\min},\sum_pC(p)K_{p\bar D}\right\rangle,\\
 |S|^2&\le
 \frac{\|R\|_2^2}{\varphi(q)}
 \left\{\varphi(q)\sum_c
  \left|\sum_{p\bar D=c}C(p)\right|^2-\left|\sum_pC(p)\right|^2\right\}.
 \end{aligned}
\tag{CG17}
\]
这里的密度扣除仍在同一能量内，没有取 atom 或 Type 块绝对值。
对已登记的 Hilbert 坐标及 projective 权重作一次加权 Cauchy，
即得到 §9.183 所需的 global scalar adapter，短侧 norm 使用
(CG16)，而非未投影 tensor。若共同 Fourier 使用未规范化的和，
应先把每行 \(V^{(\nu)}\) 除以 \(\sqrt g\)，与原 \(1/g\) 匹配；
乘单位相位及这一 Fourier/Parseval 操作不增加原行能量。

这修复的是有限 adapter 和短侧能量关系。要进一步沿原目标得到上界，
仍须证明 (CG17) 第二因子的实际相对能量估计。由于旧 Type-I 删格
没有证书，该相对估计目前应作用于未删格的完整系数，不能沿用
已扣除旧 \(\eta_{\rm I,S}\) 的较弱目标。

## 5. 下一个分析对象不能再次丢掉共同频率

(CG3) 的全部 \(\nu\) 可在 Cauchy 之前重组。两行 active 模数
\(p,q\)，共同 Fourier 相关的因子
\(g^{-1}\sum_\nu e_g(\nu D\overline{pq})\)，恢复的约束恰为
\[
 q m_1 n_2-p m_2 n_1+D n_1n_2\equiv0\pmod g.
\tag{CG18}
\]
证明：代入两行 (CG3) 的 \(\nu\)-相位（右行取共轭），再乘单位
\(pq n_1n_2\)。这是有限正交性，没有平均区间延长。

因此下一次 joint dispersion 可以直接使用 (CG4)、(CG18) 及
(CG14)，或使用等价的 \((\chi_p,\chi_q,\eta_1,\eta_2,\nu)\) 字符和。
需要保留的算术结构已经明确；(CG10) 的平方和等于 1 并不自动给
额外节省，(CG8) 也不允许先取绝对值后宣称分离成本亚幂次。

## 6. 一个真正可用的新子区域：零共同频率的低共同导子投影

恢复相位后，不能免费分离它；但可以直接计算它在一个共同字符
子空间上的**算子范数**。这一步不分离 \(F,G\)，因此接受实际
\(h\delta\)、Möbius、Type 和平滑权的任意组合。

令 \(E_F=\{\eta\bmod g:\operatorname{cond}(\eta)\le F\}\)，\(F\ge1\)，
\(P_{E_F}\) 为共同 \(s\)-坐标的正交投影。对任意有限 Hilbert-valued
\(Z(s,x)\) 定义规范化零行
\[
 (\mathcal L_{E_F}Z)(x)
 =g^{-1/2}\sum_{s\in U(g)}
 e_g(C\overline{ps})(P_{E_F}Z)(s,x).
\tag{CG19}
\]
对每个 \(x\) 的线性泛函取范数，再用共同字符 Parseval，得到精确式
\[
 \boxed{\|\mathcal L_{E_F}\|^2
 =\frac1{g\varphi(g)}
   \sum_{\substack{f\mid g\\f\le F}}f\,\varphi^*(f),\qquad
 \varphi^*(f)=\prod_{\ell\mid f}(\ell-2),\
 \varphi^*(1)=1.}
\tag{CG20}
\]
这里 \(\varphi^*(f)\) 是平方自由导子 \(f\) 上的原始字符数。
(CG20) 的证明只用每个诱导 Gauss 和的模长平方等于 \(f\)；
偶模因子 \(\ell=2\) 自动给出 0，不需要例外删除。
因此
\[
 \|\mathcal L_{E_F}Z\|_2^2
 \le \Gamma_g(F)\|Z\|_2^2,\qquad
 \Gamma_g(F)\ll_\varepsilon
 g^\varepsilon\min\{1,(F/g)^2\}.
\tag{CG21}
\]
上界来自 \(\varphi^*(f)\le f\)、导子因子数至多 \(\tau(g)\)、
\(g/\varphi(g)\ll_\varepsilon g^\varepsilon\)。空的有效字符子集
算子为零；\(F\ge g\) 时 (CG20) 恰为 \(\varphi(g)/g\)。
在素数 \(g\)、\(1\le F<g\) 时，它恰为 \(1/[g(g-1)]\)。

例如 \(g=5\) 时，principal-only 的范数平方为 \(1/20\)，
完整共同字符空间为 \(4/5\)；\(g=15,F=3\) 时为 \(1/30\)。
这是真正的小算子范数，不是把每个小 Gauss 元素误当成小矩阵范数。

现把两行的共同导子分别限制为
\[
 g=T^\gamma,\quad f_i\le F_i=T^{\lambda_i},
 \quad0\le\lambda_i\le\gamma.
\]
(CG21) 提供的额外**线性**节省为
\[
 \boxed{\eta_{\rm common,0}
 =(\gamma-\lambda_L)+(\gamma-\lambda_S).}
\tag{CG22}
\]
在主笔记 (9.1117) 的 mutual-character 范数中代入这两个实际零行，
再使用 §9.144 已登记的行能量界，可支付该子区域的剩余 imbalance，
只要
\[
 \boxed{2\gamma-\lambda_L-\lambda_S\ge\eta_{\rm imb}.}
\tag{CG23}
\]
此处原 baseline **只**计已有 active-cofactor
\(\kappa_L,\kappa_S\) 边际，不再另扣 \(g/f_i\) 的
imprimitive 能量节省，也不使用已撤回的 Type-I companion gain。
(CG21) 是作用于完整输入行的独立范数界；如此记账不会重复使用
§9.144 的行界。投影在 Type/外标量求和之前线性执行，所有符号保留。

极端 \(g=T,\ \eta_{\rm imb}=1/4\) 且 \(g\) 素数时，
**任一侧共同字符为 principal** 的 \(\nu=0\) 部分都满足 (CG23)：
取该侧 \(\lambda=0\)，另一侧 \(\lambda=1\)，已有线性节省 1。
以 principal/nonprincipal 两侧分块只增加固定常数，不花掉幂次；
该零频面的仍未覆盖部分包含两侧共同字符均非 principal 的扇区。
在合数 \(g\) 上，(CG23) 给出了相应可审计的低共同导子子多面体。

这不覆盖全部 \(\nu\ne0\)：完整共同 Fourier 的平方和是等距，
不能把单个 \(\nu=0\) 的小投影范数乘到所有频率。也不宣称覆盖
整个原参数格或完整 gate。它确实在恢复正确物理相位后，关闭了
一个明确的共同零频子空间，其他子空间仍需联合 dispersion。


## 7. 验证与边界

新有限审计比较原 CRT 求和 (CG2) 与消元式 (CG3)，在有理群环中
逐系数相等；涵盖零/非零/负共同频率、平方自由合数、所有单位掩码、
负 \(h,\delta\)、空支持和 Type 重组。数值根仅用于独立检查
(CG6) 的有限 Gauss Gram；不是渐近界的证据。最小 lift 的范数、
pairings 与正交性使用精确有理数验证。

本节证明了 (CG23) 指定的共同零频低导子子空间覆盖，但没有覆盖整个
原参数格，也没有把有限 signed identity 提升成完整 twisted-moment
定理。其余进展是恢复被漏掉的共同导子、撤回错误删格，并给出不损失
短侧范数的正确 scalar adapter。

English summary: common Fourier frequency zero does not erase its
inverse-ratio phase. Restoring that multiplier reinstates the common
character conductor and invalidates an unverified active-prime Type-I
coverage transfer. A canonical graph-span lift repairs the short-profile
energy comparison exactly. The normalized common-zero projection has an
explicit small norm on low-common-conductor sectors, yielding the restricted
coverage (CG23). The coupled analytic estimate is still open.

**后续覆盖。** [联合共同频率定理](2026-08-30-mwkf-joint-common-frequency.md)
的 (JF10) 另覆盖指定小共同字符族上的全频率及非零频补集。其输入是
共同族的基数，不是这里的导子截断；稠密共同字符族仍未估计，两个
覆盖界不能不经记账直接相乘。
