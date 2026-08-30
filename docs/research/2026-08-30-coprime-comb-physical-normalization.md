# 互素 comb 的完整卷积与物理前因子核查

本次继续把局部结果接回原算术和：固定模数的互素条件、密度乘子以及单变量
有界变差权重可以完整保留，包括卷积中的大因子尾。但是，旧稿从双 Poisson
到短余因子重组的公式出现了一个额外的 \(S^{-1}\)。在该幅度没有从原核中
得到证明以前，局部对数消去不能推出其声称的全局界。

**这不是长 mollifier 渐近式的反例，也不是零点界。** 本文不改旧研究分支，
不把额外的核幅度估计当作已证条件，不修改 Lean。

## 1. 使用的已核查局部结论

沿用[全模式笔记](2026-08-30-cubic-comb-mode-density-audit.md)的参数：

\[
 \epsilon_0=1/1000,\quad 1/2\le u\le3,\quad S=T^u,\quad
 e\le T^{\epsilon_0},\quad D=S/e,\quad 1\le A\le S,
\]

\[
 |kl|\le T^p(\log T)^{C_P},\qquad 0\le p\le2u.
 \tag{1}
\]

\(W\in C_c^\infty((1,2))\)，\(\Phi_T(x,y)\) 的固定支集和所有所需
光滑半范数一致至多损失固定对数幂。对 \(r\le D^{\epsilon_0}\)，已得

\[
 \frac1{e^2}\sum_n\frac{\mu(n)}{rn}W(rn/D)
 \sum_c\Phi_T\left(rn/D,\frac{rnc-Akl}{A}\right)
 \ll_B\frac1{re^2}\left(1+\frac AD\right)(\log T)^{-B}.
 \tag{2}
\]

该结论使用 [MRSTT Theorem 1.1(i)](https://arxiv.org/html/2411.05770v2#S1.Thmtheorem1.1)
及连续滑动窗口证明，而不是假设所有短区间均有相同消去。

(2) 还允许乘一个与 \(c\) 无关的权重 \(U(rn)\)，只需

\[
 \|U\|_{\infty,[D,2D]}+\operatorname{Var}_{[D,2D]}U
 \ll(\log T)^{C_U}. \tag{3}
\]

证明是在原笔记的 Abel 求和中使用
\(\operatorname{Var}(bU)\le\|U\|_\infty\operatorname{Var}b+
\|b\|_\infty\operatorname{Var}U\)。合成 \(U(rn)\) 不增变差。
这包括硬区间选择、一个固定光滑截断及它们的有限乘积。对 \(q\ge1,N>1\)，
\(p_N(qd)=\max(0,1-\log(qd)/\log N)\) 在此支集上单调且介于零与一，
故也满足 (3)。**这不处理依赖 \(c\) 的任意算术权重。**

## 2. 精确保留互素条件和密度乘子

令 \(Q\le T^{C_Q}\) 为正整数，\(\kappa\in\{0,1\}\)，定义

\[
 g(d)=\prod_{p\mid d}\frac p{p+1},\qquad
 f_{Q,\kappa}(d)=\mu(d)g(d)^\kappa\mathbf1_{(d,Q)=1}.
\]

定义非负乘法函数 \(h_{Q,\kappa}\)，使 \(h(1)=1\)，且对所有 \(a\ge1\)，

\[
 h_{Q,\kappa}(p^a)=
 \begin{cases}
 1,&p\mid Q,\\
 0,&p\nmid Q,\ \kappa=0,\\
 1/(p+1),&p\nmid Q,\ \kappa=1.
 \end{cases}
 \tag{4}
\]

逐个素数幂计算 \(h(p^a)-h(p^{a-1})\) 即得精确卷积

\[
 \boxed{f_{Q,\kappa}=\mu*h_{Q,\kappa}.} \tag{5}
\]

\(\kappa=0\) 时 \(h\) 是 \(Q\)-smooth 整数的示性函数；
\(\kappa=1\) 时则在 \(Q\) 外的素数上也不为零，不能仍只求和
\(Q\)-smooth 因子。

记 \(H_{Q,\kappa}(\sigma)=\sum_r h_{Q,\kappa}(r)r^{-\sigma}\)。
对 \(\sigma>0\)，Euler 乘积绝对收敛且为

\[
 H_{Q,\kappa}(\sigma)
 =\prod_{p\mid Q}(1-p^{-\sigma})^{-1}
 \prod_{p\nmid Q}
 \left(1+\frac{\kappa}{(p+1)(p^\sigma-1)}\right).
 \tag{6}
\]

特别地，

\[
 H_{Q,0}(1)=\frac Q{\varphi(Q)},\qquad
 H_{Q,1}(1)=\zeta(2)\prod_{p\mid Q}(1+p^{-1})
 \le\zeta(2)\frac Q{\varphi(Q)}
 \ll(1+\log Q)^2. \tag{7}
\]

这里的最后一步可用原笔记的有限除数恒等式，不需零点假设。
另外存在绝对常数，使得

\[
 H_{Q,\kappa}(1/2)
 \ll\exp(C\sqrt{\log(2Q)})=T^{o(1)}. \tag{8}
\]

证明：\(Q\) 外的无限乘积由 \(\sum_p p^{-3/2}<\infty\) 控制。
对 \(Q\) 内的有限乘积，取 \(L=\max(2,\log(2Q))\)；小素数贡献
至多 \(O(\sum_{n\le L}n^{-1/2})=O(\sqrt L)\)，大素数至多有
\(\log Q/\log L\) 个，其贡献不超过
\(O(\log Q/(\sqrt L\log L))\)。又
\(-\log(1-p^{-1/2})\ll p^{-1/2}\)，得到 (8)。

## 3. 不遗漏大卷积因子的完整局部界

定义

\[
 \mathcal F_{Q,\kappa}
 =\frac1{e^2}\sum_{d\ge1}\frac{f_{Q,\kappa}(d)}d
 W(d/D)U(d)\sum_{c\in\mathbb Z}
 \Phi_T\left(d/D,\frac{dc-Akl}{A}\right).
 \tag{9}
\]

**命题。** 在 (1)、(3) 及上述核条件下，对任意固定 \(B>0\)，

\[
 \boxed{|\mathcal F_{Q,\kappa}|
 \ll_B\frac1{e^2}\left(1+\frac AD\right)(\log T)^{-B}.}
 \tag{10}
\]

所有常数对 \(Q\le T^{C_Q}\) 一致。

证明：用 (5) 写 \(d=rn\)，并令 \(R=D^{\epsilon_0}\)。对 \(r\le R\)
使用 (2)，求和成本是 (7)。先提高 (2) 所取的任意对数节省，即得 (10)
对小因子部分的界。

大因子部分不再使用 Möbius 消去。由固定 \(y\)-支集，对于 \(d\asymp D\)，
允许的整数 \(c\) 至多 \(O(1+A/D)\) 个。并且只有 \(r\le2D\) 有贡献；
此时

\[
 \#\{n:D<rn<2D\}\le D/r+1\le3D/r.
\]

故每个 \(r\) 的绝对贡献至多
\(e^{-2}(1+A/D)r^{-1}(\log T)^C\)。这一步同时支付了整数端点，
不以 \(D/r\gg1\) 为前提。用 Rankin 界，

\[
 \sum_{r>R}\frac{h_{Q,\kappa}(r)}r
 \le R^{-1/2}H_{Q,\kappa}(1/2)
 \ll D^{-1/2000}\exp(C\sqrt{\log(2Q)}).
 \tag{11}
\]

由于 \(D\ge T^{499/1000}\)，右侧为
\(T^{-499/2000000+o(1)}\)，足以吸收任意指定对数损失。
所以大因子尾同样满足 (10)。证毕。

在短余因子原式中可直接取 \(Q=Ae\)；固定额外互素模数也可并入 \(Q\)。
因此这部分互素条件及全部卷积因子已不需要条件性输入。
\(\kappa=1\) 处理的是截断密度修正的算术系数，但 (10) 仍带原有
\(d^{-1}\) 权；不能在用于无此权的修正项时偷偷删去一个 \(D\)。

## 4. 从原 MMKLS 到 comb 的前因子必须一致

本节核对旧稿 commit `7cc472d4` 的
`2026-08-25-mwkf-alternative-routes-spike.md`，特别是
\((\mathrm{MMKLS})_q^L\)、(4.845dc_14xq_35p)、(35u) 及 (35w31n29a1)。
保留任意一个原始分离张量的幅度 \(F_{A,m}(s)\)，并写

\[
 \mathcal M=\sum_A\frac{\alpha(A)}A
 \sum_{\substack{s\ge1\\(s,A)=1}}\frac{\mu(s)}s
 \sum_m F_{A,m}(s)\sum_{h,\delta\in\mathbb Z}
 u(h/H)v(\delta/L)S(\bar A m,-h\delta;s).
 \tag{12}
\]

核和截断使所需原变量和有限，或者使变换后级数绝对收敛。双 Poisson 的
精确结果是

\[
 \mathcal M=HL\sum_A\frac{\alpha(A)}A\sum_{m,k,l}
 \sum_{\substack{s\ge1\\(s,A)=1}}
 \frac{\mu(s)c_s(m+Akl)}{s^2}
 F_{A,m}(s)\widehat u(kH/s)\widehat v(lL/s).
 \tag{13}
\]

这里用 \((A,s)=1\) 把 Ramanujan 参数从 \(\bar A m+kl\) 换成
\(m+Akl\)。在平方自由支集上，令 \(s=de\)，则有精确恒等式

\[
 \frac{\mu(s)c_s(n)}{s^2}
 =\sum_{\substack{de=s\\d\mid n\\(d,e)=1}}
       \frac{\mu(d)}d\frac{\mu^2(e)}{e^2}.
 \tag{14}
\]

因而把 \(m=dc-Akl\) 代回后，短余因子项的外因子是 **\(HL\)**，
局部核中必须原样保留

\[
 F_{A,dc-Akl}(de)\widehat u(kH/(de))\widehat v(lL/(de)).
 \tag{15}
\]

这时 (9) 正好描述其局部 \(d,c\) 求和的代数形式，含 \(\mu(d)/(de^2)\)，
而不是再乘一次 \(S^{-1}\)。调用 (10) 仍须验证 (15) 回代核的固定支集及
半范数条件；一般 \(F\) 不自动满足它们。相反，长余因子密度替换

\[
 \sum_e\frac{\mu^2(e)}{e^2}W(de/S)\mathbf1_{(e,dA)=1}
 \sim\frac dS\times\text{density integral}
\]

确实把 \(HL\) 改成 \(HL/S\)，同时把 \(d^{-1}\mu(d)\) 改成
\(\mu(d)g(d)\) 型系数。**这一个密度替换的 \(S^{-1}\) 不能同时用于仍然
保留原始 \(\mu(d)/(de^2)\) 的短余因子项。**

旧稿 (35w31n29a1) 写作 \((HL/S)\sum\cdots\mathcal C\)，而紧接着定义的
\(\mathcal C\) 仍有 \(\mu(n)/(rne^2)\)。要从 (12) 得到这种写法，必须
另外证明实际张量能精确写成
\(F_{A,m}(s)=S^{-1}\widetilde F_{A,m}(s)\)，且
\(\widetilde F\) 及所有转换后的核半范数仍一致至多为对数幂。
单纯把 \(S\) 移进核会把核范数乘以 \(S\)，没有估计收益。

上游 (4.845ah)–(4.845ai) 只声明归一化四变量核的对数半范数和核分解
总范数；(4.845ao)–(4.845aq_1) 明确保留 \(E/s\)、\(E=R/A\)
以及除以 \(R\) 的归一化。它们本身没有给出上述额外的 \(S^{-1}\) 幅度。

继续核对同一 commit 的 `2026-08-24-mobius-weighted-off-diagonal.md`
中 (5.13b)–(5.15)：

\[
 \frac{\sqrt{S/R}}{\sqrt{rs}\,s}
 =\frac1{RS}u^{-1/2}v^{-3/2},\qquad
 \mathcal O_q=\frac{2T}{qRS}\mathfrak S_q[\Psi].
 \tag{15a}
\]

\(1/(RS)\) 已在外因子中；核只吸收无量纲因子，不能再从此处提取
一个 \(S^{-1}\)。旧稿开头 (2.2) 另有合法的
\(\mathfrak S_q=(HL/S)\mathfrak D_q^{(2)}\)，但 (2.3) 在
\(\mathfrak D_q^{(2)}\) 内显式保留 \(S/s\)，同样没有免费增益。
若另定义 \(\mathcal O^{\mathrm{short}}=\mathrm{MMKLS}_{\mathrm{short}}/S\)，
则右侧目标也必须除以 \(S\)；旧稿未展示这个重定义。

这些恒等式定位了一个精确的回代义务；没有把任意张量当作物理核的反例。

## 5. 这对下一步算术目标有什么影响

若只知道 (15) 归一化后有对数半范数，且
\(\sum_{A\asymp A_0}|\alpha(A)|/A\ll(\log T)^C\)，那么对非轴双频率
数目 \(\mathcal N\ll S^2(HL)^{-1}(\log T)^C\)，(10) 给出的直接绝对聚合
只是

\[
 HL\mathcal N\sum_{e\le T^{\epsilon_0}}
 \left(\frac1{e^2}+\frac{A_0}{eS}\right)(\log T)^{-B}
 \ll_B S^2(\log T)^{-B}. \tag{16}
\]

原 MMKLS 目标是 \(S(\log T)^{-B}\)。在 \(S=T^u\) 的幂次范围内，任意
固定对数节省都不填补这一个 \(S\) 因子。坐标轴、共同相位以及其他导子
模式可能带来进一步抵消，但不能由 (16) 推断已经获得。

可继续攻的对象因此更具体：

- 若实际核确有额外 \(S^{-1}\)，从原始积分展示其精确来源及所有半范数；
- 否则，在共同 \((A,k,l)\) 系数求和中获得 (16) 没有使用的幂次抵消；
- 长余因子截断修正必须和其 \(d^{-1}\) 是否存在、实际 \(d\)-范围一起处理。

不能把解决固定互素模数的 (10) 报告为已经解决上述幂次问题。
局部定理、完整长 mollifier 渐近式和高高度零点排除仍是三个不同层次。

## 6. 检查范围

`scripts/check_cubic_comb_mode_density.py` 现有 19 个标准库测试，新增部分
核对 (5) 的素数幂/有限卷积、(7) 的有限 Euler 乘积、(11) 的有限 Rankin
比较、整数端点，以及带 \(\mu(s)/s\) 的离散双完成。另对
\(s=S=5,n=1\) 检查 (14) 的系数为 \(1/25\)，拒绝多乘一次
\(S^{-1}\) 所得到的 \(1/125\)。这些有限检查不证明 MRSTT 或无限渐近式。

### English scope summary

The local all-mode estimate extends to fixed coprimality constraints, the
density multiplier, bounded-variation tapers, and the full convolution tail.
The exact short-cofactor transformation retains an outer factor HL. An HL/S
formula with the same local d-inverse weight requires an additional physical
kernel amplitude bound not supplied by the displayed tensor seminorms. This
is a normalization obligation, not a counterexample to the full asymptotic.
