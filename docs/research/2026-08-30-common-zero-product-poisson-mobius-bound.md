# 共同零频的联合 product Poisson：一个有幂次节省的 Möbius 单行界

白话结论：保留共同相位并同时完成原 \(h,\delta\)，确实能证明一个
Möbius 加权单行界，而不只是换一个接口。在明确的平滑单位掩码
core 上，短侧极端尺度从逐项估计的 \(T^{19/4}\) 降到 \(T^{9/2}\)。
这个四分之一次幂节省不能直接抵消长素数平均的缺口：逐点界与原
均方占据预算不是同一种归一化。下文分别证明局部结论和写出转换成本。

**范围。** 本文只处理 (CG4) 的共同 Fourier 零频 \(\nu=0\)，保留其
\(e_g(A n/(h\delta))\) 相位。允许联合光滑幅度与固定额外互素因子；
不允许把未展开的比率同余、依赖 \(n,h,\delta\) 的算术相位或全
AFE/reflection 补集伪装成光滑幅度。完整 pre-Cauchy 长素数色散、
\(14/17\)、\(2/3\) 零点界均未证明。

特别地，(CG4) 也允许一般 Type 系数，而本篇必须从原始
\(\mu(n)\) 开始；未重装配的 \(\Lambda\)-companion、除数标签或其他
非平滑乘子不能塞入 \(F\)。本篇不是对全部 (CG4) 原子的自动适配。

来源为另一 worktree 的共同相位修正 (CG3)–(CG4) 和主笔记 §9.175；
本篇沿用 [整数 residual 审计](2026-08-30-pre-cauchy-common-determinant-residual.md)，
不混同 \(\nu=0\) 与 \(R=0\)，不再次计入此前行能量已使用的节省。

## 1. 要估计的具体物理 core

设 \(q\) 为奇素数，\(g>1\) 平方自由，\((g,q)=1\)，\(Q=gq\)；
\(A\in U(g)\)、\(c\in U(q)\) 固定。\(c\) 可以是用户原式中的
\(-D\overline p_q\)；以下上界对 \(c\) 一致，但不平均 \(p\)。
令 \(F\in C_c^\infty(\mathbb R^2\times(1,2))\)，第一、二变量支持
于离开零的固定紧集，所有所用归一化导数有明确统一界。置

\[
 \begin{aligned}
 V_c={}&\sum_{h,\delta\in\mathbb Z}\sum_{n\ge1}
 \mu(n){\bf1}_{(h\delta n,Q)=1}
 F(h/H,\delta/L,n/N)e_g(A n\overline{h\delta})\\
 &\hspace{25mm}\times
 \left({\bf1}_{h\delta\equiv cn\ (q)}-\frac1{q-1}\right).
 \end{aligned}
\tag{P1}
\]

这是有两条原光滑变量的 core；没有把 \(h\delta\) 的系数替换为一个
任意光滑序列。允许 \(h,\delta\) 两个符号。额外固定
\((n,r)=1\)、\((h,r_h)=1\)、\((\delta,r_\delta)=1\)，且各整数与 \(Q\)
互素，也可加入；其成本在 §5 单独证明。

**单行定理。** 当 \(Q\le N\le Q^{4/3}\)、\(H,L>0\)，对任意
\(\varepsilon>0\)，

\[
 \boxed{|V_c|\ll_{\varepsilon,F}
    (NQ)^\varepsilon g\sqrt q\,\sqrt{NQ}.}
\tag{P2}
\]

加入上述固定互素因子后右侧再乘
\((rr_hr_\delta)^\varepsilon\)。此处 \(F\) 的依赖是有限个明确的
Schwartz/Mellin 半范数；若物理族的这些半范数增长，必须另付增长，
不能把它包含在一个“绝对常数”中。

## 2. 双 Poisson 的准确有限算术核

令 \(\widehat F_{12}\) 只对前两个变量作 Fourier 变换，约定
\(e(x)=e^{2\pi ix}\)。固定 \(n\) 后按模 \(Q\) 的两个剩余类 Poisson，
得到精确的绝对收敛表达式

\[
 V_c=\frac{HL}{Q^2}\sum_{j,k\in\mathbb Z}
 \sum_{n\ge1}\mu(n)\widehat F_{12}(jH/Q,kL/Q,n/N)
 T_{j,k}(n),
\tag{P3}
\]

其中对 \((n,Q)>1\) 定义 \(T=0\)，否则

\[
 T_{j,k}(n)=
 \sum_{a,b\in U(Q)}e_Q(ja+kb)e_g(A n\overline{ab})
 \left({\bf1}_{ab\equiv cn\ (q)}-\frac1{q-1}\right).
\tag{P4}
\]

CRT 将它精确分成 \(G_g(n)P_q(n)\)。在模 \(g\) 中令
\(J=j\overline q,K=k\overline q\)，在模 \(q\) 中令
\(j'=j\overline g,k'=k\overline g\)，则

\[
 \begin{aligned}
 G_g(n)&=\sum_{a,b\in U(g)}
      e_g(A n/(ab)+Ja+Kb),\\
 P_q(n)&=S(j',k'cn;q)-\frac{c_q(j')c_q(k')}{q-1}.
 \end{aligned}
\tag{P5}
\]

这两个公式各自只在局部单位 \(n\) 上使用；在非单位处分别定义
\(G_g(n)=0\)、\(P_q(n)=0\)。尤其 \(P_q(0)=0\)，**不是**把
第二行右端代入 \(n=0\)。如此零延拓后 CRT 分解才对所有整数
\(n\) 成立，下面的零均值和 Fourier 变换也均指该延拓。

这里 \(S\) 为未归一化二阶 Kloosterman 和，\(c_q\) 为 Ramanujan 和。
若 \(q\mid j\) 或 \(q\mid k\)，则 \(P_q(n)\equiv0\)（单位 \(n\)）。
**因此两条完整 Fourier 坐标轴精确消失**，不是将其当作小尾删掉。
以下只需 \((jk,q)=1\)，此时 \(c_q(j')c_q(k')=1\)。

归一化核记作

\[
 K_{j,k}(n)=\frac{T_{j,k}(n)}{g\sqrt q},\qquad
 d=(g,j,k).
\tag{P6}
\]

## 3. 加性与乘性 Fourier 界：共同相位没有被丢掉

以下所有 Fourier 变换**未归一化**。对于模 \(q\) 的部分：

\[
 \sum_{n\in U(q)}P_q(n)=0,
\tag{P7}
\]

非主字符的乘性变换是两个 Gauss 和之积，绝对值为 \(q\)；主字符
变换为零。对 \(t\ne0\bmod q\)，直接先求 \(n\) 和给出

\[
 \sum_{n\in U(q)}P_q(n)e_q(-tn)
 =q\,e_q(j'k'c/t)+\frac q{q-1}.
\tag{P8}
\]

故 \(P_q/\sqrt q\) 的乘性变换上界为 \(\sqrt q\)，加性变换上界
为 \(2\sqrt q\)。零加性频率精确为零。

在 \(\ell\mid g\) 处，将 CRT 的单位乘子一并吸入 \(A,J,K\)。
若 \(JK\ne0\bmod\ell\)，则

\[
 G_\ell(n)/\ell=\operatorname{Kl}_3(AJK n;\ell).
\tag{P9}
\]

其乘性变换精确为三个 Gauss 和之积除以 \(\ell\)，所以绝对值
至多 \(\sqrt\ell\)。其加性变换为

\[
 \sum_{n\in U(\ell)}\frac{G_\ell(n)}\ell e_\ell(-tn)
 =
 \begin{cases}
 -1/\ell,&t=0,\\
 S(A,JK/t;\ell)-1/\ell,&t\ne0.
 \end{cases}
\tag{P10}
\]

证明可直接令 \(n=zab\)，先对 \(a\) 求和：
\(\sum_{a\in U(\ell)}e_\ell(a(J-tzb))
=\ell{\bf1}_{J=tzb}-1\)。这也核查了末项的负号。

非单位 Fourier 参数不能丢掉：若 \(J,K\) 中恰好一个为零，则对
单位 \(n\)，\(G_\ell(n)=1\)；两者均为零，则 \(G_\ell(n)=-(\ell-1)\)。
因此前者的归一化 Fourier 范数至多 1，后者至多 \(\ell\)。
后一情形相对于 \(\sqrt\ell\) 只多 \(\sqrt\ell\)，不是 \(\ell\)。

由 CRT、Gauss 和、经典 Weil/Deligne 界，

\[
 \begin{aligned}
 \|K_{j,k}\|_\infty&\le 3^{\omega(g)+1},\\
 \max_t|\widehat K_{j,k}(t)|&\ll_\varepsilon
          Q^\varepsilon\sqrt{Qd},\\
 \max_{\chi\bmod Q}|\widetilde K_{j,k}(\chi)|
       &\le\sqrt{Qd},\qquad \widehat K_{j,k}(0)=0.
 \end{aligned}
\tag{P11}
\]

乘性变换在 \(U(Q)\) 上取，\(\chi\) 包括所有 imprimitive 字符。
所用点值输入只有 \(|\operatorname{Kl}_2|\le2\)、
\(|\operatorname{Kl}_3|\le3\)；定义和标准纯性来源见
[Fouvry–Kowalski–Michel, §1 与 §5.2](https://arxiv.org/pdf/1211.6043)。
不调用其 sums-over-primes 结论，也不声称获得新的有限域定理。

## 4. 从两个 Fourier 范数直接证明 Möbius 界

设一般周期核 \(K\) 在模 \(Q\) 的非单位处为零，完整均值为零，
并满足 (P11)。对固定光滑 \(W\) 支持在 \((1,2)\)，证明

\[
 \left|\sum_n\mu(n)K(n)W(n/N)\right|
 \ll_{\varepsilon,W}(NQ)^\varepsilon\sqrt{NQd},
 \qquad Q\le N\le Q^{4/3}.
\tag{P12}
\]

取 \(U=\lceil2N/Q\rceil\)。因 \(Q\ge6\)，原支撑 \(n>N\) 上有
\(n>U\)。精确 two-cutoff 恒等式为

\[
 \mu(n)=
 -\sum_{\substack{bcr=n\\b,c\le U}}\mu(b)\mu(c)
 +\sum_{\substack{bcr=n\\b,c>U}}\mu(b)\mu(c).
\tag{P13}
\]

没有额外 Type 剩余项。非单位 \(bcr\) 的项原核已为零。

**Type I。** 固定 \(b,c\) 后，unsigned quotient \(r\) 的核
\(K(bcr)\) 仍周期 \(Q\) 且均值零（仅需考虑 \((bc,Q)=1\)）。
由加性 Fourier 完成与调和和，任意区间上的和
\(\ll Q^\varepsilon\sqrt{Qd}\log(2Q)\)；Abel 求和允许原光滑权。
故全部 \(b,c\le U\) 的成本为

\[
 \ll (NQ)^\varepsilon U^2\sqrt{Qd}.
\tag{P14}
\]

均值为零很重要：没有一个被漏掉的 quotient 长度主项。

**Type II。** 将 \(s=cr\) 合并，\(\beta_s=\sum_{c\mid s,c>U}\mu(c)\)，
\(|\beta_s|\le\tau(s)\)。原条件给
\(b>U,s>U\)，且 \(b,s<2N/U\le Q\)。因此它们在单位剩余类中
都是不重复的整数标签，不需付 \(\lceil b/Q\rceil\) 的重数。
按 \(b,s\) 作 dyadic 分块，保留 \(bs\asymp N\)。用 \(W\) 的
Mellin 反演分离平滑乘积权，变换的 \(L^1\) 成本由固定导数控制。
每块仍保留 \(U<b<Q,U<s<Q\) 的截断；不能为了使用整个 dyadic
区间而重新引入模 \(Q\) 的重复标签。

乘性矩阵 \(K(xy)\) 的奇异值恰为
\(|\widetilde K(\chi)|\)：乘性字符变换后只另有一个逆元排列。
所以每块为

\[
 \ll\sqrt{Qd}\|\alpha\|_2\|\beta\|_2
 \ll (NQ)^\varepsilon\sqrt{NQd}.
\tag{P15}
\]

对数个块吸入 \(\varepsilon\)。最后
\(U^2\sqrt Q\ll N^2Q^{-3/2}\le\sqrt{NQ}\)，其中最后一步准确等价
于 \(N\le Q^{4/3}\)。由 (P13) 得 (P12)。这是一个真实的 Möbius
估计，但只对具备这两个 Fourier 范数的核成立；乘性字符核自身
的矩阵范数为 \(\varphi(Q)\)，不满足所用平方根假设。

## 5. 完整额外互素条件，不只保留小因子

先加 \((n,r)=1\)，\((r,Q)=1\)。精确卷积为

\[
 \mu(n){\bf1}_{(n,r)=1}
 =\sum_{\substack{s\mid n\\s\text{ is }r\text{-smooth}}}\mu(n/s).
\tag{P16}
\]

所有 \(r\)-smooth 正整数（含素数幂）都在和内。
当 \(s\le N/Q\)，内和长度 \(N/s\in[Q,Q^{4/3}]\)，
\(K(sm)\) 的两个 Fourier 范数不变，使用 (P12)。
当 \(s>N/Q\)，用 (P11) 的点值界及整数个数 \(O(N/s+1)\)；
非空支持要求 \(s<2N\)，所以 \(N/s+1\le3N/s\)。

利用

\[
 \sum_{s\ r\text{-smooth}}s^{-1/2}
 =\prod_{\ell\mid r}(1-\ell^{-1/2})^{-1}
 \ll_\varepsilon r^\varepsilon,
\tag{P17}
\]

小因子总成本为 \((NQr)^\varepsilon\sqrt{NQd}\)；大因子由
\(\sum_{s>N/Q}s^{-1}\le(N/Q)^{-1/2}\sum_s s^{-1/2}\) 也达到此界。
没有丢掉整数端点或大因子。

固定的 \((h,r_h)=1,(\delta,r_\delta)=1\) 先作有限除数容斥，
然后令 \(h=a h',\delta=b\delta'\)。因 \((ab,Q)=1\)，只改变
\(H,L,A,c\) 的单位缩放；每个缩放后仍有 (P2)，对除数只付
\(\tau(r_h)\tau(r_\delta)\)。这不处理一般的
\(h\delta\equiv c'n\pmod r\) 或额外混合相位；后者必须保留新的
模数/变换成本，不能引用 (P16) 当作已消除。

## 6. 双 Fourier 模式与所有 gcd 层一起求和

\(\widehat F_{12}(\xi,\eta,t)\) 及所需 \(t\)-导数满足任意固定阶的
\((1+|\xi|)^{-J}(1+|\eta|)^{-J}\) 衰减。对每个 \((j,k)\) 使用
(P12) 后，唯一需要的算术模式和是，令 \(a=Q/H,b=Q/L\)，

\[
 \sum_{j,k\ne0}\sqrt{(g,j,k)}
 (1+|j|/a)^{-J}(1+|k|/b)^{-J}\ll_J ab
 \qquad(J\ge2).
\tag{P18}
\]

证明使用平方自由恒等式
\(\sqrt{(g,j,k)}=\sum_{d\mid(g,j,k)}
\prod_{\ell\mid d}(\sqrt\ell-1)\)。对 \(j,k\) 的非零 \(d\)-倍数
分别求和，每个至多 \(C_Ja/d,C_Jb/d\)，最后
\(\sum_{d\mid g}d^{1/2}/d^2\le\zeta(3/2)\)。
这个估计保留了稀疏大 gcd 模式，而不是逐模式以 \(\sqrt g\) 上界。

将 (P18) 代入 (P3)，\(HL/Q^2\) 与 \(ab\) 正好抵消，得到 (P2)。
完整模式和绝对收敛，没有未经计费的 Fourier 截断尾。
若 \(H/Q\) 或 \(L/Q\) 是固定正幂的大量，保留更高阶 Schwartz
衰减还能给相应任意幂次衰减；这里只登记最简单的一致界。

## 7. 极端面与为什么仍不能宣称长素数平均闭合

在明确的 short-row 模型
\(g=T,q=T^{3/2},Q=T^{5/2},N=T^3,H=L=T^{5/2}\) 上，
(P2) 给

\[
 |V_c|\ll T^{9/2+\varepsilon},
\tag{P19}
\]

而对同一个归一化完成式逐 \(n\) 取绝对值只有
\(g\sqrt q\,N=T^{19/4}\)。二者差 \(1/4\)，确有局部幂次节省。
但均方预算与逐点预算不能混用。

固定一个短 \(q\)，写原外平均为
\(\sum_p C(p)\overline{V_{-D/p}}\)。若长素数集合大小为 \(M_P\)，
最大短剩余类占据数为 \(n_{\max}\)，两种合法上界分别是

\[
 \begin{aligned}
 |\text{平均}|&\le\|C\|_2\sqrt{n_{\max}}\|V\|_2,\\
 |\text{平均}|&\le\|C\|_2\sqrt{M_P}\|V\|_\infty.
 \end{aligned}
\tag{P20}
\]

所以用 (P19) 替换第一行时，必须付 \(\sqrt{M_P/n_{\max}}\)；
不能只因局部节省为 \(T^{1/4}\) 就抵消 NPIT 的 \(T^{1/4}\)。
在占据近均匀的情形，该代价约为 \(\sqrt q=T^{3/4}\)，远大于
上述局部收益。实际 \(\|V\|_2\) 的已证明界仍须按原标签插入，
不能用它的上界充当下界来宣称相对 delocalization。

因此 (P2) 是可复用的真实单行界与长光滑变量子域控制，不是原
pre-Cauchy prime-pair estimate。下一步仍需在 (P3) 的两侧模式、
两个 Möbius 序列和长素数系数尚未分开取绝对值时得到联合估计。
未受 (P1) 处理的物理算术掩码、非零共同频率和 AFE/reflection
补集也继续留在原证明义务中。

## 8. 固定模式的精确剩余类能量：把缺口写回有符号相关

还有一个比逐点界更直接的诊断。固定 \(j,k\) 且 \((jk,q)=1\)，
固定共同相位参数 \(A\) 及全部平滑权，只让 \(c\in U(q)\) 变化。
记
\[
 p(z)=\frac{S(j',k'z;q)-1/(q-1)}{\sqrt q},\qquad z\in U(q).
\]
其所有非主乘性 Fourier 系数模长恰为 \(\sqrt q\)，主系数为零。
因此不是只有算子范数上界，而有精确 Gram 恒等式
\[
 \sum_{c\in U(q)}p(ca)\overline{p(cb)}
   =q\left({\bf1}_{a=b}-\frac1{q-1}\right),\qquad a,b\in U(q).
\tag{P21}
\]
这是字符正交性的直接推论。对任意有限系数 \(a_n\)，限定
\((n,q)=1\)，置
\[
 B(a)=\sum_{n\equiv a\ (q)}a_n,\qquad
 U(c)=\sum_n a_n p(cn).
\]
则精确有
\[
 \boxed{\sum_{c\in U(q)}|U(c)|^2
   =q\sum_{a\in U(q)}|B(a)-\overline B|^2,
 \qquad \overline B=\frac1{q-1}\sum_a B(a).}
\tag{P22}
\]
这里 \(\overline B\) 表示剩余类均值，非复共轭。
对 (P3) 中一个固定模式，取
\(a_n=\mu(n)G_g(n)\widehat F_{12}(jH/Q,kL/Q,n/N)/g\)，
并显式保留 \((n,q)=1\)，即完全保留共同 \(g\)-相位。

若 \(a_n\) 支持在 \((N,2N)\) 且 \(|a_n|\ll Q^\varepsilon\)，
逐剩余类 Cauchy 只给
\(\sum_a|B(a)-\overline B|^2\ll (N+N^2/q)Q^{O(\varepsilon)}\)。
要将其降到平方根型的 \(NQ^{O(\varepsilon)}\)，一个明确的充分输入是
\[
 \left|
 \sum_{n\ne m}a_n\overline{a_m}
    \left({\bf1}_{n\equiv m\ (q)}-\frac1{q-1}\right)
 \right|\ll NQ^{O(\varepsilon)}.
\tag{P23}
\]
对角项准确是 \((1-1/(q-1))\sum_n|a_n|^2\)；未将有符号非对角项
替换成正主项。 (P23) 在此仍未证明。

这说明 active Kloosterman 变换在均值零子空间上只是乘以
\(\sqrt q\) 的等距变换，**它本身不会改善输入的剩余类方差**。
要改进长素数平均，必须控制留下来的共同相位加权 Möbius 相关，
或在不同 \((j,k)\)、不同素模和两侧 profile 之间直接利用抵消。
(P22) 只对同一冻结模式/共同参数成立；实际 \(A\) 或核随 \(p\)
变化时须保留该依赖，不能把整个外平均当作同一个 \(U\)。因此
这是一条准确的研究靶标，不是完整 NPIT 的等价判据或已有闭合。

## 9. 有限核查与证明边界

`scripts/check_common_zero_product_poisson.py` 的 26 项检查通过，覆盖
精确 CRT、局部零延拓、两条消失轴、加性 Fourier 与二/三 Gauss
乘性恒等式、非单位频率、two-cutoff 恒等式、Type-II 截断、完整
互素卷积、频率除数账本、剩余类 Gram 与有符号非对角分解。
根单位恒等式在 \(\mathbb Q[X]/\Phi_m(X)\) 中比较；少数范数检查
只是小模数浮点 sanity check，未用来证明 Weil/Deligne 界或解析尾界。

连同本 PR 先前九个脚本的 165 项和既有覆盖检查 10 项，本轮共
201 项通过。解析结论依赖 §§2–6 的纸面证明及其明确平滑性假设，
不依赖有限枚举外推。未修改、未运行 Lean，未运行全仓 baseline。
源公式只读复核自 `docs-mobius-weighted-offdiagonal-20260824` 的
`63c2b6521d8ae4406cc23642aa50a28c28e43aa6`，没有改动该 worktree。

## English summary

Joint Poisson summation in the original two smooth product variables
produces a normalized hyper-Kloosterman factor at the common squarefree
modulus and a principal-subtracted Kloosterman factor at the active prime.
Both additive and multiplicative Fourier norms are controlled, including
all nonunit dual-frequency strata. An elementary two-cutoff Möbius
decomposition then gives a square-root \(NQ\) bound for \(Q\le N\le Q^{4/3}\).
All fixed coprimality factors and all Poisson modes can be reassembled.
The resulting \(T^{1/4}\) pointwise gain on the specified short-row model
does not automatically pay the long-prime occupancy cost. The complete
physical coupled estimate and every new zero-free theorem remain open.
For a frozen Poisson mode, an exact active-prime Gram identity identifies
its squared row norm with q times the centered residue-class variance of
the common-phase-weighted Mobius coefficients. The needed signed variance
bound and cross-mode/cross-prime recombination have not been established.
