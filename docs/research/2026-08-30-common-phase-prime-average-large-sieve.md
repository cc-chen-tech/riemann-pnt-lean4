# 保留共同相位的素模平均：从单行到一个直接双素数界

**后续更新。** [全共同频率延拓](2026-08-30-all-common-frequencies-prime-average.md)
现已在同一共同系数、统一光滑模型内移除本文的 \(\nu=0\) 限制，
并允许任意有界的共同比例函数。下文保留零频证明及其当时的范围；
完整物理范数比较与复合 active conductor 的缺口仍未闭合。

白话结论：上一轮的单行界不能直接支付长素数占据损失。本轮改为
在取最终 Cauchy 之前控制整个短素模族，得到一个真正的平均估计。
共同相位可以任意随素模变化，但内部系数必须来自同一序列，核的
光滑半范数必须一致。在指定的双侧光滑模型上，原交叉剩余类双素数
和的上界由 \(T^{47/4+\varepsilon}\) 降至 \(T^{23/2+\varepsilon}\)。

这不是把同一个 saving 用两次，也不把任意行能量的上界当作下界。
这里证明一个**绝对**双素数界；尚未证明它与完整物理包的
\(\mathscr B_{\rm MC}\) 有所需范数比较，更没有证明全 \(\nu\)、
复合 active conductor、AFE/reflection 补集或新零点自由半平面。

复用 [联合 product Poisson 笔记](2026-08-30-common-zero-product-poisson-mobius-bound.md)
的 (P3)–(P11)、(P21)–(P22)。本篇不再调用其中的单行 Möbius
估计 (P12)，所以没有叠乘那里的 \(T^{1/4}\)。

## 1. 明确的共同系数 profile

固定平方自由 \(g>1\)、\(R\ge2\)，令 \(\mathcal Q\) 是
\((R,2R]\) 中不整除 \(g\) 的任意素数子集。固定有限序列
\(a_n\)，支撑在 \(N<n\le2N\)，\(N\ge1\) 为整数。
允许 \(a_n=\mu(n)\) 或一个已固定的 Type/companion 系数；
关键是 \(a_n\) 不随 \(q\) 改变。

对每个 \(q\)，允许任意 \(A_q\in U(g)\)，无需它随 \(q\)
光滑或等分布。令 \(F_q(x,y,t)\) 是共同紧支撑上的光滑族，
\(t\in(1,2)\)，\(x,y\) 远离零；固定阶混合导数一致有界。
不要求对离散参数 \(q\) 求导。定义

\[
 \begin{aligned}
 V_q(c)={}&\sum_{h,\delta\in\mathbb Z}\sum_n a_n
  {\bf1}_{(h\delta n,gq)=1}
  F_q(h/H,\delta/L,n/N)e_g(A_qn/(h\delta))\\
 &\qquad\times
  \left({\bf1}_{h\delta\equiv cn\ (q)}-\frac1{q-1}\right),
 \qquad c\in U(q).
 \end{aligned}
\tag{A1}
\]

所有模逆只在单位支撑上书写。\(H,L>0\) 固定；允许正负
\(h,\delta\)。相位 \(e_g(A_qn/(h\delta))\) 从未并入光滑权。
记 \(\mathcal A_2=\sum_n|a_n|^2\)。本轮主要结论是

\[
 \boxed{
 \sum_{q\in\mathcal Q}\sum_{c\in U(q)}|V_q(c)|^2
 \ll_{\varepsilon,F}(gRN)^\varepsilon
          g^2R(N+gR^2)\mathcal A_2.}
\tag{A2}
\]

这是任意 \(N\) 的估计，不要求 \(gq\le N\le(gq)^{4/3}\)。
它不是任意 level-dependent \(a_{q,n}\) 的结论。统一平滑族可以
依赖 \(q\)，但若另有随 \(q\) 变化的非平滑系数，必须先证明
共同系数展开及其成本。

## 2. 一个固定 Poisson 模式的完整共同相位范数

固定整数 \(j,k\ne0\)。当 \(q\mid jk\)，active 核精确为零，
将该 \(q\) 删去不会增加正能量。其余模数记
\[
 J_q=j\bar q_g,\quad K_q=k\bar q_g,\quad
 j'_q=j\bar g_q,\quad k'_q=k\bar g_q,
\]
以及在非单位 \(n\) 处分别零延拓的核
\[
 \begin{split}
 L_q(n)&=\frac1g\sum_{u,v\in U(g)}
     e_g(A_qn/(uv)+J_qu+K_qv),\qquad (n,g)=1,\\
 p_q(z)&=\frac{S(j'_q,k'_qz;q)-1/(q-1)}{\sqrt q},
                  \qquad (z,q)=1.
 \end{split}
\tag{A3}
\]
局部零延拓在本篇同样不可省略。固定模式的待估计行是
\[
 U_q(c)=\sum_n a_n L_q(n)p_q(cn).
\tag{A4}
\]

将共同模数中的非退化部分记为
\[
 g_0=\prod_{\substack{\ell\mid g\\\ell\nmid jk}}\ell.
\tag{A5}
\]
它与 \(q\) 无关。注意这不是上篇的 \((g,j,k)\)：这里只保留
\(j,k\) **同时**为单位的素因子。由 (P9)–(P10) 的局部精确式：

- \(\ell\nmid jk\)：得到一个 \(\operatorname{Kl}_3\) 因子；
- \(j,k\) 恰有一个被 \(\ell\) 整除：归一化因子是 \(1/\ell\)；
- 两者均被整除：归一化因子是 \(-(\ell-1)/\ell\)。

所以在 \((n,g)=1\) 上，\(L_q(n)\) 是一个常数
\(\lambda_{j,k}\)，\(|\lambda_{j,k}|\le1\)，乘以模 \(g_0\)
的三阶 Kloosterman 乘积。CRT 的单位缩放全部保留在参数中。
其单位乘性 Fourier 系数的模长至多 \(\sqrt{g_0}\)。

给任意有限 \(b_n\)，先按 \(r\bmod g_0\) 合并并保留
\((n,g)=1\)。对**全部单位相位参数**作平方平均，乘性 Parseval
给出以下未归一化界：
\[
 \sum_{A\in U(g_0)}
 \left|\sum_n b_n L_A(n)\right|^2
 \le g_0\sum_{r\in U(g_0)}
       \left|\sum_{\substack{n\equiv r\ (g_0)\\(n,g)=1}}b_n\right|^2.
\tag{A6}
\]
\(|\lambda|^2\le1\) 已用在右侧；没有多一个 \(\varphi(g_0)\)。
左端包含每个指定 \(A_q\) 的平方，所以 (A6) 可以控制任意
\(A_q\)，代价已明示为 \(g_0\)。没有假定物理相位真的在平均。
\(g_0=1\) 时单位群是单点，(A6) 直接成为恒等/缩小关系。

## 3. 在共同剩余类上用加性大筛，只付 \(N+gR^2\)

由 (P21)，或者对 active 字符作 Parseval，准确有
\[
 \sum_c|U_q(c)|^2
  =\frac q{q-1}\sum_{\chi\bmod q,\ \chi\ne\chi_0}
       \left|\sum_n a_n L_q(n)\chi(n)\right|^2.
\tag{A7}
\]
对每个字符使用 (A6)。设任意序列 \(b_n\) 的加性变换为
\(\widehat b_q(v)=\sum_n b_ne_q(vn)\)。非主素模字符的 Gauss
和模长为 \(\sqrt q\)，再用单位字符正交性，得到
\[
 \frac q{q-1}\sum_{\chi\ne\chi_0}
   \left|\sum_n b_n\chi(n)\right|^2
 \le\sum_{v\in U(q)}|\widehat b_q(v)|^2.
\tag{A8}
\]
这条不等式允许 \(q\mid n\) 的 \(b_n\)：字符在其上零延拓；
右侧没有假装这些项消失，Bessel 不等式已经支付它们。

固定 \(r\in U(g_0)\)，置 \(n=r+g_0m\)。区间内的 \(m\)
有至多 \(\lceil N/g_0\rceil\) 个整数。因 \((g_0,q)=1\)，
\(v\mapsto g_0v\) 置换 \(U(q)\)，而 \(e_q(vr)\) 是行标量。
因此对全部 \(q\in\mathcal Q\)、\(v\in U(q)\) 求和，可以直接
在 **\(m\) 的区间** 上使用加性大筛：这些约分后的分数 \(v/q\)
两两不同，圆周间距至少 \(1/(4R^2)\)。由
[Davenport–Halberstam 大筛，Harcos Theorem 1](https://www.renyi.hu/~gharcos/large_sieve.pdf)，
\[
 \sum_{q,v}\left|\sum_{n\equiv r\ (g_0)}
       a_n{\bf1}_{(n,g)=1}e_q(vn)\right|^2
 \ll (N/g_0+1+R^2)
       \sum_{n\equiv r\ (g_0)}|a_n|^2.
\tag{A9}
\]
不需要素数等分布；任意素数子集都适用。最后求 \(r\) 并乘
(A6) 的 \(g_0\)，因为 \(R\ge2\) 吸收整数 \(+1\)，得到
\[
 \boxed{
 \sum_q\sum_c|U_q(c)|^2
 \ll(N+g_0R^2)\mathcal A_2
 \le(N+gR^2)\mathcal A_2.}
\tag{A10}
\]

这解释了为什么不能直接把 (A3) 当作固定系数使用普通大筛，
也证明完整共同相位的代价没有被扩大为 \(g^2R^2\)。
非退化局部参数含 \(A_qjk\bar q^2\)，物理
\(A_q=-C_q\bar q\) 时含 \(-C_qjk\bar q^3\)；(A6) 确实处理了
这一变化，并非将 \(q^{-3}\) 删除后再证明另一个模型。

## 4. 可依赖素模的 BV 权与所有 Poisson 模式

为避免要求 \(q\) 参数光滑，先给 (A10) 一个标准的最大部分和
延拓。把原 \(n\) 区间补零到长度为二次幂；任意前缀是每层
至多一个 dyadic 区间的并。Cauchy 后至多付 \(O(\log(2N))\)，
每层用 (A10) 并对该层不交区间求和，再付一层对数，故
\[
 \sum_{q,c}\max_t
 \left|\sum_{N<n\le t}a_nL_q(n)p_q(cn)\right|^2
 \ll \log^2(2N)(N+gR^2)\mathcal A_2.
\tag{A11}
\]
每个小区间仍是共同的系数截断，没有随 \(q\) 单独选择系数。
Abel 求和遂允许任意 \(q\)-dependent 权 \(w_q(n)\)，只要
\(\|w_q\|_\infty+\operatorname{Var}(w_q)\le B\) 一致；右侧
再乘 \(B^2\)。原有硬端点包含在 BV 范数中。

对 (A1) 在两条原光滑变量 Poisson，得到
\[
 V_q(c)=\frac{HL}{gq^{3/2}}
    \sum_{j,k\ne0}\sum_n a_n L_q(n)p_q(cn)
       \widehat F_{q,12}(jH/(gq),kL/(gq),n/N).
\tag{A12}
\]
\(q\mid jk\) 的项为零；符号与 Jacobian 沿用 (P3)。
所需 \(n\)-BV 范数对每个固定 \(J>1\) 满足
\[
 \ll_{J,F}(1+|j|H/(gR))^{-J}(1+|k|L/(gR))^{-J}.
\tag{A13}
\]
这里只用了 \(h,\delta,n\) 的统一导数，没有对 \(q\) 求导。
在 \((q,c)\) 的 Hilbert 范数中使用 Minkowski，保留两条轴的
精确消失。于是
\[
 \sum_{j,k\ne0}(1+|j|H/(gR))^{-J}(1+|k|L/(gR))^{-J}
 \ll_J\frac{g^2R^2}{HL}.
\tag{A14}
\]
(A12) 的前因子至多 \(HL/(gR^{3/2})\)，和 (A14) 相乘恰为
\(g\sqrt R\)。代入 (A11) 并平方，得到 (A2)。完整模式和绝对
收敛，包含所有大 gcd 模式，无额外截断尾。

固定的 \((n,r)=1\) 可以直接并入同一 \(a_n\)，不需要再次拆
Möbius。固定 \((h,r_h)=1,(\delta,r_\delta)=1\)，各与 \(gq\)
互素时，用有限除数容斥；重标定 \(H,L,A_q,c\) 后仍适用
(A2)，只花除数函数的平方。若这些因子本身随 \(q\) 任意变化，
不能无条件把它们也称为固定系数。

## 5. 原交叉剩余类上的直接双素数上界

取长素数 \(p\in(P,2P]\)、短素数 \(q\in(R,2R]\)，\(P>2R\)，
均与 \(gD\) 互素。两侧各是 (A1) 型 profile，允许不同的
\(N_1,N_2,H_i,L_i,F_i\)、共同系数 \(a_n,b_n\) 和任意相位参数。
记 \(A_p,B_q\) 为其中心化行；也允许进一步删去任意 active
字符子集，因为这是每行 \(\ell^2\) 的正交投影。
每侧所有相位和核只依赖本侧素模及先前固定的共同标签；不能
把 \(A_p\) 暗中换成随对侧 \(q\) 改变的 \(A_{p,q}\)。

对任意 \(|\omega_{p,q}|\le1\)，考虑用户指定的原交叉剩余类：
\[
 \mathcal S=\sum_{p,q}\omega_{p,q}
         A_p(D\bar q_p)\overline{B_q(-D\bar p_q)}.
\tag{A15}
\]
固定 \(p\)，短素数在模 \(p\) 中没有重复标签；固定 \(q\)，
长素数在任意剩余类中至多 \(1+P/R\) 个整数。因此唯一的
pair-Cauchy 给
\[
 |\mathcal S|^2\le (1+P/R)
   \left(\sum_p\|A_p\|_2^2\right)
   \left(\sum_q\|B_q\|_2^2\right).
\tag{A16}
\]
现在插入的是已经在素模族中证明的新上界 (A2)，不是旧行范数
后额外乘一个来源不明的 saving。得到
\[
 \boxed{
 |\mathcal S|\ll_{\varepsilon,F_1,F_2} (gPRN_1N_2)^\varepsilon g^2
 \sqrt{PR(1+P/R)(N_1+gP^2)(N_2+gR^2)}\,
       \|a\|_2\|b\|_2.}
\tag{A17}
\]
这里没有要求外层素数 Möbius 权变号；两侧真正保留的约束是
内部共同系数以及原 \(h\delta\) 核，不是任意独立行数组。

## 6. 极端尺度与严格的覆盖边界

在 \(g=T,P=T^2,R=T^{3/2},N_1=N_2=T^3\)、
\(\|a\|_2^2,\|b\|_2^2\ll T^{3+\varepsilon}\) 的指定模型上，
\[
 \sum_p\|A_p\|_2^2\ll T^{12+\varepsilon},\qquad
 \sum_q\|B_q\|_2^2\ll T^{21/2+\varepsilon},\qquad
 |\mathcal S|\ll T^{23/2+\varepsilon}.
\tag{A18}
\]
相比同一个完成式上的逐 \(n\) Cauchy、剩余类整数计数和经典
Kloosterman 点值界，旧的两侧绝对预算分别为 \(T^{12}\)、
\(T^{11}\)，连同 \(\sqrt{P/R}\) 给 \(T^{47/4}\)。
具体地，固定模式的 (P22) 给
\(\|U_q\|_2^2\ll g^\varepsilon(N+q)\mathcal A_2\)，
再按 (A12)–(A14) 重装配，旧素模族预算为
\(g^{2+\varepsilon}R^2(N+R)\mathcal A_2\)。比较的是两个可独立
证明的绝对上界，不是实际能量的上下界比较。
因此本篇的 \(T^{1/4}\) 差别出现在**完整双素数和的绝对预算**，
不再只是单个 \(c\) 上的点态差别。

但这仍不允许宣称整个 (NPIT) 已证明：

1. 旧绝对预算不是实际 \(\mathscr B_{\rm MC}\) 的下界。
   要用 (A17) 接原定理，须把真实系数范数、Type-frequency gcd、
   共频 \(1/g\)、所有外标量和原注册行能量逐项对齐。
2. 本篇覆盖 (A1) 的 common-coefficient 光滑族，包括任意随
   \(q\) 变化的共同相位参数。未证明所有物理 \(\Lambda\)-companion、
   交叉掩码及 AFE/reflection 族都有这个表示和统一成本。
   一般 \(a_{q,n}\) 不被覆盖；如果它有已证的共同系数展开，须
   在 (A2) 的 Hilbert 范数中支付该展开的实际范数。
3. 本篇仅共同 Fourier 零频。非零 \(\nu\) 多出的
   \(e_g(B_qh\delta/n)\) 不再是这里的三阶 Gauss 核。
   复合 active conductor 的 imprimitive 字符也未由素模大筛处理。
4. \(g,P,R,N_i\) 取指数只说明指定模型的渐近账本；不提供
   有效有限高度阈值或对整个参数多面体的覆盖。

因此下一步的具体工作是核查 (A1) 的真实共同系数及归一化接入，
并研究非零共同频率的替代谱范数；不是再把 (A17) 声明为一个
未经证明的假设，也不是把全部零点结论藏在“adapter”里。

## 7. 验证记录

`scripts/check_common_phase_prime_average.py` 的 20 项检查通过，
另经独立重跑。覆盖共同参数的素数/平方自由 CRT Gram、Gauss
零剩余类差项、退化模式及 \(g_0=1\)、进程频率置换和整数舍入、
dyadic 前缀、Abel、完整模式前因子及双素数占据/指数。
解析链条和可依赖素模的 BV 强化亦经独立复核；修正了双侧核
半范数的隐常数依赖。

本轮此前十个脚本的 191 项、上述 20 项及既有覆盖检查 10 项，
合计 221 项通过。根单位恒等式使用精确分圆多项式算术；少数
有限范数是浮点 sanity check，不能外推为大筛或零点结论。
本篇的解析证明由 §§2–5 承担。未改动、未运行 Lean；未运行
全仓 baseline。未改动其他研究 worktree。

## English summary

For squarefree common modulus g and a common coefficient sequence, a
joint average over active primes q in (R,2R] controls the centered row
energy by g²R(N+gR²) times the coefficient square norm, up to explicitly
allowed smooth seminorms and logarithms. The common-phase parameter may
depend arbitrarily on q. Completing its finite unit family costs g0,
whereas the additive large sieve is applied on progressions of length
N/g0; the resulting cost is N+g0R², not gN+g²R². All degenerate Poisson
modes and q-dependent uniformly BV weights are retained. This gives an
absolute cross-residue prime-pair bound of T^(23/2) on the specified
extreme smooth model, versus the earlier T^(47/4) absolute budget. It
does not establish comparison with the full registered physical norm,
nonzero common frequencies, or any zero-free theorem.
