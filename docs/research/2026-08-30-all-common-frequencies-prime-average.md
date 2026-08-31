# 全共同频率的素模平均：用双模式密度支付退化核

**后续加强。** [真实共同频率 Parseval 与导子分层](2026-08-30-common-frequency-parseval-conductor-average.md)
进一步利用物理族 \(f_c(t)e_g(\nu u_ct)\) 的频率正交性，在平方
平均中省去一个 \(g\)，并接入复合本原 active 导子及带单位掩码的
诱导层。本文任意独立比例函数的逐频一致界仍保留原有适用范围。

白话结论：上一轮的素模平均只处理共同 Fourier 零频。本轮把
共同相位推广为任意有界的模 \(g\) 比例函数，因而覆盖全部共同
频率。退化核确实可能变大；我们没有删除它，而是用两条 Poisson
频率同时为某个除数的倍数这一稀疏性支付其增长。最终素模平均
和双素数绝对上界保持原有幂次，没有再损失一个 \(g\)。

**证明边界。** 本篇证明共同系数、统一光滑核模型的结论。它修复
[上一轮笔记](2026-08-30-common-phase-prime-average-large-sieve.md)
§6 第 3 项的“仅共同零频”限制，但不声称处理复合 active
conductor、任意随素模变化的系数、完整物理范数比较或任何新零点
自由半平面。特别地，\(14/17\) 和 \(2/3\) 仍未由此证明。

## 1. 允许任意共同比例函数的定理

沿用上篇 (A1) 的约定：\(g>1\) 平方自由，\(q\in\mathcal Q\)
是 \((R,2R]\)、\(R\ge2\) 中不整除 \(g\) 的任意素数子集；
\(a_n\) 是同一个有限序列，支撑 \(N<n\le2N\)，\(N\) 为正整数。
\(F_q(x,y,t)\) 具有共同紧支撑，\(t\in(1,2)\)、\(x,y\) 远离
零，固定阶混合导数一致有界。允许 \(F_q\) 随 \(q\) 变化；不要求
对 \(q\) 求导。令 \(f_q:U(g)\to\mathbb C\) 任意，\(|f_q|\le1\)。
它不必随 \(q\) 平滑，也不必是 CRT 乘积。定义

\[
 V_q^f(c)=\sum_{h,\delta,n}a_n{\bf1}_{(h\delta n,gq)=1}
 F_q(h/H,\delta/L,n/N)f_q(h\delta\bar n_g)
 \left({\bf1}_{h\delta\equiv cn\ (q)}-\frac1{q-1}\right).
\tag{F1}
\]

\(H,L>0\)。所有模逆只在单位支撑上使用。写
\[
 \mathfrak C(g)=\sum_{d\mid g}\frac{\varphi(d)}{d^2}
 =\prod_{\ell\mid g}(1+\ell^{-1}-\ell^{-2}).
\tag{F2}
\]
则有显式保留退化因子的估计
\[
 \boxed{\sum_q\sum_{c\in U(q)}|V_q^f(c)|^2
 \ll_F \mathfrak C(g)^2\log^2(2N)\,
       g^2R(N+gR^2)\sum_n|a_n|^2.}
\tag{F3}
\]
隐常数仅依赖共同支撑及有限个光滑半范数，与所有 \(f_q\) 无关。
例如每个 \(x,y\) 方向至三阶、\(t\) 方向至一阶的混合导数足够。
\(\mathfrak C(g)\ll_\varepsilon g^\varepsilon\)：对大素数
\(1+1/\ell\le\ell^\varepsilon\)，有限个小素数并入常数。
故 (F3) 具有上篇 (A2) 相同的 \((gRN)^\varepsilon\) 版本。

## 2. 完整有限核的乘性 Fourier 范数

固定 \(j,k\ne0\)，令 \(J=j\bar q_g,K=k\bar q_g\)，并定义
\[
 L_q(n)=\frac1g\sum_{u,v\in U(g)}
       f_q(uv\bar n_g)e_g(Ju+Kv),\qquad n\in U(g),
\tag{F4}
\]
在非单位 \(n\) 处零延拓。取单位群字符 \(\chi\)，约定
\(\widehat L(\chi)=\sum_nL(n)\overline{\chi(n)}\) 和
\(\tau_J(\bar\chi)=\sum_u e_g(Ju)\overline{\chi(u)}\)。
置 \(t=uv/n\)，有限和换元准确给出
\[
 \widehat L_q(\chi)=
   \frac{\tau_J(\bar\chi)\tau_K(\bar\chi)}g
       \sum_{t\in U(g)}f_q(t)\chi(t).
\tag{F5}
\]
右侧的字符是 \(\chi\)，不是 \(\bar\chi\)；它只是把输入的
Fourier 下标取逆，并不改变 Parseval 范数。

为控制乘子，在每个 \(\ell\mid g\) 的局部单位群使用：

| 局部 \(J,K\) | 主字符的乘子模长 | 非主字符的乘子模长 |
|---|---:|---:|
| 两者均非零 | \(1/\ell\) | \(1\) |
| 恰有一者为零 | \((\ell-1)/\ell\) | \(0\) |
| 两者均为零 | \((\ell-1)^2/\ell\) | \(0\) |

这是素模 Gauss 和的直接结果：非零加性参数的主字符和为
\(-1\)，非主字符和模长为 \(\sqrt\ell\)；零加性参数只保留主
字符。后一个模长公式也可直接展开平方后用加性正交性证明。
\(\ell=2\) 没有非主字符，第一行的上界仍成立。

CRT 将 Gauss 乘子分解成这些局部因子；其加性参数的 CRT 单位
缩放不会改变零/非零分类。即使 \(f_q\) 不可按 CRT 分离，(F5)
的**算子乘子**仍可分解，所以不需要对 \(f_q\) 作任何分离。
设 \(d=(g,j,k)\)，因 \((q,g)=1\)，恰好在 \(\ell\mid d\)
出现最后一行。因此
\[
 \max_\chi\frac{|\tau_J(\bar\chi)\tau_K(\bar\chi)|}g\le d,
 \qquad
 \boxed{\sum_{n\in U(g)}|L_q(n)|^2
      \le d^2\sum_t|f_q(t)|^2\le g d^2.}
\tag{F6}
\]
这里用的是有限群 Parseval，不需要 Deligne 点值界、素数等分布
或任何关于 Möbius 的未证消去。

**为什么必须保留 \(d\)。** 当 \(g=\ell\)、\(J=K=0\) 时，
\[
 L_q(n)=\frac{\ell-1}{\ell}\sum_{t\in U(\ell)}f_q(t),
\tag{F7}
\]
与 \(n\) 无关。若 \(f_q=1\)，其平方范数为
\((\ell-1)^5/\ell^2\asymp\ell^3\)，绝不是 \(O(\ell)\)。
对真实 \(f_q(t)=e_\ell(A/t+Bt)\)，(F7) 是一个 Kloosterman
和；当 \(B=0,A\ne0\) 时恢复上篇的显式常数，一般 \(B\) 则保留
这个和。非零 \(B\) 也可能偶然取相同值，不能据此排除该参数。
本篇不假装这些模式消失，也不把它们逐项归入 residual main term。

## 3. 固定模式的素模平均，保留零剩余类

active 核不变，令 \(j'=j\bar g_q,k'=k\bar g_q\)，
\[
 p_q(z)=\frac{S(j',k'z;q)-1/(q-1)}{\sqrt q}\quad(z\in U(q)),
 \qquad U_q(c)=\sum_n a_nL_q(n)p_q(cn).
\tag{F8}
\]
当 \(q\mid jk\) 时，应使用原中心化有限核；它精确为零。
(F8) 的 Kloosterman 简式只用于 \(q\nmid jk\)，在非单位
\(z\) 处零延拓。特别是 \(j=0\) 或 \(k=0\) 的整条模式轴为零。

对其余 \(q\)，上篇 (A7) 给
\[
 \sum_c|U_q(c)|^2=\frac q{q-1}\sum_{\chi\ne\chi_0\ (q)}
          \left|\sum_n a_nL_q(n)\chi(n)\right|^2.
\tag{F9}
\]
先按 \(r\in U(g)\) 合并，使用 (F6) 的 Cauchy，得到
\[
 \left|\sum_n a_nL_q(n)\chi(n)\right|^2
 \le g d^2\sum_{r\in U(g)}
       \left|\sum_{n\equiv r\ (g)}a_n\chi(n)\right|^2.
\tag{F10}
\]
此时任意 \(q\)-dependent 比例函数已经用一致范数支付，余下
序列才是真正共同的序列。对每个 \(r\)，Gauss/Bessel 给
\[
 \frac q{q-1}\sum_{\chi\ne\chi_0}
  \left|\sum_{n\equiv r\ (g)}a_n\chi(n)\right|^2
 \le\sum_{v\in U(q)}
  \left|\sum_{n\equiv r\ (g)}a_ne_q(vn)\right|^2.
\tag{F11}
\]
加性侧须保留 \(q\mid n\) 的项，不可偷偷换成依赖 \(q\) 的
masked sequence。参见上篇 (A8) 的精确非负差项。

置 \(n=r+gm\)，在长至多 \(\lceil N/g\rceil\) 的 \(m\) 区间
上，对所有 \(v/q\) 应用 [加性大筛，Harcos Theorem 1](https://www.renyi.hu/~gharcos/large_sieve.pdf)。
\(v\mapsto gv\pmod q\) 是置换；不同素数给出的约分分数相距
至少 \(1/(4R^2)\)。乘回 \(gd^2\) 并对 \(r\) 求和得
\[
 \boxed{\sum_{q,c}|U_q(c)|^2
     \ll d^2(N+gR^2)\sum_n|a_n|^2.}
\tag{F12}
\]
整数舍入项 \(g\) 被 \(gR^2\) 吸收，没有额外 \(gN\)。
同一结论适用于任意共同子区间；dyadic 前缀分解及 Abel 求和
遂给出上篇 (A11) 的最大部分和/BV 版本，只增加
\(\log^2(2N)\) 和一致 BV 范数的平方。

## 4. 两条非零 Poisson 模式支付 \(d\)

两次 Poisson 的准确前因子仍为
\[
 V_q^f(c)=\frac{HL}{gq^{3/2}}\sum_{j,k\ne0}\sum_n
 a_nL_q(n)p_q(cn)
 \widehat F_{q,12}(jH/(gq),kL/(gq),n/N).
\tag{F13}
\]
每项的 \(n\)-BV 范数有衰减
\((1+|j|/a)^{-J}(1+|k|/b)^{-J}\)，其中
\(a=gR/H,b=gR/L\)，固定 \(J>1\)（例如 \(J=3\)）。
对任意 \(a>0,d\ge1\)，单调积分给
\[
 \sum_{j\ne0,\ d\mid j}(1+|j|/a)^{-J}
 \le\frac{2a}{d(J-1)}.
\tag{F14}
\]
尤其没有 \(+1\)：零模式已经由 active 中心化精确删除。
用整数恒等式 \((g,j,k)=\sum_{d\mid(g,j,k)}\varphi(d)\)，
全部双模式有绝对收敛的界
\[
 \begin{split}
 &\sum_{j,k\ne0}(g,j,k)(1+|j|/a)^{-J}(1+|k|/b)^{-J}\\
 &\hspace{15mm}\le\frac{4ab}{(J-1)^2}
      \sum_{d\mid g}\frac{\varphi(d)}{d^2}
  =\frac{4ab}{(J-1)^2}\mathfrak C(g).
 \end{split}
\tag{F15}
\]
在 \((q,c)\) Hilbert 范数中作 Minkowski，(F12) 的平方根只带
一个 \(d\)。将 (F15) 与 (F13) 的前因子相乘为
\(\ll g\sqrt R\,\mathfrak C(g)\)，再平方即得 (F3)。
这是一条完整求和不等式，不是先选“典型模式”再忽略退化层。

## 5. 所有共同频率及原双素数和

真实共同相位是
\[
 f_{q,\nu}(t)=e_g(A_q\bar t+B_{q,\nu}t),
 \qquad A_q=-C_q\bar q_g,\quad B_{q,\nu}=\nu\bar q_g.
\tag{F16}
\]
它对每个 \(\nu\bmod g\) 均满足 (F1)，包括非单位 \(\nu\)。
无需分离两项，也无需删去任何频率。原 incidence 的 \(m+xn=0\)
与 (F1) 的符号差，可由 \(c=-x\) 的行标签置换准确实现。

取 \(P>2R\)，两侧各为 (F1) 型 profile，系数序列 \(a,b\)
分别共同，平滑半范数一致，并且每侧只依赖本侧素模、共同频率
及预先固定的共同标签。为明确恢复原 \(m+xn=0\) 的行标签，定义
\(A_p^{(\nu)}(x)=V_{p,\nu}^{f,\mathrm{left}}(-x)\)、
\(B_q^{(\nu)}(x)=V_{q,\nu}^{f,\mathrm{right}}(-x)\)。
也可随后对每行作任意 active 字符正交投影。
定义 \(|\omega_{p,q,\nu}|\le1\) 的全共同频率双素数和
\[
 \mathcal S_{\rm all}=\frac1g\sum_{\nu\bmod g}\sum_{p,q}
  \omega_{p,q,\nu}A_p^{(\nu)}(D\bar q_p)
                  \overline{B_q^{(\nu)}(-D\bar p_q)},
 \qquad (pq,gD)=1.
\tag{F17}
\]
物理外相位 \(e_g(\nu D/(pq))\) 可包含在 \(\omega\) 内；若原
坐标含固定单位因子，也按其真实值保留在这里。对每个 \(\nu\)
分别用上篇 (A16) 的注入/占据界，再用 (F3)，得到
\[
 \boxed{|\mathcal S_{\rm all}|
 \ll_{\varepsilon,F_1,F_2}(gPRN_1N_2)^\varepsilon g^2
 \sqrt{PR(1+P/R)(N_1+gP^2)(N_2+gR^2)}\,
       \|a\|_2\|b\|_2.}
\tag{F18}
\]
最后只是 \(g^{-1}\sum_\nu 1=1\)，并未声称频率之间有新消去。
若系数也随 \(\nu\) 变化，则每个 \(\nu\) 内仍须对本侧素模
共同，(F18) 的最后范数积替换为
\(g^{-1}\sum_\nu\|a^{(\nu)}\|_2\|b^{(\nu)}\|_2\)；统一上界
或 Cauchy 的频率均方界均可使用，不能隐去这个成本。

在明确的极端模型 \(g=T,P=T^2,R=T^{3/2},N_i=T^3\)、
\(\|a\|_2^2,\|b\|_2^2\ll T^{3+\varepsilon}\) 上，(F18) 给
\(T^{23/2+\varepsilon}\)。这是上篇零频预算向**全部共同频率**
的延伸，不是再多出一次 \(T^{1/4}\) saving。

## 6. 已移除和仍未移除的障碍

已移除的是共同相位的特殊形状及 \(\nu=0\) 限制。实际上任何
模 \(g\) 的有界 ratio multiplier 都可以保留在物理核中。
本篇允许其任意随本侧素模和共同频率变化，不要求独立相位平均。

仍未移除：任意 \(a_{q,n}\)、随对侧素数变化的行、复合 active
modulus 的 imprimitive 字符、以及真实物理包的所有系数范数与
外层归一化比较。固定平方自由共同模数也不能直接推广到素幂。
因此还不能把 (F18) 当作原 \(\mathscr B_{\rm MC}\) 的相对幂次
saving，更不能由它宣布 \(14/17\) 或 \(2/3\) 的闭合。

这条路线并未“离开”用户提出的 pre-Cauchy 双素数平均：它证明
整个行族的算术平均之后，才对原交叉剩余类使用一次 pair-Cauchy。
但它没有发现一个可以单独提出的 residual main term；两条频率
轴的精确消失是 active 中心化的既有事实，不是本篇新删掉的主项。

## 7. 验证与独立审计

新增 `scripts/check_all_common_frequencies_prime_average.py` 的 20 项
检查通过，且由独立审阅者重跑通过。覆盖非 CRT 可分输入的精确
Mellin 恒等式、素模 Gauss 范数、全退化反例、非单位零延拓、
双 Poisson 的字面 CRT 恒等式、全共频相位、除数模式密度以及
前因子与极端指数。小模有限范数仅作 sanity check；一般解析
结论由上述证明承担，不由测试外推。

本轮重跑此前 11 个相关脚本的 211 项、新增 20 项及既有覆盖
检查 10 项，共 241 项通过。独立数学审计复核了 (F3)–(F18)，
并据反馈澄清了行标签的负号置换与局部常数的偶然重合。
没有修改或运行 Lean，没有运行全仓 baseline，也没有改动其他
研究 worktree。此验证不代表完整物理包或零点排除的验证。

## English summary

For squarefree common modulus g, replace the common phase by an arbitrary
bounded function of h delta / n modulo g. Its product-Poisson kernel has
multiplicative Fourier operator norm at most gcd(g,j,k). A large sieve on
progressions of length N/g gives fixed-mode energy bounded by gcd(g,j,k)^2
times (N+gR²). The two nonzero Poisson modes have sufficient divisor density
to absorb this loss, up to the explicit factor product(1+1/ell-1/ell²).
The previous g²R(N+gR²) profile energy bound therefore holds uniformly for
all common Fourier frequencies, even for non-CRT-factorable ratio functions.
The normalized common-frequency sum of the original prime-pair expression
has the same absolute bound, T^(23/2+epsilon) in the stated extreme model.
No extra cancellation between common frequencies, general physical norm
comparison, composite active-conductor bound, or zero-free theorem is claimed.
