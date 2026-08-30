# 全共同模数与本原导子联合平均：减少混合区的长度项成本

白话结论：上一轮先固定共同模数 g，再按整数个数收费；这在长
内部系数序列控制大筛时仍有浪费。若内部系数在全部 g 中共同，
可以将 g 和剩余本原导子一起筛。新界只减少长度项，不对同一个
导子项重复计入节省。上一轮模型中 12.9 的上界账本降为 12.4，仍没有
达到 12，也没有证明任何新的零点自由半平面。

**新假设不能省略。** 本篇要求跨 g、c、ν 的共同内部系数，以及
共同归一化光滑分离成本。[前篇 (C1)](2026-08-30-common-frequency-parseval-conductor-average.md)
只要求固定 g 后系数共同，因此本结果不能无条件替换其全部应用。
真正 gcd、外权、Type-frequency 周期因子及主字符仍须分别处理。

交付边界与上游分工见[物理原子交接清单](2026-08-30-pr503-scope-and-physical-handoff.md)。
未完成该清单的物理映射前，G15–G16 的模型见证不代表原式的真实障碍。

## 1. 行族与要证明的联合估计

取 \(G\ge1,R\ge2,N\ge1\)，平方自由
\(g\in(G,2G]\)、\(g>1\)，整数 \(c\in(R,2R]\)、\((g,c)=1\)。
每个 c 的任意本原字符子集记为 \(\mathcal X_c\)，其单位行投影
为 \(P_c\)。可以取任意允许的 (g,c) 子族；主导子 c=1 不在内。

\(a_n\) 支撑于 \(N<n\le2N\)，在全部 g、c、ν 中共同。
对固定 \(H,L>0\)，设 \(F_{g,c,\nu}(h/H,\delta/L,n/N)\)
有共同紧支撑及一致的所有固定阶混合导数。第一、二坐标支撑
离开零。允许核依赖 g、c、ν；允许 \(a_n\) 随另外固定的标签变化。
\(f_{g,c}:U(g)\to\mathbb C\)、\(|f_{g,c}|\le1\)，以及
\(u_{g,c}\in U(g)\) 均不随 ν 改变。使用原 C1 行：
\[
 V_{g,c}^{(\nu)}(x)=\sum_{h,\delta,n}a_n
 {\bf1}_{(h\delta n,gc)=1}F_{g,c,\nu}(h/H,\delta/L,n/N)
 f_{g,c}(h\delta/n)e_g(\nu u_{g,c}h\delta/n)
 {\bf1}_{h\delta\equiv xn\ (c)},\qquad W_{g,c}^{(\nu)}=P_cV_{g,c}^{(\nu)}.
\tag{G1}
\]
所有比例在对应单位群中求值。令 \(Q_*=4GR\)。本篇结论是，
对任意固定 \(M\ge0,\epsilon>0\)，
\[
 \boxed{
 \sum_g{1\over g}\sum_{\nu\bmod g}\sum_c\|W_{g,c}^{(\nu)}\|_2^2
 \ll_{F,M,\epsilon}(GRN)^\epsilon GR\bigl(N+(GR)^2\bigr)\|a\|_2^2
 \min\!\left(1,({Q_*\over H})^{2M}\right)
 \min\!\left(1,({Q_*\over L})^{2M}\right).}
\tag{G2}
\]
当 M=0 时，与逐 g 使用 C2 再计数的
\(G^2R(N+GR^2)\|a\|_2^2\) 相比，\(G^2RN\) 变为 \(GRN\)，
而 \(G^3R^3\) 不变。这不是把两种估计的 saving 相乘。

## 2. 先分离物理光滑权，再作真实频率正交

在共同的归一化坐标上，用固定紧支撑 cutoff 乘 Fourier 基写
\[
 F_{g,c,\nu}(x,y,z)=\sum_{\mathbf m}\lambda_{g,c,\nu,\mathbf m}
       U_{m_1}(x)V_{m_2}(y)Z_{m_3}(z).
\tag{G3}
\]
对任何预定多项式导数权，一致足够高阶导数给
\(\sum_{\mathbf m}\sup_{g,c,\nu}|\lambda_{g,c,\nu,\mathbf m}|
(1+|\mathbf m|)^D<\infty\)。这里不是把任意依赖 ν 的算术系数
交给 Parseval。先在包含 (g,c,ν,x) 的加权 Hilbert 空间中用
Minkowski，每个原子的标量 λ 用其 sup 支付，然后才处理一个
与 ν 无关的分离原子。\(Z_{m_3}(n/N)\) 并入共同 \(a_n\)，
其平方范数一致可控。

固定一个这样的原子，定义完整 ratio 行
\[
 \mathcal R_{g,c}(t,x)=\sum_{h,\delta,n}a_n U(h/H)V(\delta/L)
 {\bf1}_{(h\delta n,gc)=1}
 {\bf1}_{h\delta\equiv tn\ (g)}{\bf1}_{h\delta\equiv xn\ (c)}.
\tag{G4}
\]
则准确有
\[
 {1\over g}\sum_\nu\|W_{g,c}^{(\nu)}\|_2^2
 =\sum_{t\in U(g)}|f_{g,c}(t)|^2\|P_c\mathcal R_{g,c}(t,\cdot)\|_2^2
 \le\sum_t\|P_c\mathcal R_{g,c}(t,\cdot)\|_2^2.
\tag{G5}
\]
理由是 \(u_{g,c}\) 为单位，ν 正交给 t 相等；\(P_c\) 只作用
x，故与只依赖 t 的相位交换。这个等式保留准确的 \(1/g\)，
没有把每个 ν 再收费。任意 \(f_{g,c}\) 无需在不同 g 间相同。

记 \(\psi=\chi_g\chi_c\)，作为模 gc 的零延拓字符。对 t、x
作乘性 Parseval，G5 的最右端等于
\[
 {1\over\varphi(g)\varphi(c)}
 \sum_{\chi_g\bmod g}\sum_{\chi_c\in\mathcal X_c}
 \left|\sum_h U(h/H)\overline{\psi(h)}\right|^2
 \left|\sum_\delta V(\delta/L)\overline{\psi(\delta)}\right|^2
 \left|\sum_n a_n\psi(n)\right|^2.
\tag{G6}
\]
这里投影到 χc(x) 的系数为 \(\sum_xR(x)\overline{\chi_c(x)}\)，
故 h、δ 两侧共轭而 n 侧不共轭。若改用相反约定，字符子集也
须同步取逆；任意 \(\mathcal X_c\) 不必对共轭封闭。

## 3. 下降共同字符的导子，并保留三个非本原掩码

令 \(r=\operatorname{cond}(\chi_g)\mid g\)、\(g=rb\)。
平方自由性给 \((r,b)=1\)，且 \((b,rc)=1\)。于是 ψ 由模
\(q'=rc>1\) 的本原字符 \(\psi^*\) 诱导；其三个因子均有
\({\bf1}_{(\cdot,b)=1}\)。\(r=1\) 允许，因为本原 active
\(c>1\) 已保证总本原字符非主。准确的分母是
\[
 \varphi(g)\varphi(c)=\varphi(b)\varphi(q').
\tag{G7}
\]

对光滑紧支撑 U、本原非主 χ 模 q'，由
[本原 Gauss 恒等式](https://dlmf.nist.gov/27.10)和一维 Poisson，
\[
 \left|\sum_hU(h/X)\chi(h)\right|
 \ll_{U,M}\sqrt{q'}\min(1,(q'/X)^M).
\tag{G8}
\]
证明：零频精确为零；非零模式的模长至多
\(X/\sqrt{q'}\sum_{j\ne0}|\widehat U(jX/q')|\)。完整模式和
用前篇 O7 的两种界即得 G8。没有硬端点产生的额外主项。

保留 b-unit 掩码并按 \(s\mid b\) 容斥，每项长度为 H/s。
因 \(q's\le q'b=gc\le4GR\)，所以
\[
 \left|\sum_h U(h/H)\psi^*(h){\bf1}_{(h,b)=1}\right|
 \ll_{U,M}\tau(b)\sqrt{q'}\min(1,(Q_*/H)^M).
\tag{G9}
\]
δ 方向同理。n 方向则保留共同系数
\(a_n^{(b)}=a_n{\bf1}_{(n,b)=1}\)，不删其掩码。
两个光滑因子的平方乘积给 \(\tau(b)^4q'^2\)，而 G6–G7 的
权准确重写为
\[
 {q'^2\over\varphi(b)\varphi(q')}
 ={q'\over\varphi(b)}{q'\over\varphi(q')}.
\tag{G10}
\]

固定 b 后，\(q'=rc\le4GR/b\)，同一 q' 的 (r,c) 表示不超过
\(\tau(q')\)。所有相应 \(\psi^*\) 是该 q' 的本原字符子集，
所以正能量可延拓为全部本原字符，再用
[Harcos, Theorem 2 的本原字符大筛](https://www.renyi.hu/~gharcos/large_sieve.pdf)：
\[
 \sum_{q'\le4GR/b}{q'\over\varphi(q')}
 \sum_{\psi^*\bmod q'}^{\rm primitive}
 \left|\sum_n a_n^{(b)}\psi^*(n)\right|^2
 \ll\bigl(N+(GR/b)^2\bigr)\|a\|_2^2.
\tag{G11}
\]
这一处必须有跨 r、c 共同的 \(a_n^{(b)}\)。一般
\(a_{g,c,n}\) 不满足此条件。表示次数只花 \((GR)^\epsilon\)。

将 G9 的两个 gain 抽出后，其余上界为
\[
 (GR)^\epsilon GR\|a\|_2^2
 \sum_b^{\rm squarefree}{\tau(b)^4\over b\varphi(b)}
       \bigl(N+(GR/b)^2\bigr).
\tag{G12}
\]
这里的权重级数 \(\sum_b\tau(b)^4/[b\varphi(b)]\) 绝对收敛，
其 Euler 因子为
\(1+16/[p(p-1)]\)。因此 G12 给出 G2。这个 b 来自共同字符
导子下降，**不是真正 gcd d，也不是此前的诱导余因子 k**。
其逆 totient 权不能拿去支付另外两种标签。

## 4. 与真正 gcd 和方向性删区的兼容条件

复用[交叠重组 O2–O5](2026-08-30-genuine-gcd-overlap-smooth-mode-removal.md)。
先固定 \(d=a_0b_0e\)、\(k\) 和两个 k-mask 除数；本文中
g=rb 的 b 不等于交叠分解中的 \(b_0\)。内部系数保留
\(a_n^0{\bf1}_{(n,dk)=1}\)，只要它在 g 变化时仍共同即可。
随后本篇下降增加的是 \((n,b)=1\)，同样保留。

两个实际长度 H*,L* 代入 G2；同一 dyadic g 区间使 4GR 与
原有效模数同阶。因此 O11–O13 的方向性删区和边界 collar 保持，
但不产生第二份独立 saving。外层 k 仍使用实际点值
\(1/\varphi(k)\) 权和原 C13；不同 k 的真实 active 区间不能混用。

来源 §9.144 的坐标分离在固定真正 gcd 和掩码标签后给
\(\mu(n)B_\omega(n){\bf1}_{\ell\mid n}\) 型共同系数，变化的
模数坐标另成标量。这类 core 与本篇共同性要求兼容。若实际
Type-frequency、reflection 或其他条件产生额外 g-dependent
算术因子，必须证明新的分离成本，不能称为已适配。

本轮另只读查看了来源 worktree 最新 `d9b63e61`：其全频率物理
adapter 与零差带求值仍保留长 Möbius Gram；前一个 `43d4062b`
全 B 重组则回到 quotient 边界，明确没有新幂次节省。两者没有
供应本篇未证的交叠上界，也不能与 G2 相乘作额外 saving。

## 5. 对全 g 配对只作一次 Cauchy

取两侧 \(c_1\asymp P,c_2\asymp R,P\ge R\)，共同
\(g\asymp G\)。保持 C14 的 D 单位条件、所有互素条件和
本侧只依赖本侧导子的限制。对全部 (g,ν) 一起作带 \(1/g\)
的 Cauchy，并保留双向占据 \((1+R/P)(1+P/R)\)，G2 给
\[
 \boxed{|\mathcal S_G|
 \ll_\epsilon (GPRN_1N_2)^\epsilon G(P+R)
 \sqrt{\bigl(N_1+(GP)^2\bigr)\bigl(N_2+(GR)^2\bigr)}
 \|a\|_2\|b\|_2.}
\tag{G13}
\]
两侧光滑半范数、固定掩码及方向性 gain 如前。此处已经对
全部 g 求和，不能再按 G 个整数收费。一般非有界外权须计入
其实际成本，不由此自动涵盖。

采用 O15 的同一规范化模型，\(N_i=T^3\)、
\(\|a_i\|_2^2\ll T^{3+\epsilon}\)，以及
\(\sigma_i=3-\eta_i-\delta_i-\gamma-\kappa_i\ge0\)。
现在每侧**全 g 能量**指数是
\[
 E'_i=\gamma+\sigma_i+\max(3,2\gamma+2\sigma_i)+3.
\tag{G14}
\]
按 \(\sigma_L\ge\sigma_S\) 定向，支付真正 d 的两侧计数后，
\[
 B'=\eta_L+\eta_S+\tfrac12(E'_L+E'_S+\sigma_L-\sigma_S).
\tag{G15}
\]
无额外 \(+\gamma\)。三种情况如下；它们的阈值与 O17 不同。

| 大筛控制项 | G15 的准确指数 |
|---|---|
| 两侧 \(2\gamma+2\sigma_i\ge3\) | \(12-\eta_L-2\delta_L-\delta_S-2\kappa_L-\kappa_S\le12\) |
| 两侧 \(2\gamma+2\sigma_i\le3\) | \(12-\gamma-\delta_L-\kappa_L-\delta_S-\kappa_S-\sigma_S\le12\) |
| 长侧 \(\ge3\)、短侧 \(\le3\) | \(21/2-\eta_L+\eta_S-2\delta_L-2\kappa_L\) |

混合区若仍超出 12，必有
\[
 \eta_S>3/2+\eta_L+2\delta_L+2\kappa_L.
\tag{G16}
\]
这把 O18 中的 \(-\gamma/2\) 去掉，但不保证剩余区域为空。
原 O19 见证 \(\gamma=1,\eta_L=0,\eta_S=19/10,
\delta_i=\kappa_i=0\) 的新能量为 \(E'_L=12,E'_S=71/10\)，
故 \(B'=62/5=12.4\)。其短侧 \(H_*=L_*=T^{3/5}\)、
\(Q_*\asymp T^{11/10}\)，仍无方向性快速衰减。
这是上界账本的改善，不是原和的渐近式或反例。

## 6. 为什么不能继续免费删除剩下的 N 项

对一般共同系数，N 项确实不可完全去掉。取单个
\(g=2,c=3\)，固定光滑权只选择 \(h=\delta=1\)，且
\(f=1,u=1\)。令 \(N=6m\)，在 \(N<n\le2N\) 上取
\(a_n=\chi_3(n){\bf1}_{n\ {\rm odd}}\)，其中 χ3 为模3的
非主实字符。于是 \(\|a\|_2^2=2m\)，两个单位类各有 m 项。
本原投影不改变该行，且
\[
 \boxed{{1\over2}\sum_{\nu\bmod2}\|W_{2,3}^{(\nu)}\|_2^2
       =2m^2.}
\tag{G17}
\]
固定模数下，删掉 N 项的通用界只有
\(O_\epsilon(N^\epsilon\|a\|_2^2)=O_\epsilon(m^{1+\epsilon})\)。
取任意固定 \(0<\epsilon<1\)，仍与 G17 矛盾。
此例的系数不是实际 Möbius 系数；它只阻止把
一般共同系数大筛自动加强为无需长度项的界，不排除利用真正
Möbius 符号、e 重装配或物理支持获得更强结果。

下一步仍是 G16 与原 O12 同时成立的大交叠混合区。还需证明
其原符号和相位下的联合估计，或用合法的外权/支持将其支付。
主字符、全部 AFE/reflection、Type 周期因子和最终零点排除
没有在本篇完成。没有写 Lean。

## 7. 验证记录

新增 `scripts/check_global_common_modulus_conductor.py` 的 17 项
检查通过，最终版本由独立审阅者重跑 17/17。包括准确 ν-Parseval、
完整 ratio 乘性 Parseval、非共轭封闭单字符的共轭方向反例、
共同字符导子下降、三个单位掩码、漏 n-mask 反例、totient 权、
表示重数、有限 Euler 乘积及新配对账本。固定字符族的 N 项
必要性是准确有限计算，不是实际 Möbius 家族的反例。

本轮重跑此前 14 个相关脚本的 271 项，新增 17 项及既有覆盖
检查 10 项，共 298 项通过。独立数学及文件审计核对了 G2 的
新增共同性、分离顺序、方向性 gain 与混合剩余区域。没有运行
Lean 或全仓 baseline；没有修改引用的来源 worktree。

## English summary

When the internal coefficients are common across g as well as c and nu,
averaging the actual nu-family first produces the full ratio-row energy.
Descending the common character conductor g=rb and retaining all b-unit
masks allows a single primitive-character large sieve in q'=rc. The
convergent weight sum over b yields GR(N+(GR)^2), replacing the former
G²R(N+GR²). Only the length term improves. Both directional smooth-mode
gains survive. The explicit genuine-gcd mixed budget falls from 12.9 to
12.4 but remains above 12. A fixed-character finite family shows that
the remaining N term is necessary for general common coefficients; this
is not a counterexample for the physical Mobius family. All unadapted
periodic factors, principal terms, full physical assembly and zero-free
conclusions remain open.
