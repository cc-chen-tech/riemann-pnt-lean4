# 真实共同频率 Parseval：省回一个 g，并接入复合导子与诱导层

白话结论：上一轮对每个共同频率分别给一致上界，仍浪费了真实
Fourier 族的结构。把共同频率平方平均保留到有限核内部后，行族
能量减少一个 \(g\)，双侧配对也减少一个 \(g\)。这个因子足以
支付一个未加权 dyadic \(g\) 区间的整数计数成本。同时，active
导子可以是复合数；诱导余因子的单位掩码和逆 totient 权也能明确
保留。本轮没有把注册能量的上界当作下界。

**范围。** 证明仍要求每个固定外标签内有共同的内部系数，以及
一致的光滑/BV 成本。下面给出的 \(T^{12}\) 覆盖是指定规范化模型
的绝对上界，不是完整物理包、NPIT、\(14/17\) 或 \(2/3\) 的证明。
尚未核实的 AFE/reflection 权、真正 gcd 行数及其他外标量不能免费
放入这个结论。全局零点目标仍开放。

## 1. 本次使用的真实频率族

固定平方自由 \(g>1\)，让 active 导子 \(c\) 取 \((R,2R]\)、
\((c,g)=1\) 中任意整数子集，\(R\ge2\)。不要求 \(c\) 是素数，
甚至不要求 \(c\) 平方自由。令 \(\mathcal X_c\) 是模 \(c\) 的
任意本原字符子集，\(P_{\mathcal X_c}\) 为单位行上的正交投影。
主导子 \(c=1\) 不在此定理内。

\(a_n\) 支撑 \(N<n\le2N\)，在本侧所有 \(c,\nu\) 中共同。
允许它随先前固定的 \(g,k\) 等标签变化。光滑核
\(F_{c,\nu}(h/H,\delta/L,n/N)\) 满足
[上篇](2026-08-30-all-common-frequencies-prime-average.md) (F1) 的
共同紧支撑和一致混合导数条件；可随 \(c,\nu\) 变化。
取任意 \(f_c:U(g)\to\mathbb C\)、\(|f_c|\le1\)，以及
\(u_c\in U(g)\)，两者均不随 \(\nu\) 改变。定义
\[
 V_c^{(\nu)}(x)=\sum_{h,\delta,n}a_n{\bf1}_{(h\delta n,gc)=1}
 F_{c,\nu}(h/H,\delta/L,n/N)
 f_c(h\delta/n)e_g(\nu u_ch\delta/n)
 {\bf1}_{h\delta\equiv xn\ (c)},\quad
 W_c^{(\nu)}=P_{\mathcal X_c}V_c^{(\nu)}.
\tag{C1}
\]
逆元均在对应单位群中。可在 incidence 中减去 \(1/\varphi(c)\)，
因为本原投影已删除常数。真实共同相位正是
\(f_c(t)=e_g(A_c/t)\)、\(u_c=\overline{ck}_g\) 的特例。

令 \(\mathfrak C(g)=\prod_{\ell\mid g}(1+\ell^{-1}-\ell^{-2})\)。
本轮主要行估计为
\[
 \boxed{\frac1g\sum_{\nu\bmod g}\sum_c\|W_c^{(\nu)}\|_2^2
 \ll_F\mathfrak C(g)^2\log^2(2N)\,
       gR(N+gR^2)\sum_n|a_n|^2.}
\tag{C2}
\]
与上篇逐频一致界相比，右端是 \(gR\)，不是 \(g^2R\)。
不允许把任意 \(a_{c,\nu,n}\) 宣称为这里的共同系数。

## 2. 在共同频率内部做 Parseval，准确省一个 g

固定非零整数 Poisson 模式 \(j,k\)，令
\(J=j\bar c_g,K=k\bar c_g,d=(g,j,k)\)。共同有限核为
\[
 L_{c,\nu}(n)=\frac1g\sum_{a,b\in U(g)}
 f_c(ab/n)e_g(\nu u_cab/n+Ja+Kb).
\tag{C3}
\]
在非单位 \(n\) 处零延拓。置 \(t=ab/n\)，准确得到
\[
 L_{c,\nu}(n)=\frac1g\sum_{t\in U(g)}
 f_c(t)e_g(\nu u_ct)S(J,Knt;g).
\tag{C4}
\]
因此对任意单位群向量 \(b_r\)，加性正交性给出
\[
 \boxed{\frac1g\sum_\nu\left|\sum_r b_rL_{c,\nu}(r)\right|^2
 =\frac1{g^2}\sum_{t\in U(g)}|f_c(t)|^2
       \left|\sum_r b_rS(J,Krt;g)\right|^2
 \le d^2\sum_r|b_r|^2.}
\tag{C5}
\]
等式中的 \(g^{-2}\) 不能丢失：原核有 \(g^{-1}\)，平方后仍有
\(g^{-2}\)；外面的 \(g^{-1}\sum_\nu\) 给 Kronecker delta。
\(u_c\) 是单位，故 \(\nu\mapsto\nu u_c\) 是置换。

末个不等式的证明：矩阵 \(S(J,Krt;g)\) 在乘性 Fourier 基下，
除下标取逆外，乘子是
\(\tau_J(\bar\chi)\tau_K(\bar\chi)\)。上篇 (F5)–(F6) 的局部
Gauss 表给其模长至多 \(gd\)。于是其平方算子范数至多
\(g^2d^2\)，恰好抵消 (C5) 的 \(g^{-2}\)。没有隐藏
\(\varphi(g)\) 因子，也不要求 \(f_c\) 是 CRT 乘积。

这与逐个 \(\nu\) 作 Cauchy 的区别是：后者只给
\(gd^2\sum_r|b_r|^2\)，而 (C5) 是 \(d^2\sum_r|b_r|^2\)。
两者不能叠乘；本篇直接替换那一步。

## 3. 复合 active 导子的本原投影与大筛

本原字符的 Gauss 恒等式对所有整数加性参数成立：
\[
 \tau_j(\chi)=\bar\chi(j)\tau_1(\chi),\qquad
 |\tau_1(\chi)|^2=c.
\tag{C6}
\]
特别是 \((j,c)>1\) 时左侧为零；参见
[DLMF 27.10.10–11](https://dlmf.nist.gov/27.10)。这一步不要求
素模；若不先投影本原字符，则这种非单位消失一般不成立。

设 \(j'=j\bar g_c,k'=k\bar g_c\)，定义零延拓核
\[
 p_c(z)=c^{-1/2}P_{\mathcal X_c}[S(j',k'z;c)],\qquad
 U_{c,\nu}(x)=\sum_n a_nL_{c,\nu}(n)p_c(xn).
\tag{C7}
\]
它的乘性 Fourier 系数在 \(\chi\in\mathcal X_c\) 上为
\(\tau_{j'}(\bar\chi)\tau_{k'}(\bar\chi)/\sqrt c\)，其他处为零。
当 \((jk,c)=1\) 时，这些系数模长均为 \(\sqrt c\)，所以
\[
 \|U_{c,\nu}\|_2^2
 =\frac c{\varphi(c)}\sum_{\chi\in\mathcal X_c}
       \left|\sum_n a_nL_{c,\nu}(n)\chi(n)\right|^2.
\tag{C8}
\]
当 \((jk,c)>1\) 时整个核为零，包含 \(j=0\) 或 \(k=0\) 的轴。

在 (C8) 中先按 \(r\in U(g)\) 合并，再用 (C5)；随后使用
本原 Gauss/Bessel 不等式
\[
 \frac c{\varphi(c)}\sum_{\chi\in\mathcal X_c}
       \left|\sum_n b_n\chi(n)\right|^2
 \le\sum_{v\in U(c)}\left|\sum_n b_ne_c(vn)\right|^2.
\tag{C9}
\]
这里 \(b_n\) 不必在非单位 \(n\) 处消失；加性侧保留这些项。
证明是用 (C6) 展开每个字符后，对单位群的字符系数用 Bessel。

对每个 \(r\) 置 \(n=r+gm\)，长度为 \(O(N/g+1)\)。所有
不同整数导子 \(c\) 的约分分数 \(v/c\) 两两不同，间距至少
\(1/(4R^2)\)。由 [加性大筛，Harcos Theorem 1](https://www.renyi.hu/~gharcos/large_sieve.pdf)，
\[
 \boxed{\frac1g\sum_\nu\sum_c\|U_{c,\nu}\|_2^2
 \ll d^2(N/g+R^2)\sum_n|a_n|^2.}
\tag{C10}
\]
\(+1\) 由 \(R^2\) 吸收。将 \(\nu\) 也纳入 Hilbert 坐标，
dyadic 最大部分和及 Abel 求和仍只增加 \(\log^2(2N)\) 和统一
BV 半范数；因此可接受 (C1) 的 \(F_{c,\nu}\)。

两次 Poisson 的前因子仍是 \(HL/(gc^{3/2})\)。Minkowski 后，
全部非零双模式的 \(d\)-加权和仍由上篇 (F15) 控制：
\[
 \sum_{j,k\ne0}(g,j,k)
 (1+|j|H/(gR))^{-J}(1+|k|L/(gR))^{-J}
 \ll_J\frac{g^2R^2}{HL}\mathfrak C(g).
\tag{C11}
\]
前因子乘模式和的平方是 \(g^2R\mathfrak C(g)^2\)。乘上
(C10) 的 \(N/g+R^2\)，得到 (C2)。未删去任何退化模式。

## 4. 诱导层：点值和行范数的 totient 因子不同

令 \(r=ck\)，\((c,k)=(g,ck)=1\)，\(k\) 平方自由。考虑同一个
有限物理三元组和，其权重包含 \({\bf1}_{(h\delta n,gck)=1}\)、
共同相位及完整平滑核。记 \(Z_r(y)\) 使用原 incidence
\(h\delta+yn=0\pmod r\)；\(V_{c,k}(x)\) 使用
\(h\delta+xn=0\pmod c\)，但**仍保留 k 单位掩码**。

把模 \(r\) 的行投影到恰由 \(\mathcal X_c\) 诱导的字符层。
字符变换逐项相同，逆变换的分母不同，因此准确有
\[
 Z_r^{[c]}(y)=\frac1{\varphi(k)}
      (P_{\mathcal X_c}V_{c,k})(y\bmod c),\qquad
 \boxed{\|Z_r^{[c]}\|_{\ell^2(U(r))}^2
       =\frac1{\varphi(k)}
        \|P_{\mathcal X_c}V_{c,k}\|_{\ell^2(U(c))}^2.}
\tag{C12}
\]
点值是 \(\varphi(k)^{-1}\)，不是免费取消；平方范数也只有
\(\varphi(k)^{-1}\)，不是 \(\varphi(k)^{-2}\)，因为每个模 \(c\)
单位类有 \(\varphi(k)\) 个 lift。

固定 \(k\)。将 \({\bf1}_{(n,k)=1}\) 并入同一 \(a_n\)，并在
\(h,\delta\) 两个方向各作一次有限容斥。对
\(d_h,d_\delta\mid k\)，置 \(h=d_hh',\delta=d_\delta\delta'\)。
\(d_hd_\delta\) 在模 \(gc\) 上为单位：比例函数重标定为
\(f_c(d_hd_\delta t)\)，\(u_c\) 变为 \(u_cd_hd_\delta\)，行标签
也作相同单位置换。\(H,L\) 相应缩放，光滑半范数不变。于是
(C2) 的平方根至多多付 \(\tau(k)^2\)，能量至多多付
\(\tau(k)^4\)。没有将依赖 \(c\) 的掩码塞进共同系数。

对**直接点值配对**，(C12) 的权为 \(1/\varphi(k)\)。若同一
dyadic 导子区间内系数平方范数一致可控，则
\[
 \sum_{k\le K}^{\rm squarefree}\frac{\tau(k)^2}{\varphi(k)}
 \ll_\varepsilon K^\varepsilon.
\tag{C13}
\]
这是初等除数界：\(\tau(k)^2k/\varphi(k)\ll_\varepsilon
k^{\varepsilon/2}\)，再求 \(k^{-1+\varepsilon/2}\)。若系数随
\(k\) 变化，则必须保留 \(\sum_k\tau(k)^2\|a^{(k)}\|_2/\varphi(k)\)
的实际值。若回到原 \(U(ck)\) Hilbert 空间，不得把 (C13) 当作
范数权：那里的点态范数缩放是 \(\varphi(k)^{-1/2}\)。

## 5. 直接配对、g 求和以及一个明确的尺度覆盖

固定 \((g,k_1,k_2,D)\)，让 \(c_1\asymp P,c_2\asymp R\)，
\(P\ge R\ge2\)，明确保留 \((c_i,k_i)=1\)、
\((g,c_1c_2k_1k_2)=1\)、\((c_1k_1,c_2k_2)=1\) 以及
\((D,c_1c_2)=1\)。最后一个条件不仅是模逆条件：它保证采样仍在
单位行上，乘 D 是置换。若 D 与某 active 导子不互素，原单位
incidence 在该非单位标签处为零，可零延拓删除该项。
把 (C1) 行标签改为 \(x\mapsto-x\)，
得到原 \(h\delta+xn=0\) 的行 \(A_{c_1}^{(\nu)},B_{c_2}^{(\nu)}\)。
对任意 \(|\omega_{c_1,c_2,\nu}|\le1\)，考虑
\[
 \frac1g\sum_\nu\sum_{c_1,c_2}\omega_{c_1,c_2,\nu}
 A_{c_1}^{(\nu)}(D\overline{c_2k_2}_{c_1})
 \overline{B_{c_2}^{(\nu)}(-D\overline{c_1k_1}_{c_2})}.
\tag{C14}
\]
每侧只依赖本侧导子及固定标签；不能依赖对侧导子。固定长模数
时短标签的占据至多 \(1+R/P\)，反向至多 \(1+P/R\)。这对复合
模数同样成立，所需只是互素类上的逆元置换和整数计数。

先作 pair-Cauchy，再对共同频率作带 \(1/g\) 的 Cauchy，插入
(C2)。因为 \(PR(1+R/P)(1+P/R)=(P+R)^2\)，无额外 k 掩码时
\[
 \boxed{|(C14)|\ll_\varepsilon(gPRN_1N_2)^\varepsilon
   g(P+R)\sqrt{(N_1+gP^2)(N_2+gR^2)}\,
       \|a\|_2\|b\|_2.}
\tag{C15}
\]
隐常数包含两侧统一半范数。加入 k 掩码后乘
\(\tau(k_1)^2\tau(k_2)^2\)；重装配 (C12) 的直接点值权，再用
(C13)，只增加已声明的亚幂次及实际系数范数成本。若原 \(r_i\)
区间固定，须按 \(c_i=r_i/k_i\) 的真实 dyadic 尺度使用 (C15)，
不可令所有 k 层免费共用未缩放的导子区间。

再令 \(g\asymp G\)。若外权模长至多 1，最多有 \(O(G)\) 个 g，
直接三角要再乘 \(G\)，不能忽略。一般外权则保留其实际
\(\ell^1\) 和。极端尺度 \(g\asymp T,P=T^2,R=T^{3/2},N_i=T^3\)、
\(\|a\|_2^2,\|b\|_2^2\ll T^{3+\varepsilon}\) 给
\[
 \begin{array}{c|c}
 \text{固定 g 的两侧平均行能量}&T^{11+\varepsilon},\ T^{19/2+\varepsilon}\\
 \text{固定 g 的全共频配对}&T^{21/2+\varepsilon}\\
 \text{再对 g\asymp T 作单位权求和}&T^{23/2+\varepsilon}.
 \end{array}
\tag{C16}
\]
没有把上一轮的均匀 \(\nu\) 上界再次乘进来。

更一般，在明确的最大 ambient 模型
\[
 N_i=T^3,\quad g=T^\gamma,\quad
 \sigma_i=3-\delta_i-\gamma-\kappa_i,\quad
 0\le\gamma\le1,\quad0\le\delta_i\le\tfrac12,\quad\kappa_i\ge0,
 \quad\sigma_i>\tfrac23(3-\delta_i-\gamma),
\tag{C17}
\]
并假设共同系数平方范数 \(\ll T^{3+\varepsilon}\)，有
\(\gamma+2\sigma_i>3\)。故 (C2) 每侧指数为
\(12-\gamma-3\delta_i-3\kappa_i\)。按
\(\sigma_L\ge\sigma_S\) 定向，(C15) 再支付 g 区间的 \(T^\gamma\)
后，绝对指数是
\[
 \boxed{12-2\delta_L-\delta_S-2\kappa_L-\kappa_S\le12.}
\tag{C18}
\]
这里的 k 层用原 \(1/\varphi(k)\) 求和，使用 (C13)，不是再按
\(T^{\kappa_i}\) 整数数目付一次代价。这证明了此**明确模型**的
near-primitive 尺度覆盖，不需要把旧 \(\mathscr B_{\rm MC}\) 当作
下界。它不证明一般物理权的相对 NPIT。

## 6. 剩余的实际对接义务

本轮已接入复合本原 active 导子，以及给定 \((c,k)=1\) 下的
诱导字符点值/能量归一化和 k 单位掩码。原始平方自由 active
模数的这种分层在本结论内；共同模数 g 的素幂仍未处理。

但原材料的真正 gcd 因子 \(d=(|h\delta|,v)\) 不等于诱导余因子 k。
它没有 (C13) 的逆 totient 权。若这类 gcd 原子有 \(T^\eta\) 个，
按原 §9.144 粗略 Minkowski 重装配可能花 \(T^{2\eta}\) 行能量。
Type-frequency gcd 又是第三种标签；它不
缩短原 \(h\delta\) 支撑。本篇没有把这三者混淆或删除。

尤其还要证明：所有待估 AFE/reflection 原子均有 (C1) 的共同系数
与统一半范数；随两侧导子变化的权能以登记成本处理；g、D、真正
gcd 和全部外标量的总范数满足 (C18) 所用预算。若任一项产生额外
幂次，必须重新计入。原 active 主字符 \(c=1\) 也仍是独立项。
因此本篇不宣布整个 coupled-kernel gate 或零点目标完成。

## 7. 验证记录

新增 `scripts/check_common_frequency_parseval_conductor_average.py` 的
20 项检查通过，并经独立审阅者重跑。覆盖复合/素幂模数的本原
字符、非单位 Gauss 消失、精确共同频率 Parseval、诱导字符变换
与原单位行能量、掩码反例、除数权、双向占据以及全部指数公式。
有限范数的浮点检查仅作 sanity check，不替代上述解析证明。

本轮重跑此前 12 个相关脚本的 231 项、新增 20 项及既有覆盖
检查 10 项，合计 261 项通过。独立数学审计确认共同频率中省去
一个 g、复合导子大筛及 (C12)–(C18) 的归一化，并补明了 D 的
单位条件。没有修改或运行 Lean，没有运行全仓 baseline，没有
改动其他研究 worktree；这不是完整零点目标的验证。

## English summary

The actual common-frequency family has the form f_c(t)e_g(nu u_c t).
Parseval in nu reduces the common-kernel energy cost from g d² to d²,
where d=gcd(g,j,k). After the progression large sieve and both nonzero
Poisson-mode sums, the averaged row energy is gR(N+gR²), rather than
g²R(N+gR²), times the common coefficient square norm. Primitive projection
extends this result to composite active conductors. An induced c-layer in
modulus ck has pointwise factor 1/phi(k), but original-unit-row energy
factor 1/phi(k), not 1/phi(k)². The k unit masks are retained with explicit
divisor costs. The direct all-frequency pair bound gains one g; paying a
whole dyadic g range still gives exponent 23/2 in the specified extreme
model and at most 12 on its near-primitive polytope. Full physical weights,
genuine gcd rows, the principal sector and zero-free conclusions remain
outside this result until their actual budgets are proved.
