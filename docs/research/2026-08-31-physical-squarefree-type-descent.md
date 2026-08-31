# 实际双整除 gcd 层：全部平方自由模数的 Type 下降

白话结论：前一篇指定 gp 子族的结账可以推广到同一 FP3 双整除
gcd 层的全部平方自由约化模数。先准确保留单位掩码，再将每个 Type
频率按真正的 gcd 分到唯一一层；下降带来的 1/d 外权可求和。
在同一内部例子中，整个所选 FP3 层由直接计数 T^(11/10) 降为
T^(33/40+ε)。这不是所有 genuine-gcd 分配，更不是全局零点界。

沿用[前篇](2026-08-31-physical-large-gcd-type-columns.md)的唯一冻结
上游 MWKF-PHYS-v1、内部核 Ψ、半范数 A_J 和物理外权；不改 #490/#503。
前篇的 gp / 1/p 论证仍独立成立；以下是更广的另一个上界，节省
不能与前篇相乘。这里只固定原平方自由 q₀，不加入 q₀ 壳扩展。

## 1. 对象：原 FP3 层，不引入 prime 标签

固定 E,Q≥1、EQ≈S，选择
\[
 E<e\le2E,\quad Q<q\le2Q,\quad e,q\text{ 平方自由},\quad
 (e,q)=(q_0,eq)=1,\quad q>1,
\]
\[
 s=eq,\quad r=n,\quad h=eu,\quad\delta=ev,\quad
 (n,q_0eq)=(uv,q)=1,\qquad u,v\ne0.                         \tag{D1}
\]
保留全部原支持与实权。真正 gcd 为 (hδ,s)=e，且 e 同时整除 h、δ；
反之，仅有 (hδ,s)=e 并不推出这两个整除条件。所估原式是
\[
 \mathcal O_{E,Q}={2T\over q_0RS}
 \sum_{(D1)}\mu(e)\mu(q)\mu(n)
 p_N(q_0n)p_N(q_0eq)\Psi(n/R,eq/S,ev/L,eu/H)
 e_q(-euv\bar n).                                         \tag{D2}
\]
各 e/q/n/u/v 元组由原行唯一恢复。不存在 p 最大素因子标签，不需
q=gp 或 p>g。D1 包含的是所有满足这个双整除筛选的原 FP3 行；
平方自由 q 的全部 Type 频率（以及 principal）都在下文付费。

## 2. 含真实单位掩码的 primitive 加性大筛

设 R≥1,Q≥1，aₙ 为支撑于 1≤n≤2R 的任意共同复系数。定义
\[
 U_q(k)=\sum_{(n,q)=1}a_ne_q(kn),\qquad
 \mathcal E=\sum_{Q<q\le2Q\atop q\ {\rm squarefree}}
                 \sum_{k\in U(q)}|U_q(k)|^2.
\]
对任意 ε>0，有
\[
 \boxed{\mathcal E\ll_\epsilon(RQ)^\epsilon
                   (R+Q^2)\sum_n|a_n|^2.}                    \tag{D3}
\]

证明不能直接删除 (n,q)=1。先准确容斥：
\[
 U_q(k)=\sum_{f\mid q}\mu(f)\sum_m a_{fm}e_{q/f}(km).
                                                               \tag{D4}
\]
Cauchy 只损失 τ(q)≪ε Q^ε。写 q=fℓ；因 q 平方自由，(f,ℓ)=1，
k∈U(fℓ) 降到 U(ℓ) 的每个值有准确 φ(f) 个 lift，至多 f 个。
于是
\[
 \mathcal E\ll_\epsilon Q^\epsilon
 \sum_{f\le2Q} f\sum_{Q/f<\ell\le2Q/f\atop (f,\ell)=1,
                   \ f\ell\ {\rm squarefree}}
 \sum_{t\in U(\ell)}\left|\sum_{m\le2R/f}a_{fm}e_\ell(tm)\right|^2.
                                                               \tag{D5}
\]
固定 f 后，primitive 分数 t/ℓ 在不同 ℓ 间不重复。圆周间距
至少 (2Q/f)^−2；ℓ=1 只有分数 0，其他分母没有 0。
由[加性大筛 Theorem 15.5](https://kskedlaya.org/ant/chap-largesieve.html)，
该 f 的费用至多
\[
 \ll f\left({R\over f}+{Q^2\over f^2}\right)
             \sum_m|a_{fm}|^2
 =\left(R+{Q^2\over f}\right)\sum_m|a_{fm}|^2.                 \tag{D6}
\]
若 2R/f<1 则子序列为空。若 Q/f<1，只可能有 ℓ=1，直接 Cauchy
也给 D6，避免对单点集合虚构间距。最后
\[
 \sum_{f\le2Q}\sum_m|a_{fm}|^2
 \le\sum_n\tau(n)|a_n|^2\ll_\epsilon R^\epsilon\sum_n|a_n|^2,
                                                               \tag{D7}
\]
即得 D3。上式可以删去任意模数子集；这是正能量的单调性，并非
对原有符号外层做无损删项。额外固定整数 b 的单位条件 (n,b)=1
可直接放入共同 aₙ，常数不依赖 b。

## 3. 全部非零 Type 频率的唯一下降

采用前篇的完整中心核
\[
 B_q(k,A)=S(k,-A;q)-{\mu(q)c_q(k)\over\varphi(q)},\qquad(A,q)=1.
\]
对 k mod q，令 d=(k,q)、q=dℓ、k=dt。因为 q 平方自由，
(d,ℓ)=1，t∈U(ℓ)。每个 (q,k) 有且仅有一个这样的 (d,ℓ,t)。
CRT 给出精确的中心核下降
\[
 B_{d\ell}(dt,A)=\mu(d)B_\ell(t,A\bar d).                    \tag{D8}
\]
这里右边的 \(\bar d\) 是模 ℓ 逆元，不能删去。证明为
\(S(dt,-A;d\ell)=\mu(d)S(t,-A\bar d;\ell)\) 以及
\(c_{d\ell}(dt)=\varphi(d)c_\ell(t)\)；整个 Ramanujan 修正随同下降。
ℓ=1 时中心核为零，恰好对应 k=0，不再付费或冒充 principal。

原 1/q 不变成 1/ℓ。对 §4 的一个共同平滑原子，将外 μ(q) 和
该原子的模数侧标量记为 β_(dℓ)，规范化后 |β_(dℓ)|≤1，
原子系数绝对和另由 A_J 支付。其 d 层准确写作
\[
 {\mu(d)\over d}\sum_{\ell\asymp Q/d}{\beta_{d\ell}\over\ell}
   \sum_{t\in U(\ell)}\widehat G_{d\ell}(dt)
                     B_\ell(t,A\bar d).                       \tag{D9}
\]
\(\widehat G_{d\ell}(dt)=\sum_{(n,d\ell)=1}a_n e_\ell(-tn)\)。
固定 d 后把 (n,d)=1 放入共同系数，剩余 (n,ℓ)=1 使用 D3，
不是先去掉掩码。外层的 μ(q) 及其他模长≤1 标量始终保留，
应用 Cauchy 时只用其绝对值界，不把 μ(e) 改成 μ²(e)。

## 4. 一次 Cauchy 与 d 层求和

固定 e,u,v,d 和一个共同平滑原子，其共同 n 序列有平方范数≪R。
对允许的 (ℓ,t) 做一次 Cauchy。D3 控制第一因子；精确 Parseval
\[
 \ell^{-2}\sum_{t\bmod\ell}|B_\ell(t,A\bar d)|^2
 =\varphi(\ell)/\ell-1/(\ell\varphi(\ell))\le1
\]
控制第二因子平方≤#ℓ≪Q/d。即使 A\bar d 随 ℓ 改变，范数公式仍
逐 ℓ 成立。由 D9 得该层费用
\[
 \ll_\epsilon{(RQ)^\epsilon\over d}
       \sqrt{{Q\over d}R\left(R+{Q^2\over d^2}\right)}.
                                                               \tag{D10}
\]
ℓ≥2 才有非零核，故 d≤Q。对 d 求和时三角不等式给
\[
 \sum_{d\le Q}{1\over d}
       \sqrt{{Q\over d}R\left(R+{Q^2\over d^2}\right)}
 \le R\sqrt Q\sum_{d\ge1}d^{-3/2}
       +\sqrt R Q^{3/2}\sum_{d\ge1}d^{-5/2}
 \ll\sqrt{QR(R+Q^2)}.                                      \tag{D11}
\]
这不是抵消不同 d 层；1/d 和剩余模数数量的平方根共同产生收敛。

**实际联合权的预算。** 对每个固定 e,u,v,d，取变量 n/R 和
ℓ/(Q/d)。原核第二变量为
\(ed\ell/S=(eQ/S)(\ell/(Q/d))\)，缩放因子 eQ/S 一致有界，
不产生 d 阶数损失。固定盒上作两变量光滑 Fourier 分离，取 J≥6，
系数绝对和≪A_J；前篇给出的固定盒 cutoff 与分部积分论证适用。
共同 n 系数为 μ(n)1_(n,e q₀ d)=1 乘共同 n 因子。原 (uv,dℓ)=1、
(ℓ,e q₀d)=1 只限制固定标签下允许的 ℓ，全部保留。原 n/ℓ 壳为
各自的单变量支持；原 Ψ 内部的连续积分支持没有另作硬分割。
分离预算对 e/u/v/d 一致，因此可在 D11 之前逐层使用，没有未付费
的跨 d 共同系数假设。

**principal 仍独立。** 它是 \(\mu(q)\sum_n a_n/\varphi(q)\)，不是
k=0 的中心核。由于
\(\sum_{Q<q\le2Q}1/\varphi(q)\ll_\epsilon Q^\epsilon\)，
固定 e/u/v 时费用≤A₀ RQ^ε，可被 D11 的 bound 吸收。

## 5. 恢复全部标签与物理外权

同前篇使用准确非零整数计数 #u≤4H/e、#v≤4L/e，空域直接为零，
以及 \(\sum_{e\asymp E}e^{-2}\ll1/E\)。三角不等式合并 principal
与全部 d 层，未在平方中删除任何 cross，得到
\[
 |\mathcal S_{E,Q}|\ll_\epsilon
       \mathcal A_J(RQ)^\epsilon{HL\over E}\sqrt{QR(R+Q^2)}.
                                                               \tag{D12}
\]
乘回唯一外权 2T/(q₀RS)，用内部 HL≲RS/T，在固定幂尺度上
\[
 \boxed{|\mathcal O_{E,Q}|\ll_\epsilon
       {\mathcal A_J T^\epsilon\over q_0E}\sqrt{QR(R+Q^2)}.}
                                                               \tag{D13}
\]
对于 q₀=1、R=S≈T³、H=L≈T^(5/2)、E≈T^η、Q≈T^(3−η)，
若 3/2≤η≤5/2，D13 的指数为 9/2−3η/2。故 η≥7/3 时满足
局部 T^(1+ε) 预算，η>7/3 时留正幂余量。特别是 η=49/20 给
\[
 \text{直接计数 }RS/E^2:T^{11/10},\qquad
 \text{D13}:T^{33/40+\epsilon},\qquad
 \text{改善 }11/40,\quad \text{距 T 的余量 }7/40.              \tag{D14}
\]
前篇的 Bertrand 整数族仍是这里的真实子族，所以 D14 不仅是空域
参数账。但 η=5/2 的非空性仍须依具体常数/整数端点，不能只由指数
断言；本篇非空见证只为 η=49/20。计数比较不声称原和有匹配下界。

D13 可从原 FP2 的和中逐项分离 D1；补集保留原共同 signed 算子。
它不覆盖只由 h 或只由 δ 承担某些 e 素因子的其他 genuine-gcd
分配、剩余 E/Q 区域、全部 q₀ 外和及其他物理包或尾项。因此这不是
全局 arithmetic gate、paired 能量估计、长 mollifier 渐近式，或
任何 14/17 / 2/3 零点排除的完成证书。

English summary: an inclusion-exclusion argument retains the exact unit mask
in a primitive additive large sieve. Unique squarefree Type descent contributes
1/d, and the d^(-3/2), d^(-5/2) sums converge. With the actual smooth weight and
all label counts restored, (D13) bounds the entire explicitly defined FP3
double-divisibility layer, not all genuine-gcd allocations or the global problem.
