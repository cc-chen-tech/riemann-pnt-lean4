# 实际大 gcd 子族：分离拥挤 Type 频率并完成局部结账

白话结论：这次不把模型列当作原式，而直接使用上游冻结的 FP2/FP3
原子。Type 完成后，仍含大素数 p 的频率跨 p 不重合；其余低分母
频率准确重装配出 1/p 外权。保留原 principal、两种频率、所有单位
掩码与物理外权，可以控制一个指定的真实大 gcd 子族。下例从原
整数绝对计数的 T^(11/10) 上界改为 T^(37/40+ε)，净节省 7/40，
相对局部 T 预算留下 3/40 余量。

这不是所有 genuine-gcd 分配、整个 off-diagonal 或 paired-CG 算子
的控制，也没有证明 14/17、2/3 或长 mollifier 渐近式。这里的
“拥挤”指 **Type 频率 k**，不是共同 Fourier 频率 ν=0。
没有写 Lean，也没有将原 μ(e) 改成 μ²(e)。

## 1. 唯一物理上游与本次精确子族

复用 [MWKF-PHYS-v1 的 FP1–FP7](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/7cf2e7d43c4365e38e2aa708d1a250694b698bec/docs/research/2026-08-30-mwkf-frozen-physical-atom.md)。
文件 SHA256 为 `a7e39b12936fd463aabd46216c12ac2eb1e5b87473910e13600a472c11bfb53a`；
其原定义永久指向研究提交 `49cfacd70c60372757280177c7b63fd4f7760817`。
本篇不重定义 AFE、reflection、taper 或原核 Ψ。

固定平方自由原 gcd q₀。使用 FP §3 的内部光滑 core，特别是
原 mollifier 支持、Kz Mz≲T、Kz S/(Mz R)≈1，以及
\(HL\lesssim RS/T\)。所有所需阶数的归一化混合导数预算记为
\(\mathcal A_J\)，原核绝对值预算为 \(\mathcal A_0\le\mathcal A_J\)。
内部例子中这些预算为 O(1)；较大 log-core 必须显式支付其预算。

取 \(E,G\ge1,P\ge2\)，\(P\ge2G\)、\(S\asymp EGP\)，选
\[
 \begin{gathered}
 E<e\le2E,\quad G<g\le2G,\quad P<p\le2P,\quad p\text{ prime},\\
 e,g\text{ squarefree},\quad q_0,e,g,p\text{ pairwise coprime},\\
 s=egp,\quad r=n,\quad h=eu,\quad\delta=ev,\quad
 (n,q_0egp)=(uv,gp)=1.
 \end{gathered}                                                    \tag{L1}
\]
保留原 n/s/h/δ 壳、正负标签、所有截断与 taper；不容许 u 或 v 为零。
记 \(Q=gp,A=euv\)。于是 \((h\delta,s)=e\)，相位为
\(e_Q(-A\bar n)\)，系数仍为 \(\mu(e)\mu(g)\mu(p)\mu(n)\)。
因 p>g，p 是 Q 的唯一最大素因子；同一原始行不会因选取不同 p
而重复。e 则由真正 gcd 唯一确定。不同半开 dyadic 块按原分区处理。

所选原式贡献准确写为
\[
 \mathcal O_{E,G,P}={2T\over q_0RS}\mathcal S_{E,G,P},\qquad
 \mathcal S_{E,G,P}=
 \sum_{(L1)}\mu(e)\mu(g)\mu(p)\mu(n)
 p_N(q_0n)p_N(q_0egp)
 \Psi(n/R,egp/S,ev/L,eu/H)e_Q(-A\bar n).
                                                                    \tag{L2}
\]
这是 FP3 的真实层，不是 signed-overlap 容斥中的第三个正项。
下面只估计 L2，不把不同表示中的 n 因子相乘，也不使用未认证的
twisted-character 或跨 e 共同相位假设。

## 2. 真实 Type 列的非拥挤大筛，保留 p-unit 掩码

先给有限系数引理。固定 g≥1，p∈(P,2P]、p∤g；共同序列 aₙ
支撑于 1≤n≤2X，X≥1。令
\[
 F(x)=\sum_n a_ne(nx),\quad F_p(x)=\sum_m a_{pm}e(mx),\quad
 T_p(k)=\sum_{(n,p)=1}a_ne(-kn/(gp)).
\]
不删任何项便有
\[
 T_p(k)=F(-k/(gp))-F_p(-k/g).                                      \tag{L3}
\]
对 p∤k，分数 k/(gp) 约分后仍含 p。不同 p 不会有相同分数；
其圆周差的分母整除 \(gp_1p_2\)，不是 \(g^2p_1p_2\)。因此共同
频率集合的间距至少 \((4gP^2)^{-1}\)，同 p 的间距更大。
由[加性大筛 Theorem 1](https://www.renyi.hu/~gharcos/large_sieve.pdf)，
\[
 \sum_p\sum_{k\bmod gp\atop p\nmid k}|F(-k/(gp))|^2
 \ll (X+gP^2)\|a\|_2^2.                                         \tag{L4}
\]

p-unit 掩码的费用可准确计算。每个模 g 的类有 p−1 个 p∤k 的 lift，故
\[
 \begin{split}
 \sum_{k\bmod gp\atop p\nmid k}|F_p(-k/g)|^2
 &=(p-1)g\sum_{r\bmod g}\left|\sum_{m\equiv r\ (g)}a_{pm}\right|^2\\
 &\le(p-1)(2X/p+g)\sum_m|a_{pm}|^2.
 \end{split}                                                       \tag{L5}
\]
这里保留了整数端点的 +g。记实际允许的素数集合为
\(\mathcal P\subset\{P<p\le2P:p\nmid g\}\)，跨 p 的子序列能量满足
\[
 \sum_p\sum_m|a_{pm}|^2
 =\sum_n|a_n|^2\omega_{\mathcal P}(n)
 \le {\log(2X)\over\log P}\|a\|_2^2.                             \tag{L6}
\]
其中 \(\omega_{\mathcal P}\) 只计属于允许集合的素因子。
令 \(\mathcal L_X=1+\log(2X)/\log P\)。L3–L6 给
\[
 \boxed{\sum_p\sum_{k\bmod gp\atop p\nmid k}|T_p(k)|^2
 \ll\mathcal L_X(X+gP^2)\|a\|_2^2.}                              \tag{L7}
\]
可对每个固定 (u,v) 删除不满足 p∤uv 的 p 子集，因为这是正能量。
这不支付 u/v 外层计数，也不容许先删去其有符号权。

在 L2 中固定 e,g 后，按
\((n/R,p/P,u/(H/e),v/(L/e))\) 分离实际 Ψ 与内部 taper。原核
代入 egp/S、ev/L、eu/H 后的缩放比例在共同紧集中，故足够高阶
\(\mathcal A_J\) 控制共同 Fourier 原子的加权 ℓ¹ 预算。每个原子可取
\(a_n=\mu(n){\bf1}_{(n,eq_0g)=1}\) 乘一个共同 n 光滑因子，
\(X\asymp R,\|a\|_2^2\ll R\)。p 侧有界标量单独保留。
此处的 X 不是原 mollifier 长度 N。固定 e 的掩码不能直接用于未
付费的 e 聚合；本篇在 §5 显式计数 e。

具体地，在包含这些归一化变量支持的固定盒上乘一个恒为 1 的光滑
cutoff，再作固定周期的四维 Fourier 展开。取 J≥6，分部积分给
\(|c_{\mathbf m}|\ll\mathcal A_J(1+|\mathbf m|)^{-6}\)，故
\(\sum_{\mathbf m}|c_{\mathbf m}|\ll\mathcal A_J\)。各指数原子的
四个一变量因子模长为 1，原固定壳的单变量限制留在相应因子中；
并不对算术掩码作 Fourier 平滑。内部 mollifier cutoff 不接触角点，
p_N 的归一化导数有界，可并入同一预算。分离后 p 允许集可依赖
固定 e/g/u/v，但不依赖 n；原 Ψ 中 x、t 的积分支持已经包含在
其光滑函数中，不能额外替换成一个 n/p 相关的硬截断。

## 3. 不删除 principal 的完整 Type 完成

对固定 e,g,p,u,v，令 aₙ 含其实际 n 权及全部单位条件，
\(\widehat G_Q(k)=\sum_n a_ne_Q(-kn)\)。这里允许权依赖所有固定标签。
定义
\[
 \rho_Q={\mu(Q)\over\varphi(Q)},\quad
 B_Q(k,A)=S(k,-A;Q)-{\mu(Q)c_Q(k)\over\varphi(Q)}.
\]
原 (9.995) 精确给
\[
 \sum_n a_ne_Q(-A\bar n)
 =\rho_Q\sum_na_n+{1\over Q}\sum_{k\bmod Q}\widehat G_Q(k)B_Q(k,A).
                                                                    \tag{L8}
\]
\(B_Q(0,A)=0\)。保留完整 Ramanujan 修正后，有限 Parseval 是
\[
 {1\over Q^2}\sum_k|B_Q(k,A)|^2
 ={\varphi(Q)\over Q}-{1\over Q\varphi(Q)}\le1.                   \tag{L9}
\]
L9 只使用 Q 平方自由、(A,Q)=1；不能对未中心化的其他核套用本等式。
principal 是 L8 第一项，不是 canonical zero Gram 或共同 ν=0。

## 4. 拥挤 k=pj 恰是带 1/p 外权的低 g 行

CRT 和 Ramanujan 分解给
\[
 S(pj,-A;gp)=-S(j,-A\bar p;g),\qquad
 {\mu(gp)c_{gp}(pj)\over\varphi(gp)}
 =-{\mu(g)c_g(j)\over\varphi(g)}.
\]
因此 L8 中的全部 p|k 部分（j=0 的核为零）准确等于
\[
 \begin{split}
 \mathcal C_{e,g,p,u,v}
 &=-{1\over p}{1\over g}\sum_{j\bmod g}\widehat G_{gp}(pj)
       \left(S(j,-A\bar p;g)-{\mu(g)c_g(j)\over\varphi(g)}\right)\\
 &=-{1\over p}\sum_na_n
       \left(e_g(-A\bar p\bar n)-{\mu(g)\over\varphi(g)}\right).
 \end{split}                                                       \tag{L10}
\]
第二行是再用一次有限逆变换，不要求任何共同 n 系数或平滑性。
原 (n,p)=1 仍在 aₙ 内。g=1 时此项为零。低 g 相位依赖 p，未被删除。
若写 \(j=dr,(j,g)=d\)，其 Type 有效导子为 g/d；不因此假设它
已由某个旧低导子账支付。我们直接使用 L10 的标量界付费。

## 5. 三部分全部恢复外权后结账

令上标 nc、cr、pr 分别指 L8 的 p∤k、p|k 和 principal；三者之和
就是 L2。本篇不在它们的平方能量中删除交叉项，而是对标量贡献
使用三角不等式。

**非拥挤。** 固定 e,g,u,v 和一个共同平滑原子，对 (p,k) 只做一次
Cauchy。L7 控制第一因子；L9 给第二因子的平方至多 #p≤O(P)。因此
该原子的线性和至多
\(\ll\sqrt{\mathcal L_R P R(R+gP^2)}\)。再用平滑 ℓ¹ 预算、
\(\sum_{e\asymp E}e^{-2}\ll E^{-1}\)、#g≪G，以及原标签计数，得到
\[
 |\mathcal S^{\rm nc}|
 \ll\mathcal A_J{HLG\over E}
       \sqrt{\mathcal L_R P R(R+GP^2)}.                            \tag{L11}
\]
标签计数没有隐去 +1：若 e>2H 或 e>2L，相应非零整数域为空；
否则 \(\#\{0<|u|\le2H/e\}\le4H/e\)，v 同理。有限符号块只花常数。

**拥挤。** L10 的中心化核绝对值≤2，\(\sum_{P<p\le2P}p^{-1}\ll1\)。
保留实际未分离权也可直接得
\[
 |\mathcal S^{\rm cr}|\ll\mathcal A_0 RHLG/E.                    \tag{L12}
\]

**principal。** \(\varphi(gp)=\varphi(g)(p-1)\)，
\(\sum_p1/(p-1)\ll1\)、\(\sum_{g\asymp G}1/\varphi(g)\ll_\epsilon G^\epsilon\)。
同一真实 e/n 权仍在；取绝对值后
\[
 |\mathcal S^{\rm pr}|\ll_\epsilon\mathcal A_0 RHL E^{-1}G^\epsilon.
                                                                    \tag{L13}
\]
没有把 μ(e) 的符号改成平方自由正权来取得字符抵消；这里仅使用 |μ|≤1。

乘回唯一的 FP2 外权 \(2T/(q_0RS)\)，再用内部 \(HL\lesssim RS/T\)，
L11–L13 给实际子族定理
\[
 \boxed{
 |\mathcal O_{E,G,P}|\ll_\epsilon
 \mathcal A_J T^\epsilon {RG\over q_0E}
 \left(1+\sqrt{P\left(1+{GP^2\over R}\right)}\right).}
                                                                    \tag{L14}
\]
L14 中尺度为固定幂，\(\mathcal L_R,G^\epsilon\) 已按通常方式吸收；
若要有限高度显式常数，应使用未吸收的 L11–L13。

## 6. 真正非空的覆盖例子及节省参照

取 q₀=1、R=S=T³/8、Kz=Mz=√T、H=L=S/√T，以及
\[
 E\asymp T^{49/20},\qquad G\asymp T^{1/5},\qquad P\asymp T^{7/20}.
                                                                    \tag{L15}
\]
EGP≈S、p>g、E<min(H,L)。各项的**物理**上界指数为

| 估计 | 指数 |
| --- | --- |
| 同一子族原整数绝对计数 RS/E² | 11/10 |
| 非拥挤 L11 | 37/40 |
| 拥挤 L12 | 3/4 |
| principal L13 | 11/20 |

故整个所选子族为 \(O(T^{37/40+\epsilon})\)。7/40 是相对明确的
原整数计数上界的节省，不是已证明的下界之差，也不自动代表优于所有
已有方法。它确实低于局部 T 预算，余量为 3/40。

非空性可给无限整数族，而不只给指数点。由
[Bertrand 定理](https://math.stanford.edu/~ksound/Math155Spr12/Bertrand.pdf)，
对 Y→∞ 选互异素数 g≈Y⁴、p≈Y⁷、e≈Y⁴⁹，令
T=(8egp)^(1/3)≈Y²⁰，R=S=egp，H=L=S/√T。
取 u=v=⌈H/e⌉≈Y，则 u<g,p、H≤eu≤2H。再选素数 n∈(S,2S)，
则 n>e,g,p；L1 全部单位与真正 gcd 条件成立，n,s≤N/4。
原 x=3√T/4 时 (xn+δ)/s 位于 [√T/2,2√T]（大 Y），满足原 AFE
两个连续支持。E/(RG√P/T)≈Y^(3/2)→∞。这只证明整数/连续支持域
非空，不宣称任意给定 W/F 的积分必非零或该族有正密度。
这里 R/S/Kz/Mz/H/L 是比较尺度；放回固定 dyadic partition 时取
相邻有限个块并保留常数松弛。该取整不改变指数，也不将特定 cutoff
在某一点的非零性当成前提。

另一个有限端点守卫取 T=64、R=S=32768、H=L=4096、q₀=1，
E=1500、G=2、P=4，e=2003、g=3、p=5、n=30011、u=v=4。
则 s=30045、h=δ=8012，各壳与单位条件成立，E≥RG/T。
它只验证支持与拥挤子界的端点，不是 L15 的有限高度常数认证。

## 7. 旧覆盖对照、交付与未证范围

上游 §9.53 的 large-gcd 是 Type-product 的 gcd，§9.84 是另一
cofactor 核的 gcd；不是本篇 genuine e。§9.109 的 rank-one 校正
以及 §9.144 的 centered resonant projector 也不是 L2 的完整线性
大 gcd 子族。PQ12 的 κ/B 区域使用不同后变换参数；没有提供逐项
对应前，既不能把本篇说成替代 PQ12，也不能将两者节省相乘。

本篇覆盖对象完全由 L1–L2 指定，包含其 principal、全部 Type k
及真实外权；不是仅交付一个待接入的行模型。但是它不覆盖 e 不
同时整除 h、δ 的其他 genuine-gcd 行、剩余 E/G/P 区域、全部 q₀
求和、未选物理包、canonical zero/reflection 或独立物理尾。
这些补集仍须保留，不能从 L14 推出零点排除。
从完整原式中减去 L2 后，补集仍保持原共同有符号算子；本篇没有
对补集先取绝对值，也没有将这一局部标量界登记成全局能量门限。

有限检查脚本只验证各恒等式、圆周间距、整数端点及指数，不能替代
本篇解析证明。依赖的冻结 #490/#503 不回改；此文作为独立后续成果。

English summary: retaining the actual unit mask, noncrowded Type frequencies
admit a fixed-common-modulus additive large sieve with cost X+gP². Crowded
frequencies reassemble exactly into a centered lower-g row with weight −1/p.
Together with the original principal mean, one Cauchy step and the complete
e/g/label counts prove (L14) for the explicitly selected physical gcd family.
The example (L15) improves its counting upper bound from T^(11/10) to
T^(37/40+ε). This is a restricted scalar-family bound, not a zero-free theorem.
