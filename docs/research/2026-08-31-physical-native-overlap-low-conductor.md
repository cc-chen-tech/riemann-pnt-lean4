# 原生整数重叠：低导子大 gcd(m,k) 投影

白话结论：在之前全 h/δ 的低导子展开里，原生整数 m 与 Fourier
整数 k 有较大公因子的部分，可以额外利用稀疏计数。公因子至少
T^(1/10) 时，同一 E=T^(6/5) 尺度的这部分从旧 T^(11/10) 上界
降到 T^(59/60)。低公因子的补集仍未支付；这不是整个原式的界，
也没有证明 14/17 或 2/3 零点排除。本稿只交付数学推导和有限守卫。

English summary: in the existing native full-h/delta low-conductor expansion,
the projection gcd(m,k)>=G gains G^(-7/6). One factor comes from sparse
reciprocal-frequency counting; the other from a shorter divisor range.
At E=T^(6/5), G=T^(1/10), the bound is O(D200 T^(59/60+epsilon)).
The small-overlap complement and global zero-free target remain open.

## NO1. 冻结来源与对象

直接父版本 #554 固定
d37e1f2fb0b3c4fe5656fe6feab52587ed8efd0a，使用其
[LC1–LC6](2026-08-31-physical-low-conductor-common-large-sieve.md)。
上游为 #549 d4b8de45932f77aaa98acf7ef7f84ff48074dd4f 的
[CG1–CG10](2026-08-31-physical-common-gcd-full-reassembly.md)，
定义源仍是49cfacd70c60372757280177c7b63fd4f7760817的(4.4)–(4.5)。
原积分 I_k 与诱导Poisson使用
[TD3](2026-08-31-physical-full-delta-top-divisor.md)，但单位条件使用
后来的AM12/LC3：不恢复旧的(Y,z)=1。

固定 q₀=1、N=T³、R,S≍T³、M,K≍sqrt(T)、KS≍MR、MK≪T。
原 n,s 整包内部支持保证 n,s≤N/2。保留 p_N、B₀、W、V、F_M、F_K，
没有固定 H/L 因子；所有全 h/δ 重分组仅在本 AFE 层内。
范数 D200 完全沿LC1，不引入新的原权假设。

令 E=T^(6/5)，自然辅助 e' 壳为 E'≥E、q'≍S/E'。
沿原低导子展开写
\[
 h=(e',m),\quad m=hz,\quad e'=h\ell d f l C,
 \quad k=dr,\quad n=fjX,\quad q'=ljY.                \tag{NO1}
\]
这里 m 是原native正整数，k是 I_k 的Fourier整数；h不是原Fourier
h，d不是原Ramanujan展开的d=q项，l不是导子ℓ。
定义 \(\mathscr R^{\ge G}_{E,<\Lambda}\)：在LC2精确低部中，
对每个原求和项插入
\[
 1_{k\ne0}\,1_{\ell<\Lambda}\,1_{\gcd(m,k)\ge G}.
                                                               \tag{NO2}
\]
原 ℓ=1 唯一主角色包含一次。先按LC5剥离辅助 q'=1，它及k=0、
补回两轴后的其他零项仍沿CG5保留，不在本投影中重复计入。
这是原式经精确变换后的线性投影，不是原 h,δ 整数元组的literal子族。
m、k、mk均不要求平方自由；原Möbius整数是n与e',q'。

本稿证明，取Λ=max(2,T^(1/5))、G=T^γ，有
\[
 |\mathscr R^{\ge G}_{E,<\Lambda}|
 \ll_\epsilon\mathcal D_{200}T^{1+\epsilon}
 \qquad(3/35\le\gamma\le1/2).                       \tag{NO3}
\]
特别γ=1/10时可用更小的指数59/60。

## NO2. 同一个集合的两项精确计数收益

原h,d互素，且(d,z)=1不能删除，因而(d,hz)=1。于是
\[
 \gcd(m,k)=\gcd(hz,dr)=\gcd(hz,r).                   \tag{NO4}
\]
当此值≥G时，|r|≥G。在非零环|k|≍vT/K中，严格迫使
\[
 d\ll\frac{vT}{KG}.                                \tag{NO5}
\]
固定h,z和实数R₀>0，正负r共同满足
\[
 \begin{split}
 \#\{0<|r|\le2R_0:\gcd(hz,r)\ge G\}
 &\le\sum_{\substack{g\mid hz\\g\ge G}}
                 2\lfloor2R_0/g\rfloor\\
 &\le4R_0\tau(hz)/G.                               \tag{NO6}
 \end{split}
\]
不新增+1：若2R₀<G，集合自动为空。g是计数中的一般正除数，
不要求平方自由；hz≍M，所以τ(hz)≪T^ε且没有额外k环增长。
这些恒等式不需要也不允许补上(h,z)=1、(d,r)=1。

## NO3. 原共同系数与一次大筛不变

先固定h,d,z,k,f,l,j。NO2的新增指标此时完全不依赖C、X、Y、ℓ。
因此可原样应用LC3的C列区间一致界，再用LC7的一次joint primitive
hybrid large sieve；不是将一个有符号总和的上界直接赋给其子和。
外层允许导子的扩和仍只在Cauchy后的正范数里发生。

全部原μ(X)μ(Y)、φ(f)φ(l)、Gauss因子、(d,z)=1和AM12/LC3
的单位条件保留。旧E壳的β^μ标记按LC5作真实d₁/d₂分解，仍只
改变C列支持及其外标量；NO2不会把它变成任意有界C乘子。
特别没有(C,X)、(C,Y)或(Y,z)新掩码。

原定理的解析输入是LC3中引用的log指数对
(κ,δ)=(1/30,1/6)与普通primitive混合大筛。本稿不增加文献输入，
也不宣称新的Möbius专属消去。若任意筛选e'族，指标会进入C列，
不能据本证明自动调用同一个无筛选的C振荡界。

## NO4. 完整除数层、旧壳及无限频率尾

固定h,d，先对每个z应用NO6，再计z≍M/h，将LC9所用的
\((M/h)(vT/(Kd))\) 行数上界乘上G^-1 T^ε。
对LC6振荡项，另外保持NO5，再求h,d正和：
\[
 \sum_{h\ll M}h^{\delta-1}
 \sum_{d\ll vT/(KG)}d^{\delta-1}
 \ll_\epsilon T^\epsilon(vMT/K)^\delta G^{-\delta}.
                                                               \tag{NO7}
\]
这里δ=1/6>0。两个收益可同时使用：先对每个d计算稀疏r，
随后d范围以外同一集合严格为空；并非重复乘同一个比例。
LC6的T^-1项没有h/d的δ权，只用调和和，故只保留G^-1。

f,l,j的四组指数仍是LC4的原表，每项至多调和；LC5的
H₀=max(1,E'/E)标记费H₀^δ仍先支付，再把(T/E')^δH₀^δ
换成(T/E)^δ。B_i中的E'不变。

|k|≍vT/K的大频环仍由原I_k的十二次非驻相积分给v^-12。
新计数至多v^(1+δ+ε)，和原证明一样全环可和。负频、小环均保留，
极短r区间或过大的d按NO5/NO6为空；没有未估计的单点边界费用。
本节及共同权的导数仍只消耗一份原D200。

## NO5. 四主项、四余项与参数

沿LC4记
\[
 B_1=T^{7/2}/E'^2,\quad B_2=T^{5/2}/E'^{3/2},\quad
 B_3=T^{5/2}/E'^2,\quad B_4=T^{3/2}/E'^{3/2}.
\]
全部ℓ<Λ（含ℓ=1一次）的投影费用为
\[
 \begin{split}
 \mathcal D_{200}T^\epsilon\big[&
 T^{1/30}(T/E)^{1/6}G^{-7/6}
 \{B_1+(B_2+B_3)\Lambda^{5/6}+B_4\Lambda^{11/6}\}\\
 &+T^{-1}G^{-1}
 \{B_1+(B_2+B_3)\Lambda^{1/2}+B_4\Lambda^{3/2}\}\big].
 \end{split}                                                     \tag{NO8}
\]
这些是实际原系数费用，不把Q'<T的交叉项删掉。
所有B_i随E'增大下降，故自然E'≥E各壳可和，最坏E'=E。
η=6/5、Λ=max(2,T^(1/5))、G=T^γ时，四主指数为
\[
 (11/10,13/15,4/15,1/15)-(7/6)\gamma,
\]
四余指数为(1/10,−1/5,−4/5,−1)−γ。因此阈值恰是γ≥3/35。
γ=1/10的八项分别是
\[
 (59/60,3/4,3/20,-1/20),\qquad(0,-3/10,-9/10,-11/10).
\]
有限T中的Λ=2及固定支持常数被原隐含常数吸收。

## NO6. 原支持非空，且不是旧hd小带

给出无限支持构造。令Y趋于无穷，选互异素数
g≍Y^11、p,d≍Y^39（p,d用不同倍长区间），令
\[
 m=gp,\quad k=gd,\quad T=2\pi mk,\quad A=gpd.
\]
选素数b在(T^(6/5)/A,2T^(6/5)/A)，令e'=Ab，故
E<e'<2E且b≍Y^31。再选素数q'在(T³/(100e'),T³/(50e'))，
s=e'q'，选素数n在(s,2s)。Bertrand定理给这些素数，充分大Y时
它们按尺度彼此不同。原内部n,s≤T³/2和全部单位条件成立。

h=(e',m)=gp，d=(e'/h,k)，z=1，r=g。m,k不含e'/A的因子，
且gcd(m,k)=g≍T^(11/100)>T^(1/10)。取M=K=m、R=S=s，比较常数
固定，MK≪T且KS≍MR。原相位驻点y=nm/s在(K,2K)，
t=2πkmn/s满足t/T=n/s∈(1,2)。这是原展开支持，不保证任意
预先指定W/F/V的积分非零。该e'壳中β^μ=1。
A≍T^(89/100)超出旧principal hd≤T^(2/3)小带。

脚本另核对完全整数的见证
\[
 T=3568229,\quad m=707,\quad k=721,\quad
 e'=73476389,\quad q'=19322369063,\quad
 n=2366229842790922513.
\]
此时h=707、d=103、gcd(m,k)=7、A=72821；素数均小于2^64。
原E壳用T^6≤e'^5<32T^6核对，G条件用7^10≥T核对，
驻点t的范围只用3<π<22/7的有理夹界。

## NO7. 未付余项与交付边界

本结果仅为NO2的非零低导子投影。原完整高导子和可沿LC13支付，
但不能把G收益赠给任意高导子子投影。低导子gcd(m,k)<G的补集
仍保留原全部signed算子，未取得所需T上界。

它不同于固定H/L的Type-II b/c重叠，也不同于q频率乘积gcd；
不能与它们的saving相乘。临时联合驻相推导不是本证明的依赖。
这里也不支付其他E、q₀外层、非内部AFE及跨尺度统一尾、全局gate。
没有证明14/17或2/3，没有更改任何Lean目标或冻结父版本。
有限守卫验证计数、掩码反例、原支持和有理指数，不能替代解析
输入、无限尾或独立数学审查，更不是main最终验证。
