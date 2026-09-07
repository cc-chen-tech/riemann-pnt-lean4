# 固定光滑 H/L：对数余因子合数模数的完整 centered 包

白话结论：原模数 q 不必再是素数。当 q=cp，p 是唯一大素数，
c 平方自由且至多按固定对数幂增长时，两个 CRT 分支都能计费。
本文保留合数层的非单位双频和原单位差，重跑同一共同列的大筛及
主角色对数标签估计。在 7/6≤η≤5/4 支付这个完整 fixed-H/L 线性包
的 O(A₃₀T^(1+ε)) 预算，而不是只支付短 Type-II 或一个角色。
没有证明跨 H/L 或 AFE 的总能量，完整 twisted moment 仍未证明。

Git 父版本为 #555 **b94b0bc52b108b9a16001d0026ba579aadcfcbbe**。
唯一原式为冻结 #547 `63f15f23a7d06452d9763e2801a32f00de1a72c5`
的 RH1/LP1 smooth 包，相关定义在 #555 `b94b0bc52b108b9a16001d0026ba579aadcfcbbe`
树中未改变。本稿直接重证原 mu(n) 的整个 centered 包，不调用 #526 的
短 bc 子和，也不调用 full h/delta 成果。

## CQ1 原对象、唯一标签和目标

e prime in [E,2E)，q=c*p in [Q,2Q)，c squarefree，p prime，(c,p)=1，
(e,c*p)=1。取固定 A>=0，1<=c<=Cstar=(log(2T))^A。大 T 时
Cstar^2<Q，p>c，q 的这种大素数标签唯一。r=n,s=e*q,h=e*u,delta=e*v。
原 (n,e*q)=(u*v,q)=1，u,v 非零，mu(e)mu(c)mu(p)mu(n)、两 taper
以及唯一外 2T/(RS) 都保留。R~S~EQ~T^3，H~L~T^(5/2)，
E~T^eta，7/6<=eta<=5/4；整包 n,eq<=N/2，无额外联合硬边缘。
精确原式（记 e_q(x)=exp(2πix/q)）为
\[
 \mathcal C_A={2T\over RS}
 \sum_{\substack{e\in[E,2E)\ {\rm prime}\\
                 c\le C_*,\ c\ {\rm squarefree}\\
                 p\ {\rm prime},\ Q\le cp<2Q\\(ec,p)=(e,c)=1}}
 \mu(e)\mu(c)\mu(p)
 \sum_{\substack{n\ge1\\(n,ecp)=1}}\mu(n)p_N(n)p_N(ecp)
 \sum_{u,v\ne0}\Psi_{\rm sm}
    (n/R,ecp/S,ev/L,eu/H)1_{(uv,cp)=1}
 \left\{e_{cp}(-euv\bar n)-{\mu(cp)\over\varphi(cp)}\right\}.
\]
这里 p_N(x)=1−log(x)/log(N)。独立 e/q/n 壳与素数条件留在算术列；
原 smooth Ψ 含重插的 F(|h|/H)F(|δ|/L)，不是一般硬 H/L。
[RH1](2026-08-31-physical-prime-pair-reciprocal-hybrid.md)、
[LP1](2026-08-31-physical-prime-pair-principal-loglabels.md) 的原核和半范数
不变；其 smooth 上游为
[DP1–4](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/7cc9646c8b8a8589b920e24652c86bd063f4b1d7/docs/research/2026-08-31-physical-centered-character-poisson.md)。
同一原 smooth 核总阶30预算 A30；U=H/E,V=L/E,D1=Q/U,D2=Q/V，
nu=R D1 D2/(EQ)~T。目标是这个指定合数子族的整个线性和 <=A30 T^(1+eps)。
所有对 c 的幂费用显式记录后才用固定 A 的 log 幂吸收；不声称 c<=T^gamma。

## CQ2 两个物理 CRT 分支，缺一不可

固定 n,e,p,c，且 (ne,cp)=1。R_t(u,v)=1_(uv,t)=1 e_t(-lambda_t uv)，
P_t=mu(t)/phi(t) 1_(uv,t)=1，K_t=R_t-P_t。
lambda_c=e*inverse(n*p) mod c，lambda_p=e*inverse(n*c) mod p。
逐整数精确有

    K_q = R_c K_p + K_c P_p.                            (CQ1)

c=1 时 K_c=0。不能用 K_c K_p 替代，也不删不满足 q-unit 的双频。

第一分支作正号有限双 DFT。令

    S_c(rho,sigma;n,e,p)
      = sum_(u,v mod c,unit uv)
          e_c(-e*inverse(np)*uv + inverse(p)*(rho*u+sigma*v)),
    H_c = S_c - mu(c)/phi(c) c_c(rho)c_c(sigma).

互补逆元必须在全部局部频率中。大素数分支给

    S_c * p * 1_(rho*sigma,p)=1
       [ e_p(n*rho*sigma*inverse(ec)) + 1/(p-1) ].       (CQ2)

原 q^-2 Poisson 系数乘 UV，故 raw 项是 UV/q * (S_c/c)，不是 UV/p。
第二分支的完整谱是 H_c * [-c_p(rho)c_p(sigma)/(p-1)]，同样乘 UV/q^2。
两者合回 q 的原 centered 双 DFT。rho/sigma 为非零 c 非单位时，
S_c 和 H_c 都可能非零；若 rho=0 mod c 或 sigma=0 mod c，H_c 因
零行/列均值必为0，但 S_c 仍可非零。未截成 q-unit 双频。
第一分支 p-unit 自动排除整数 rho=0 或 sigma=0。

CRT 及每素数完整 raw 双谱给 |S_c|<=product_(l|c)(l+1)<=c*tau(c)，
因此 |S_c/c|<=tau(c)。这一步只为上界，不丢符号。

## CQ3 第二分支直接周期完成

原物理第二分支是 -K_c/(p-1) *1_(uv,p)=1，原 n-p unit 仍保留。
大 T 时 2U<p、U>=2c。u 的 p-unit 因 0<|u|<=2U 冗余；
v 和 n 的 p-unit 不删除。固定 n,v；c-unit 不满足则 K_c=0，
否则 sum_(u mod c) K_c=0（c squarefree，(lambda_c v,c)=1）。
对真实 smooth u 权作一维 Poisson，零频恰为0，其余频率以 J=6 给

    |sum_u K_c(u,v) W(u/U)| <= C A6 U (c/U)^6.          (CQ3)

这是有限 Fourier 係数 <=2c 及 1/c Poisson 归一化后的非零频率尾；
对固定其他变量一致，不假定权分离。c=1 分支直接0。
每个 c 的 e,p,n,v 计数为 O(E*(Q/c)*R*V)，1/(p-1)<=C c/Q，
因此含原 2T/(RS) 后

    |Low_c| <= C A6 T*UV/Q * (c/U)^6.                 (CQ4)

当前 eta 范围，其未含 c 的幂是 1+(5-2eta)-(3-eta)-6*(5/2-eta)
=-12+5eta<-5。全部 c<=Cstar 可和且远小于 T。原单位和 mu 全保留。

## CQ4 高分支常数、扩和差及新的有限周期因子

CQ2 的 +1/(p-1) 项 O_c 完整保留全部 p-unit 与 c 谱因子。
|S_c/c|<=tau(c)，UV D1D2=Q^2，恢复 E*(Q/c)*R 行数给
|O_c|<=C A30 tau(c) T。

raw 项先保留原 (n,ecp)=1 和 p-unit 双频。先取 e|rho*sigma 的尾 B_e,c；
剩下 e-unit 双频中扩 (n,p)=1 并减 B_n,c；最后扩 p-unit 双频减 B_p,c。
不删除 (n,c)=1 或 e/p 的 c-unit。准确仍是 Raw=F_c+B_e,c-B_n,c-B_p,c。
未定义 inverse(n) mod p 的值不会使用：扩和时用 CQ2 的显式多项式相位。
Sc 只需 inverse(n) mod c，故 (n,c)=1 仍是定义域。
保留 mu(pj) 原值，n=pj 的数目 floor(2R/p)，无 +1。
六阶非零倍数尾和原行数给

    |B_e,c| <= A30 tau(c) c^-1 T^(13/2-7eta+eps),
    |B_n,c| <= A30 tau(c) T^(1+eps),
    |B_p,c| <= A30 tau(c) c^5 T^(-23/2+5eta+eps).       (CQ5)

接下来合法 reciprocity 是

    e_p(n*rho*sigma*inverse(ec))
      = e_e(-n*rho*sigma*inverse(cp))
        * e_c(-n*rho*sigma*inverse(ep))
        * e(n*rho*sigma/(ecp)).                        (CQ6)

定义 Z_c=(S_c/c)*e_c(-n*rho*sigma*inverse(ep))。
它对 n,e,p,rho,sigma 分别 c 周期，定义在前三者 c-unit 的域；
不在 rho/sigma 上加 unit 条件。模长<=tau(c)。新连续 chirp 的
尺度仍 X=R J1J2/(EQ)，不是 X/c 或 X*c；p 的尺度是 Q/c，
原 Φ 的 q/Q 坐标就是 p/(Q/c)，无 c 导数损失。

## CQ5 有限共同分离，不把周期因子当 smooth

对五个 c 剩余类直接分离 Z_c：至多 c^5 个 rank-one residue 指示项，
每项係数模<=tau(c)。n/p/双频指示进入共同算术列，e 指示进入模数行。
这给保守的 projective l1 <=c^5 tau(c)，绝不把它计作1。
全部 class 对 rho/sigma 包括零；不引入原 smooth 半范数的新导数。
e>c、p>c，e/p 两 prime 的 c-unit 由原允许行保留。

对 e_e 周期因子采用 prime-e 的完整角色展开。非 principal chi_e 的
係数 tau_e(bar chi_e)/(e-1) 与固定 c 的 bar chi_e(c) 同时保留。
后者只为模数行标量；五个 residue 指示分别独立，所以 RH 的
共同 n 与 p*rho*sigma 两列重跑成立。第二列长 K0/c，K0=Q D1D2，
不把不同 c 误作同一列，但可逐 c 计费。一次 [CIS (1.6)](https://arxiv.org/pdf/1105.1176) 普通 hybrid primitive LS
给原 RH18 四项分别乘 c^-1,c^-1/2,c^-1,c^-1/2，另乘
c^5 tau(c) 和 A30。其中未乘原外权、未加 c^5τ(c) 的完整每块预算是
\[
 {A_{30}UV\over Q\sqrt{E(1+X)}}
 \sqrt{R(K/c)(R+E^2(1+X))(K/c+E^2(1+X))}
 T^\epsilon\prod_i(1+\lambda_i)^{-8+\epsilon},
\]
K=K₀θ、X=νθ、θ=λ₁λ₂。这是 RH16 真正以 K/c 重跑，不是丢弃
原和的某些行后直接继承一个 signed 上界。c 固定后其列才共同。
平方展开与 RH17 的比较仍被 2max(θ,θ²) 控制，外时间环的增长至多2^j，
与2^(-6j)可和；每个 λ_i→0、∞ 方向均由 √θ+θ 和八阶尾控制。
无限乘积列的除数能量额外 ∏(1+λ_i)^ε 也保留，取小 ε 后重命名。
因此所有原子、双对偶和 Mellin 交换先对有限截断操作，再用此正 majorant。

这些负幂可放大为1，故 Nonprincipal_c
<=A30 c^5 tau(c) T^(1+eps)。全部 dual/Mellin 尾仍 RH 的正 majorant。

principal 的两个 e-unit mask 必须像 LP4 那样完整扣回：n=e*j 与
e|rho*sigma 两差项（互不重计）额外係数 1/(e-1)，对应
<=A30 tau(c)/c [T^(4-3eta)+T^(13/2-8eta)]。
在删去这两个 mask 后，Zc 仍定义，因 e、n 都只须 c-unit。
再用上述五剩余类分离。共同 n 与 e*p 列长 R,S/c，各有原 mu。
两个无 Möbius 的标签现在是固定 residue mod c 的光滑 log 和，不能
直接当无掩码整数和。逐 residue 的 shifted-log 指数对估计给

    |sum_(j=a mod c) psi(j/J) j^(it)|
        <= C sqrt(J*c) |t|^(1/6+eps), |t|>=c0 J.       (CQ7)

可由 [Bourgain Theorem 6 及 §5](https://arxiv.org/pdf/1408.5794) 的 (13/84,55/84)（再放大到1/6）直接推出；
M=J/c 有界时平凡界，M 大时 phase log(m+a/c) 的导数一致。
CQ7 保守放大 residue 计数，足够本范围。全频移 omega 用与 LP11
相同的 1/3 权处理近 t+omega=0；J<=CX，c>=1 使该放大仍成立。
CQ7 也可直接将 LP9–10 的差分证明用于 log(m+a/c)，在
m≈J/c 的支撑远离0，所有导数比较常数统一；部分区间及固定有界 BV
权由分部求和处理。两标签的模 c 掩码不进入 Möbius 列的范数预算。

两标签比 LP 多至多 c，五维 H4 与 12+12+4<=30、双8阶尾不变。
S/c<=S 允许把普通共同时间均值直接放大为 LP 的 RHS。
更明确地，每块以 LP15 的根号 R,S 替成 R,S/c，整体再乘 c^6τ(c)。
原 Mellin 驻相幅度为 (1+X)^(-1/2)，没有额外免费的 T 消去。
|t|<c₀X 和 |t|>C₀X 两尾用平凡标签积和 Mellin IBP，c 的剩余类
限制只减少平凡计数。短 X 时 J_i 固定有界；大 X 相对自然尺度的增长
至多 θ^(1/3)max(1,θ)max(1,θ)^(2ε)，与双八阶衰减绝对可和。
这里的 Fourier 频率权由 H⁴ 支付，不能把所有 ω 当作有界。

故 Principal_c<=A30 c^6 tau(c) T^(10/3-2eta+eps)，仍显式保留原负号
及全部 mask 差项；不是 PT/global principal，也不删除极点。

## CQ6 全原包、允许区域与剩余缺口

合回两个 CRT 分支、所有差项、e 新 principal 和非 principal 后，
对每个 c 有保守界 A30 c^6 tau(c) T^(1+eps)，7/6<=eta<=5/4。
总和 <=A30 Cstar^(7+eps) T^(1+eps)；固定 A 时重命名 eps 得

    |C_(e prime, q=c*p, c<=(log(2T))^A)| <<_(A,eps) A30 T^(1+eps). (CQ8)

不是每条线 Möbius cancellation；是同一个完整线性原包的无条件估计。
没有改动其 EE*,EC*,CE*,CC* 共同能量分账，也不证明跨包能量界。
若 c 是 T 的正幂，当前 c^6 费用不可藏入 eps，结论不能照搬。

当固定 A>0 时新合数域确非空；A=0 则 c=1，只恢复旧素数列。
固定 c=2，Bertrand 取互异 e~Y^6,p~Y^9，q=2p，
S=R=eq、T=(8S)^(1/3)、N=8S，K_z=M_z=sqrtT，H=L=S/sqrtT。
取 prime n in(S,2S)，u=v 选不小于 H/e 的最小奇整数；大 T 时
u<p，(uv,2p)=1，H<=eu<=2H，原 x=3sqrtT/4 给正 y 支撑。
也可取增长 prime c~(log Y)^(A/2)，先 e~Y^6 后选 p~Y^9/c；
则 q~Y^9，所有比较常数仍固定，选 u 避 c 即可。这里只证明整数
支持，非给定核积分非零或密度断言。

其余合数 q、合数 e、其他 canonical/q0、full h/delta、跨AFE/HL尾、
actual amplified 或完整 coupled gate 均未支付。有限检查不能认证
解析大筛/指数对与全部换序；分析证明和有限守卫的证据必须分开。


## CQ7. 与已有预算的比较及有限命题

η=6/5 时，重跑冻结 DP14 于同一包仍给 11/10 上界预算：固定其完整
e/n 容斥因子后，将 e 素数限制留在共同列，将 q=cp 的限制与 μ(q)
留在模数行：固定 DP 导子分解 q=c'ℓ 的 c' 后，它是 β_(c'ℓ) 有界
行标量；c' 是另一个分解参数，不应与本篇 c 混同，数值可能相同。
只在 Cauchy 后的正大筛量里
扩至全部模数。β_q 是有界
行标量，故不从 DP 原 signed 总和直接删项继承。当前 CQ8 则给1，
因此此新合数子族改善1/10；这不是原值下界，不与 LP/DP 的 saving 相乘。
相较 #526，本篇不再限制 bc 短乘积，处理的是未分解前的原完整 μ(n)
线性包；相较 #547，新增 c>1 的合数原模数部分不是其重复，c=1
恢复其素数 q 范围，不将该交集重复计费。

可直接形式化的有限命题包括：CQ1 逐整数 CRT；CQ2 完整双 DFT；
CQ6 三模数互反；五剩余类精确分离；带任意有理复权的有限双 DFT 逆变换；
全部掩码的扩和差；共同列平方预算及每个端点的有理指数不等式。
附脚本保留 c=1、合数非单位频率、两轴、负号和非平方自由 μ(pj) 反例。
离散有限核验不等于解析估计、Lean 证明或最终 main 验收。
