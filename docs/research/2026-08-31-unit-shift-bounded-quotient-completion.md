# 单位位移与有界 h 商：完成 δ 后的全导子、全除数求和

白话结论：当 δ 与右模数 s 互素，而 h 除以 gcd(h,s) 有界时，
可以直接处理任意有限复系数，不必要求它是原 μ 系数。先完成
整个 δ 和，再使用共同 r 列的大筛，最后连同 gcd(h,s) 的全部除数
一起计数，得到一类原 centered 响应的 T^(1+epsilon) 界。
这不是所有 h，不是完整共同投影上界，也不是 14/17 零点定理。

## UC0. 公开定义与对象

本稿仅证明一个原始物理 centered 子域的局部界，不证明完整均方或零点排除。
必需的原核、全阶导数与全部近比例标签证明见同一PR的
[原核附件](2026-08-31-unit-shift-kernel-prelude.md) §KP1–§KP7（公式 KP1–KP14）；
公开定义基线为 562d055b4f481d7dd39db3ef8b91a48eadd56df2 的
[原物理笔记](2026-08-24-mobius-weighted-off-diagonal.md) §2、§4.1、(5.13b)。
附件直接从原AFE重推有限复系数与归一化，不需要未公开研究提交。
本文另证所选 h 子集的远比例尾，不借仅适用于完整 h 和的远尾。

令 T>=2、2<=L_b<=T^3、U0>=1 为固定整数。有限复系数 b 支持
d<=L_b，|b_d|<=B。原系数对是

\[
 C(q_0,r,s)=b_{q_0r}\overline{b_{q_0s}},\qquad(r,s)=1.
 \tag{UC1}
\]

不要求 r 平方自由，也不要求 (q0,rs)=1；不额外乘 μ、p_N 或 marked
素数权。另一 AFE 方向若给共轭系数对，则用同一证明于 bar b。
本文证明只要求这样的共同列/模数标量分离，不适用于任意 C(q0,r,s)。

沿原光滑分割取 r~R、s~S、h~H、δ~V，H,V>=1/2，正负标签分开。
s 平方自由，定义准确整数

\[
 a=(s,|h|),\quad s=aq,\quad h=au,\quad
 0<|u|\le U_0,\quad (u,q)=1,\quad (\delta,s)=1.
 \tag{UC2}
\]

于是 (a,q)=1。另取互不重叠整数 dyadic 壳 a∈[A,2A)、q∈[Q,2Q)，
非空时 AQ~S；只选满足 Q²<=R 的盒。这个选择在外层盒标签作出，
不是给共同 r 列额外附加随 q 变化的硬截断 q²<=r。
r、s 的原光滑分割保留；a、q 壳分别只限制固定外变量与模数标量。
系数支撑 q0r,q0aq<=L_b 也分别只依赖 r 与 q。

本文选定和是原 (4.4)–(4.5) 的 centered 和插入上述选择及分割后，
对所有 q0,R,S,A,Q,H,V、原 AFE 长度及非零 h,δ 求和。q=1 的
centered 括号精确为0，不能据此把原非 centered principal 删除。

## UC1. 近比例包的准确相位、权和目标

对近比例 AFE 长度 M,K，即 1/64<=KS/(MR)<=64，附件公式 KP8–KP9 给原四变量
光滑核 Ψ，其 C^30 范数记 A30。完整包恰为

\[
 {2T\over q_0RS}\sum_{
 \substack{r,a,q,u,\delta\ne0\text{ satisfying UC2}\\
 r\asymp R,\ a\sim A,\ q\sim Q}}
 b_{q_0r}\overline{b_{q_0aq}}
 \Psi(r/R,aq/S,\delta/V,au/H)
 \left\{e_q(-u\delta\bar r)-{\mu(q)\over\varphi(q)}\right\}.
 \tag{UC3}
\]

其中 (r,aq)=1、a,q 平方自由等掩码全在求和中。相位由
e_s(-hδ rbar)=e_q(-uδ rbar) 得到；(δ,s)=1 及 (u,q)=1 使
c_s(hδ)/φ(s)=μ(q)/φ(q)。唯一前因子为 2T/(q0RS)，不是再除一次 S。

要证的包界为

\[
 |\mathrm{UC3}|\ll_{U_0,\epsilon}
       B^2 A_{30}\,{T^{1+\epsilon}\over q_0},\qquad Q^2\le R.
 \tag{UC4}
\]

该界对所有 V>=1/2 一致，没有先假定 H=V 或 HL<=RS/T。
H 仅通过 au/H 落在固定支撑和 u 的有限个数出现。

在固定四维紧盒外作光滑延拓和 Fourier 分离。若 δ 模式为 ξ，
加权 Fourier 系数的 ℓ¹ 范数（权 (1+|ξ|)^10）由 C^16 范数控制：
四维积分分部积分16次给 (1+|ν|)^(-16)，乘十次权仍绝对可和。
每个分离项的 δ 权为 f(t)=f0(t)e(ξt)，f0 紧支离0，且
||f||_(C^10)<=C(1+|ξ|)^10。固定 a,u 后第四坐标权只是标量；
第二坐标 Fourier 权及 b_(q0aq) 同属模数标量，不进入 r 列。
以下证明对每个分离项成立后，再以这个绝对预算重组。

## UC2. 全导子与所有交叉单位掩码

对 q 单位 x，精确有

\[
 e_q(x)-{\mu(q)\over\varphi(q)}
 ={1\over\varphi(q)}\sum_{\chi\bmod q,\ \chi\ne\chi_0}
                         \tau_q(\bar\chi)\chi(x).
 \tag{UC5}
\]

写 q=cℓ，ℓ>1 为 χ 的 primitive conductor。因 q 平方自由，
(c,ℓ)=1，所有 c、ℓ 都必须保留；不只留下最高导子。精确 Gauss 式

\[
 \tau_{c\ell}(\bar\chi_{\rm ind})
       =\mu(c)\bar\chi(c)\tau_\ell(\bar\chi)
 \tag{UC6}
\]

中 χ 从此表示 primitive 模 ℓ 字符。固定 a,c 后，r 列是
α_r=b_(q0r)×原 r 权×1_(r,ac)=1，所有 ℓ-unit 由 barχ(r) 的零延拓
提供。这一列对变化的 ℓ 共同。限制 (a,cℓ)=1、q 壳及 q0acℓ<=L_b
留在模数标量 β_ℓ 中，|β_ℓ|<=B。u 的 (u,cℓ)=1 也留在标量中。

δ 的全部剩余单位条件是 (δ,ac)=1，故必须展开

\[
 1_{(\delta,ac)=1}=\sum_{d\mid ac,\ d\mid\delta}\mu(d),
 \quad d=d_a d_c,\quad d_a\mid a,\ d_c\mid c.
 \tag{UC7}
\]

这里 (a,c)=1，且 d 与 ℓ 互素。不能漏掉 d_a，也没有 (δ,r)=1
可供擅自添加。置 δ=dm；原 f 支撑离0，所以写全 m∈Z 不添加 δ=0。
对约定 fhat(y)=∫f(t)e(-yt)dt，普通 Poisson 和 primitive Gauss 给

\[
 \sum_{m\in\mathbb Z}\chi(m)f(dm/V)
 ={V\tau_\ell(\chi)\over d\ell}
   \sum_{k\in\mathbb Z}\bar\chi(k)
                               \widehat f(kV/(d\ell)).
 \tag{UC8}
\]

ℓ>1 primitive 非主字符，barχ(0)=0，故 k=0 精确不存在。
不假定奇字符，也不从普通剩余类权错误排除偶 k。
τ(χ)τ(barχ)=χ(-1)ℓ；它与 χ(-ud) 合并为 χ(ud)ℓ。因此固定
a,c,d,u 的变换后项准确带因子

\[
 {\mu(c)\mu(d)V\over d\varphi(c)}
 \sum_{\ell\asymp Q/c}{\beta_\ell\over\varphi(\ell)}
 \sum_{\chi\ ({\rm primitive}\bmod\ell)}
 \bar\chi(c)\chi(ud)
 \left(\sum_r\alpha_r\bar\chi(r)\right)
 \left(\sum_{k\ne0}\bar\chi(k)\widehat f(kV/(d\ell))\right).
 \tag{UC9}
\]

φ(c) 与 φ(ℓ) 都保留；Gauss 乘积正好支付 Poisson 的 ℓ。
没有再保留 √ℓ，也没有生成第二笔 1/q 或 1/s 收益。

## UC3. 非零对偶频率的全尾及共同列大筛

记 ℒ=Q/c（非空时 ℒ>1/2），K0=dℒ/V。对 k≠0 分正负 dyadic
壳 |k|~D，D>=1/2。Fourier 变换快速衰减及至多四次归一化微分给
二变量权 fhat(kV/(dℓ)) 的 C^4 范数

\[
 \ll \|f\|_{C^{10}}(1+D/K_0)^{-6}.
 \tag{UC10}
\]

证明是先对变换频率微分 j<=4（插入 t^j），再在 t 上分部积分
6+j 次，配合归一化导数产生的至多 j 次频率幂；最高只需10阶。
固定支撑的二维 Fourier ℓ¹ 分离由 C^4 控制，故分离后的 k 列对 ℓ
共同，模数 Fourier 权留在 β_ℓ。其全部尾仍带 UC10 的因子。

使用 primitive 乘法大筛

\[
 \sum_{\ell\le Q_1}{\ell\over\varphi(\ell)}
 \sum_{\chi\ ({\rm primitive}\bmod\ell)}
 \left|\sum_{M<n\le M+N}a_n\chi(n)\right|^2
 \le (Q_1^2+N-1)\sum|a_n|^2.
 \tag{UC11}
\]

输入及常数见 [Bombieri–Davenport, Theorem 16.2](https://kskedlaya.org/ant/chap-largesieve2.html)。
这是由 primitive
Gauss 展开、字符正交和加性大筛得到的均方定理，不是假定新谱一阶矩。
r 能量<=CB²R，k 壳能量<=CD，且 ℒ²<=Q²<=R。Cauchy 后 r 因子
<=CBR；k 因子<=C√((D+ℒ²)D)。原 1/φ(ℓ) 写为
(ℓ/φ(ℓ))/ℓ，只贡献一次 ℒ^(-1)。再付 |β_ℓ|<=B，得到

\[
 |\mathrm{UC9}|\ll {B^2 A_{30} VR\over d\varphi(c)}
  \sum_{D\ge1/2\ \mathrm{dyadic}}
       (\sqrt D+D/\mathcal L)(1+D/K_0)^{-6}.
 \tag{UC12}
\]

完整无限 dyadic 和满足

\[
 \sum_D(\sqrt D+D/\mathcal L)(1+D/K_0)^{-6}
 \ll(\sqrt {K_0}+K_0/\mathcal L)\min(1,K_0^2).
 \tag{UC13}
\]

K0>=1 时在 D=K0 两侧分别几何求和。K0<1 时 D>=1/2，左边
<=C K0^6(1+ℒ^(-1))，小于右边的固定常数倍。这一步不可丢掉
非零最小频率，尤其 V≫dℒ 时的 K0² 衰减必须保留。
故固定 a,c,d,u 的完整费用是

\[
 {B^2 A_{30}R\over\varphi(c)}
 \left(\sqrt{V\mathcal L/d}+1\right)
                  \min(1,(d\mathcal L/V)^2).
 \tag{UC14}
\]

## UC4. 所有 a 行、两侧 d 及 c 的合计

固定 c,d_c，令 D0=V/(d_cℒ)。对 a∈[A,2A)，d_a|a 的行数
<=2A/d_a。对全部 D0>0，有

\[
 \sum_{j\ge1}j^{-3/2}\min(1,(j/D_0)^2)\ll D_0^{-1/2}.
 \tag{UC15}
\]

D0>=1 时在 j=D0 分开，前段 D0^(-2)Σj^(1/2) 和后段
Σj^(-3/2) 均为 O(D0^(-1/2))；D0<1 时由收敛级数立即得到。
把 UC14 的根号项连同全部 a,d_a 合计，准确为

\[
 {R\sqrt{V\mathcal L}\over\varphi(c)\sqrt{d_c}}
       O(A D_0^{-1/2})
       =O\left({RA\mathcal L\over\varphi(c)}\right).
 \tag{UC16}
\]

此处已付 d_a 的真实行数，不以逐 a 的 τ(a) 上界代替这个求和。
再求 d_c|c 和 c<=2Q，根号项总和至多
RAQ Σ_c τ(c)/(cφ(c))=O(RAQ)。该级数收敛：对任意 ε<1/4，
τ(c)c/φ(c)<<ε c^(2ε)，故被 c^(-2+2ε) 控制。
UC14 的常数项则用
Σ_aΣ_(d_a|a)1<=2AΣ_(j<=2A)1/j；再求 c,d_c 得
Oε(RA T^ε)。这里 a,c<=L_b<=T³，
Σ_(c<=2Q)τ(c)/φ(c)<<ε Q^ε，所有小 epsilon 可预先缩小。

乘回唯一 2T/(q0RS)，利用 AQ~S、Q>=1，并合计至多2U0个 u，
证明 UC4。上述 τ 和 φ 的初等 ε 界可逐素数证明：大素数处每个
局部因子被 p^(εv) 控制，小素数的有限乘积由常数支付。
没有使用 b 的乘法性、原 μ 的 Type 恒等式或额外 marked 预算。

## UC5. 全部近比例 AFE 和 h、δ 标签

附件公式 KP11 在 m=30、两个衰减阶8时给

\[
 A_{30}\ll S_{154}(W)
 (1+TV/(MR))^{-8}(1+HM/S)^{-8}(1+M^2R/(ST))^{-C}.
 \tag{UC17}
\]

每个 M 只有 O(1) 个近比例 K。附件公式 KP13 给所有 M∈2^Z、
H,V∈2^(Z_{>=-1}) 的和 O([1+log(2+RS/T)]³)。UC4 不含额外 V、H
幂，所以直接适用。a 的有限 dyadic 壳、r,s,Q 壳总计 O(log^4T)，
q0 的 1/q0 和为 O(log T)，可吸入 epsilon。
u 有界使非空 A~H/|u|，但不必利用这个更强限制。

这给全部所选近比例部分 << B² S154(W)T^(1+ε)。自然对偶 K0 的
正部至多固定 T 幂，因为 d<=ac<=s<=L_b、ℒ<=2L_b、V>=1/2；
无限 k 尾已在 UC13 支付，不把它隐藏到 T^ε 常数里。

## UC6. 所选 h 子集的独立远比例证明

现在 KS/(MR) 不在 [1/64,64]。不用 whole-h Poisson。
固定 r,s,M,K，原连续变量 x~M、y=(rx+δ)/s~K。原核是

\[
 \widehat F_\delta(h/s)=\int {F_M(x)F_K(y)\over\sqrt{xy}}
 \int W(t/T)V_t(xy)e^{it\log(ys/(xr))}\,dt\ e(-hx/s)\,dx.
 \tag{UC18}
\]

在实际支撑（固定分割常数如附件 §KP0、§KP4）上，远比例给
|log(ys/(xr))|>=c(1+|log(Ks/(Mr))|)。按 t 分部积分 J 次并用
附件公式 KP3，内积分的绝对值至多
CS_J(W)T^(1-J)(1+MK/T)^(-A)(1+|log(Ks/(Mr))|)^(-J)。
h 相位模长1；此步对任意所选 δ 子集亦成立。

要控制所有非零整数 δ 的 x 支撑测度，注意 δ 位于长度
O(rM+sK) 的区间内，单个 x 交集长度<=C min(M,sK/r)。若某一
非零 δ 行非空，则 |δ|<=C(rM+sK) 强制 rM+sK>=c。因此

\[
 \sum_{\delta\ne0}\operatorname{meas}\{x\asymp M:
                         (rx+\delta)/s\asymp K\}
 \ll (rM+sK)\min(M,sK/r)\ll sMK.
 \tag{UC19}
\]

若 rM+sK<c 而无非零行，左边为0。这同时处理任意小的 M,K，
不能在计数中保留一个未支付的孤立 +1。
结合 1/√(xy)<=C/√(MK)，得 sumδ |hatF| 不超过
CS_J(W)T^(1-J)s√(MK)(1+MK/T)^(-A)(1+|log(Ks/(Mr))|)^(-J)。

对 product v=MK 和 log-ratio 分别求完整 dyadic 格：J>1 时 ratio
和一致有界（固定 r/s 只平移格）；A>1/2 时
Σ_v √v(1+v/T)^(-A)<<√T。格的奇偶约束只减少正和。于是

\[
 \sum_{M,K\ \mathrm{far}}\sum_{\delta\ne0}|\widehat F_\delta(h/s)|
 \ll S_J(W)sT^{3/2-J},
 \tag{UC20}
\]

右边不依赖 h。每个 s 允许的 h=au 至多 2U0τ(s) 个，所有 H 的
光滑分割具有固定绝对重叠。centered 括号模长<=2。乘回原
2/(q0√(rs)s)，再求 q0r,q0s<=L_b，利用
Σ_(n<=X)τ(n)/√n<<√X log(2X)、Σ_(n<=X)n^(-1/2)<<√X，得远比例总和

\[
 \ll_{U_0,\epsilon} B^2S_J(W)L_bT^{3/2-J+\epsilon}
 \le C B^2S_J(W)T^{9/2-J+\epsilon}.
 \tag{UC21}
\]

故任意指定负幂都由固定有限 J 支付。此证明不从仅适用于全部 h
的远尾或大 gcd 上界中删除子集。

## UC7. 完整所选域与剩余义务

由 UC17、UC21，存在固定有限 J_ε（近比例至少154）使本文 UC2
及 Q²<=R 所定义的整个原 centered 和满足

\[
 |\mathcal C_{\rm UC}(b)|
       \ll_{U_0,\epsilon} B^2 S_{J_\epsilon}(W)T^{1+\epsilon},
 \qquad 2\le L_b\le T^3.
 \tag{UC22}
\]

该界适用于最初给定的同一个有限 b；所有 q0、非平方自由 r、
任意 q0 公因子、复共轭方向及非零正负 δ,h 都如上保留。
s 的非平方自由赋值未覆盖。完整所选局部极限由附件 §KP7 与
本文 UC18–21 支付，不据此宣称全局 D+J+C 的三个分项各别收敛。

本次不包含特定投影系数的额外 Q_P/P 预算、到完整输出能量的范数
转移或具体零点见证应用。任意有限 b 的 UC22 本身无需这些输入，
但若要将其用于一个指定的零点排除方案，必须另证这些应用依赖。

仍未支付：无界 |h|/(s,|h|)、Q²>R 的盒、非平方自由 s，以及
允许固定 T 而系数长度超过 T³ 的低高度问题和其余完整补集。
即使另有全 h 的大 gcd 子集上界，也不能直接从两个 whole 子集
上界推出交集或差集上界；重排为互不重叠的完整总账仍需单独证明。
不把局部上界当成完整共同投影上界，更不是 Carlson 零点计数下界。

本篇纸面估计只处理上述原物理子域。有限字符/计数测试不是解析
尾部证明，局部审阅、PR及其测试均不等于 Lean 或零点定理验收。
没有给出 T0，没有证明高高度或全高度 14/17，不能以本稿宣布闭合。
