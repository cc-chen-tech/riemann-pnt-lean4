# 完整 h/δ 后的新主角色：小 reciprocal-gcd 频带

白话结论：把原 h、δ 分割合回去后，原除数展开的 d=q 项还会产生一个
新模数的主角色。本文只支付这个新主角色的一部分频率：
在 E=T^(6/5) 时，(e,mr)≤T^(2/3) 的非零 Poisson 频带为 O(T^(1+ε))。
大 gcd 补集、非主角色和原 d<q 项仍保留；这不是整个主角色的上界，
更不是 14/17、2/3 零点排除。结果不与固定 L 包的节省直接相乘。

English summary: a reciprocal-gcd band of the new complementary-modulus
principal is bounded after full h/delta reassembly. At E=T^(6/5), the nonzero
band gcd(e,mr)≤T^(2/3) costs O(T^(1+epsilon)). The complementary band and all
other character/divisor sectors remain unestimated here. No Lean claim is made.

## RP1. 来源、原包与命题

定义源为 49cfacd70c60372757280177c7b63fd4f7760817 的
docs/research/2026-08-24-mobius-weighted-off-diagonal.md，(2.5)、(4.4)–(4.5)。
全 h 格使用 PR519 冻结 614624c83da5bfe41b20a5b1c6f4629d941da806；
互补模数使用 PR529 冻结 e833305712e4229c2eb141a7d84312f7581f9550。
全 δ 的精确重组使用 PR532 冻结 08f7b664b294cb9649d76223188ed1da7f95eb83
中 FD1–FD5。本文不修改这些冻结结果。

固定 q₀=1、T≥2、N=T³，整个内部 AFE 包满足
\[
 R,S\asymp T^3,\quad M,K\asymp T^{1/2},\quad EQ=S,\quad
 KS\asymp MR,\quad MK\ll T,\quad E=T^\eta,\quad1\le\eta\le5/2. \tag{RP1}
\]
比较常数固定；R/S 包的完整支持保证 n,eq≤N/2，不能另加二变量硬角点。
保留原 p_N、F_R、F_S、F_M、F_K、W、V_t，及独立的 e∼E、q∼Q 壳。
这里是 FP3 双整除层：e、q 平方自由，(e,q)=(n,eq)=1，
原 h=eu、δ=ev，(uv,q)=1。全 h 后 m∼M 是正整数，不预设平方自由。
以下只含 q>1；q=1 的原中心化核整体为零。

令 P 为 RP3 定义的新模 a 主角色。对非零 Poisson 频率 r，定义
P_{\le G} 为其中 (e,mr)≤G 的精确线性频率投影，G≥1。则
\[
 |P_{\le G}|\ll_\epsilon \mathcal D_{40}T^\epsilon
 \frac{\sqrt{RQ\,M/K}\sqrt T}{E^{3/2}}
 \left(1+\sqrt{T/Q}+\sqrt{T/R}+\frac{T}{\sqrt{RQ}}\right)
 \left(T^{1/6}\sqrt{G/E}+T^{-1}\right).                 \tag{RP2}
\]
此处 G 可限制在固定常数倍 T 内；更高 r 尾仍完整保留。
特别 η=6/5、G=T^(2/3) 时，两项主指数分别为 1、1/10。

## RP2. 完整重组与新主角色的准确外权

由 FD2，固定本 AFE 层时 |δ|≲RM+SK，δ 整数有限；对每个 δ，
原光滑 x 核的 h Fourier 和绝对收敛。因此可精确合回所有 H/L 分割。
本包中不再有 F(|ev|/L)，也不继承旧 literal 硬 H/L 壳。
这不授予跨全部 AFE 尺度的统一换序或尾界。

全 h 核在外 μ(q) 融合后为
\[
 \mu(q)C_q=\sum_{d\mid(q,nm+ev)}\mu(d)d-c_q(m)/\varphi(q).
\]
本稿只保留原 d=q 项，系数仍为 μ(q)q。其同余和 (v,q)=1
迫使 (m,q)=1。置
\[
 h=(e,m),\quad e=ha,\quad m=hz,\quad k=hw,\qquad av=qw-nz.
\]
从此 h 是 gcd(e,m)，不是原 Fourier h。
有 (h,a)=(a,z)=(n,haq)=(q,haz)=1，不加 (z,h)=1。
对单位同余 nz=qw mod a 作完整字符展开；其主角色保留
1/φ(a) 与 (w,a)=1。所得精确表达式是
\[
 P=2\sum_{h,a,n,q,z}
 \frac{\mu(h)\mu(a)\mu(n)\mu(q)\,F_M(hz)
       p_N(n)p_N(haq)F_R(n)F_S(haq)}
      {h^2a\varphi(a)\sqrt{nqz}}
 \int W(t/T)\left(\frac q{nz}\right)^{it}
 \sum_{\substack{w>0\\(w,a)=1}}
 F_K(w/a)w^{-1/2+it}V_t(hzw/a)\,dt.                    \tag{RP3}
\]
h,a,q 平方自由；a=1 的唯一字符也保留。原 v=0 对应 qw=nz，
但 (nz,q)=1、q>1 排除该点，故此投影不引入遗漏的原 δ=0。
后续容斥单项可能出现该点，必须保留到完整有符号合计，不能逐项删除。
P 不是 FD6 的原校正，也不是 PT 全 D+J_Ram 的直接子项估计。

## RP3. 单位 Poisson 与频带定义

约定 e(x)=exp(2πix)，Fourier 核为 e(−ry)。定义
\[
 I_r(t;hz)=\int_0^\infty F_K(y)y^{-1/2+it}V_t(hzy)e(-ry)\,dy.
\]
w 单位格的 Poisson 公式含 a^(−1/2+it)c_a(r)，所以
\[
 P=2\sum_{h,a,n,q,z,r}
 \frac{\mu(h)\mu(n)\mu(q)\,[\mu(a)c_a(r)/\varphi(a)]
       F_M(hz)p_N(n)p_N(haq)F_R(n)F_S(haq)}
      {h^2a^{3/2}\sqrt{nqz}}
 \int W(t/T)\left(\frac{qa}{nz}\right)^{it}I_r(t;hz)\,dt. \tag{RP4}
\]
r 遍历全部整数。对 r≠0，置 d=(a,r)、a=db；平方自由性给
\[
 \frac{\mu(a)c_a(r)}{\varphi(a)}=\frac{\mu(d)}{\varphi(b)},\quad
 (b,r)=1,\quad(h,d)=(d,z)=1,\quad hd=(e,mr).            \tag{RP5}
\]
此 d 与 RP2 的原除数 d=q 不同。RP2 的频带就是 RP4 中 r≠0、hd≤G；
未选频带不变。它也不同于三坐标 Fourier 的 gcd(q,k,ρ,σ) 投影。

## RP4. 真实权半范数及全部 Poisson 尾

令 \(\mathcal D_{40}\) 控制如下有限量之乘积：W 的 C^40 范数；
所有上述固定缩放截断（包括内部 p_N）在固定归一化支持上的 C^40 范数；
以及
\[
 1+\max_{j+k\le40}\sup_{\substack{x>0\\T\le t\le2T}}
 (1+x/T)^{40}x^jT^k|\partial_x^j\partial_t^kV_t(x)|.
\]
每种因子的范数先加 1，并按原核中的出现次数取乘积：
p_N(n)、p_N(haq) 各计一次。原定义源 (2.5) 保证一致有界。
这是原核的半范数预算，不是对已经产生的振荡 c^(it) 再求导。
下文以 D40 粗记各步控制量，但实际分账为：I_r 只消耗 F_K、V 的预算，
三变量分离只消耗 F_R、F_S 与两份 p_N；外部 W、F_M 各消耗一次。
因而接合各步时总乘积仍由 D40 控制，不额外再乘一份 D40。

置 D=T/K。缩放 y=Kξ 后，振幅大小 √K，主相位为
t log ξ−2πrKξ，其二阶导数在 ξ 的固定正紧区间为 −t/ξ²。
故所有 r 一致有 |I_r|≪D40√(K/T)。
若 |r|∼sD 且 s 足够大，一阶导数 ≍|r|K，反复积分给
\[
 |I_r|\ll_J\mathcal D_{40}\sqrt{K/T}\,s^{-J},\qquad J\le12. \tag{RP6}
\]
负 r 和小 r 的非驻相也保留。非空的 r=d r₀≠0 环，
计数为 O(sD/d)，而不是需要额外付费的 O(sD/d+1)。
小环 s≤O(1) 的 O(s) 因子可和；大环取 J=12 支付
全部频率数、后面的除数 ε 因子和无限尾。

r=0 不使用 RP5 的频带估计。此时 c_a(0)/φ(a)=1，
y-IBP 给 |I₀|≪D40√K T^(−J)，直接完整计数得
\[
 |P_{r=0}|\ll_J\mathcal D_{40}T^{1-J}
       \sqrt{RQMK/E}\sum_{h\le2M}h^{-2}
 \ll\mathcal D_{40}T^{9/2-\eta-J}.                    \tag{RP7}
\]
J=12 足够。这是单独支付零频，不是把主角色删除。

## RP5. 三次完整容斥：共同列的必要步骤

RP5 后 b 的单位条件为 (b,hrz)=1、(b,nq)=1；另有 (n,q)=1。
先展开 f|(b,n)、l|(b,q)。因 (n,q)=1 可限 (f,l)=1。
令 b=flc、n=fx、q=ly，再完整展开 (x,y)=1 的 j，写 x=jX、y=jY。
平方自由及原互素条件逐项化为
\[
 \frac{\mu^2(f)\mu^2(l)\mu^2(c)\mu(j)\mu(X)\mu(Y)}
      {\varphi(f)\varphi(l)\varphi(c)},\qquad
 \left(\frac{qa}{nz}\right)^{it}
       =\left(\frac{d\,l^2cY}{Xz}\right)^{it}.         \tag{RP8}
\]
固定掩码完整列表如下：

- f,l,c 平方自由、两两互素，(flc,hrz)=1；
- j 平方自由，(j,flhdz)=1；
- (X,jflhd)=1，(Y,jflhdz)=1。

固定 f,l 的原 h,d,z 条件已包含在第一条，因为 d|r。
不加 (c,j)、(c,X) 或 (c,Y)！例如原 (b,n,q)=(2,2,2) 的
有符号容斥若误加 (c,j)=1 就不能恢复零。
c 列禁因子恰可取 D₀=flhrz，与 X、Y、j 无关。

长度为 C=E/(hdfl)、N₁=R/(fj)、N₂=Q/(lj)、Z=M/h。
非空正整数壳的长度参数至少为某个固定正常数，否则该壳为空。
所有 f,l,j 范围完整保留。余权 p_N(haq)F_S(haq) 是归一化 c、Y
的联合光滑函数，R 权属于 X。在固定外紧区间上以三维 Fourier 分离；
Sobolev–Cauchy 给
\[
 \sum_{\nu\in\mathbb Z^3}|\widehat w(\nu)|(1+|\nu_c|)
 \ll \|w\|_{H^3}\ll\mathcal D_{40}.                   \tag{RP9}
\]
理由为 3>3/2+1；硬的独立 e/q/n 壳在固定外参数后成为各自单变量区间，
保留在各列，不冒充光滑函数。c 列的一个 BV 费用由 RP9 支付。
三个 Fourier 列的系数不依赖 t；I_r 只依赖已固定的 h,z,r,t。
内包支持使原 mollifier 硬角点冗余。

## RP6. 平方自由 reciprocal-φ 对数扭曲引理

对任意 C≥1/2、正整数 D₀、t∈[T,2T] 及固定壳上 BV 权 w，
\[
 \left|\sum_{\substack{c\sim C\\(c,D_0)=1}}
 \frac{\mu^2(c)}{\varphi(c)}c^{it}w(c/C)\right|
 \ll_\epsilon(CTD_0)^\epsilon\|w\|_{\rm BV}
 \min\{1,C^{-1/2}T^{1/6}+T^{-1}\}.                    \tag{RP10}
\]
使用 [Robert §5.1–5.2，式 (20)](https://perso.univ-st-etienne.fr/rool6510/robert-2015-indag.pdf)
对 g₀(x)=log x 的指数对 AB(0,1)=(1/6,2/3)，壳内任意子区间有
\[
 \left|\sum_{y\in J\subset[Y,2Y]}y^{it}\right|
 \ll T^{1/6}\sqrt Y+Y/T.                              \tag{RP11}
\]
任意固定比例壳可切成常数个这种区间；极短非空区间可直接用平凡界。

先去掉 1/φ：μ²(c)=Σ_{u²|c}μ(u)，并用 v|D₀ 完整展开单位掩码。
写 c=u²vy，RP11 第一项求和为
T^(1/6)√C Σ_{u≤√(2C)}u^(−1) Σ_{v|D₀}v^(−1/2)；
第二项至多 (C/T)Σu^(−2)Σ_{v|D₀}v^(−1)。
因此完整平方除数和为
O((CTD₀)^ε[√C T^(1/6)+C/T])，没有截掉大 u。

再用 c/φ(c)=Σ_{s|c}μ²(s)/φ(s)，令 c=sa；平方自由性要求 (s,a)=1。
对长度 C/s、禁因子 D₀s 应用刚才的界，然后分部求和支付 1/c 与 BV 权。
出现的 Σ_s τ(s)/(φ(s)√s)、Σ_s τ(s)/(φ(s)s) 收敛；
小 ε 的 s^ε 也仍可和。结合平凡的 dyadic reciprocal-φ 质量得 RP10。
这里使用的是精确重组后真实出现的 μ²(c)，不是原 μ(n) 的抵消假设。

## RP7. 时间均值与所有除数层结账

RP8 后，c 列可逐 t 用 RP10，剩下 X、Y 系数确实共同。
由任意复系数 Dirichlet 多项式均值定理与一次 Cauchy，
\[
 \int_T^{2T}|N_X(t)N_Y(t)|dt
 \ll_\epsilon T^\epsilon
 \sqrt{N_1N_2(T+N_1)(T+N_2)}.                         \tag{RP12}
\]
这里使用 [Vaughan 讲义 Theorem 26.A](https://personal.science.psu.edu/rcv4/597-5f25/Class597-26.pdf)；
系数的单位掩码、μ 和独立区间均保留，长度小于 T 不另假设。

固定 h,d,f,l,j，在 |r|≍D 区先计 z∼M/h、r/d≍D/d。
RP4 的唯一物理外权、RP6 与这两个计数给 RP10、RP12 前的系数
\[
 \frac{\sqrt{K/T}(M/h)(D/d)}
 {h^2(E/h)^{3/2}\sqrt{RQ\,M/h}\,\varphi(f)\varphi(l)}
 =\frac{\sqrt{TM/K}}
 {hd\,E^{3/2}\sqrt{RQ}\,\varphi(f)\varphi(l)}.          \tag{RP13}
\]
RP12 的平方根由以下四项之和控制：
\[
 \frac{RQ}{flj^2},\
 \frac{\sqrt T R\sqrt Q}{f\sqrt l\,j^{3/2}},\
 \frac{\sqrt T\sqrt R Q}{\sqrt f\,l j^{3/2}},\
 \frac{T\sqrt{RQ}}{\sqrt{fl}\,j}.                     \tag{RP14}
\]
乘 1/(φ(f)φ(l)) 以及 RP10 第一项引入的 √(fl)，所有 f,l,j 和
至多对数/除数 ε 成本；最差指数为 1，不遗漏大 f 或大 l。
例如第一项的 f,l 幂各为 −3/2，第四项各为 −1；
第一项的 j 幂 −2，第四项 −1。第二/三项也同样可和。

剩余 h,d 平凡费用为 1/(hd)；改进项为
T^(1/6)/(√E√(hd))。于是
\[
 \sum_{hd\le G}(hd)^{-1}\ll\log^2(2G),\qquad
 \sum_{hd\le G}(hd)^{-1/2}\ll\sqrt G\log(2G).
\]
原 h,d 互素或支持只能减少这些正上界。结合 RP13–RP14 得 RP2。
对 |r|∼sD 的其余环，系数多一个 s，RP6 给 s^(−12)，
足够吸收 D₀ 含 r 的 ε 因子；全部无穷尾在取绝对值后仍收敛。

## RP8. 真正的新范围与未付部分

η≤2 时 R,Q≥常数倍 T，RP2 的基本指数为 7/2−2η。
若 G=T^γ，两项指数为
\[
 11/3-5\eta/2+\gamma/2,\qquad 5/2-2\eta.              \tag{RP15}
\]
η=6/5、γ=2/3 给 (1,1/10)；不作 RP10 改进的同频带一般费用为 11/10。
所以本频带新增 1/10 的幂次节省。若把自然 hd 尺度扩大到 G≍T，
第一项变为 7/6，不能宣称整个主角色已支付；
该处可保留旧平凡界与新界的较小值，而不是称原问题出现反例。

本稿不控制：

- 新主角色的 (e,mr)>G 非零频带；
- 新模 a 的非主角色以及原 Ramanujan 展开的 d<q 项；
- 其余 canonical 分配、q₀ 外壳、全部 AFE 尺度及跨 AFE 尾；
- 完整中心化算子、最终 14/17 或 2/3。

PR529 的 CH.1 是固定 L 包，RP2 是全 δ 主角色，不能未经同一包的
重组与补集验证直接相加为全和。PR532 支付的是不同的原校正；
它与本稿也不组成完整原 d=q 或全算子的证明。

有限脚本只检查外权、Ramanujan 比值、完整三次容斥、掩码反例、
有理指数与范围门禁；它不代替 RP6–RP7 的解析证明，也不是 Lean 验证。
