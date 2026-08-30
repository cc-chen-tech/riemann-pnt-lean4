# 完整 h/δ 的顶除数项：接合全部低／高导子

白话结论：本文把新主角色和所有非主角色放回同一完整 h/δ 原核，
支付原 Ramanujan 除数展开的整个 d=q 项，而非再截取一个频带。
在内部平衡 FP3 双整除层，E=T^η、687/550≤η≤5/4 时，该项为
O(D200 T^(1+ε))。门槛只比 5/4 降低 1/1100，改善很小；
η 是 gcd 尺度指数，不是 ζ 零点实部。原 d<q、其余分配及全局尾仍未付。
本文不证明完整 FP3、14/17、2/3 或长 mollifier 渐近式。

English summary: low and high complementary-modulus conductors are estimated
on the same full h/delta packet, including its principal. The entire original
d=q divisor summand is bounded for 687/550≤eta≤5/4. Other original divisor
summands and all global completion requirements remain explicit. This is a
local analytic result, not a Lean theorem or a zero-free-region claim.

## TD1. 冻结来源、对象和主结论

原定义使用 49cfacd70c60372757280177c7b63fd4f7760817 的
docs/research/2026-08-24-mobius-weighted-off-diagonal.md，(2.5)、(4.4)–(4.5)。
精确全 h 格为 PR519 的 614624c83da5bfe41b20a5b1c6f4629d941da806；
CH 分析为 PR529 的 e833305712e4229c2eb141a7d84312f7581f9550；
全 δ 重组为 PR532 的 08f7b664b294cb9649d76223188ed1da7f95eb83；
主角色共同列为 PR536 的 492090fa902b79faf6088678583238ca7d096de6。
这些冻结源不变。下文重新证明全 δ 的高导子适配，不直接搬用旧固定 L 结论。

固定 q₀=1、T≥2、N=T³、R,S≍T³、M,K≍T^(1/2)，
\[
 EQ=S,\quad KS\asymp MR,\quad MK\ll T,\quad E=T^\eta. \tag{TD1}
\]
整个内部 R/S 包保证 n,eq≤N/2，不插入新的二变量硬角点。
n∼R、e∼E、q∼Q，e,q 平方自由，(e,q)=(n,eq)=1；保留原全部
p_N、F_R、F_S、F_M、F_K、W、V_t。q>1；q=1 的原中心化核整体为零。
这里仅 FP3 双整除层，原 h=eu、δ=ev、(uv,q)=1，不是全部 canonical 层。

令 s=eq，定义 FD4 的实际核
\[
 A_m(v)=\frac{F_M(m)F_K(y)}{\sqrt{my}}
       \int W(t/T)V_t(my)(sy/(nm))^{it}\,dt,\quad
 y=(nm+ev)/s,
\]
在 m,y>0 外光滑延零。完整 h 后 m 是正整数；y 不补成整数。
令 B₀=p_N(n)p_N(s)F_R(n)F_S(s)。本文对象为
\[
 S_{\rm top}=2\sum_{e,n,q,m}
 \frac{\mu(e)\mu(n)\mu(q)\,q\,B_0}{\sqrt{ns}\,s}
 \sum_{\substack{v\in\mathbb Z,\ (v,q)=1\\q\mid nm+ev}}A_m(v).
                                                               \tag{TD2}
\]
这是 μ(q)C_q=Σ_{d|(q,nm+ev)}μ(d)d−c_q(m)/φ(q) 的原 d=q 展开项。
它不是从原 centered 和筛选整数元组得到的子族。

定理：在 687/550≤η≤5/4，
\[
 |S_{\rm top}|\ll_\epsilon \mathcal D_{200}T^{1+\epsilon}. \tag{TD3}
\]
D200 是原固定缩放权的 C^200 范数及原 V 的加权混合导数范数之乘积，
按因子出现次数计费，详见 TD7；不假设任何未证 Möbius 平均。

## TD2. 同一个原式上的完整字符分解

置 h=(e,m)、e=ha、m=hz、nm+ev=qk、k=hw。于是
av=qw−nz，且 (v,q)=1 等价于 (m,q)=1。
保留 (h,a)=(a,z)=(n,haq)=(q,haz)=1，不加 (z,h)=1。
此 h 从此表示 gcd(e,m)，不是原 Fourier h。
对单位同余 nz=qw mod a 作完整字符展开，χ_a 在非单位处为零。
定义
\[
 H_{\chi_a}(t)=\sum_{w>0}\overline{\chi_a(w)}
     F_K(w/a)w^{-1/2+it}V_t(hzw/a).
\]
精确有
\[
 S_{\rm top}=2\sum_{h,a,n,q,z}
 \frac{\mu(h)\mu(a)\mu(n)\mu(q)F_M(hz)B_0}
 {h^2a\varphi(a)\sqrt{nqz}}
 \sum_{\chi_a\bmod a}\chi_a(nz)\overline{\chi_a(q)}
 \int W(t/T)(q/(nz))^{it}H_{\chi_a}(t)\,dt.             \tag{TD4}
\]
a=1 的唯一字符保留。固定本 AFE 层的 δ 整数有限，h Fourier 和绝对收敛，
故全 H/L 分割可精确合回；不继承旧 literal 硬壳，也没有 F(|ev|/L)。
投影前 δ=0 会迫使 qw=nz，与 (nz,q)=1、q>1 矛盾。
容斥后单项若出现该点必须保留至完整有符号合计。

每个 χ_a 唯一由 primitive χ mod ℓ 诱导，a=cℓ、(c,ℓ)=1；
ℓ=1 是新主角色。固定 Λ≥2，分别取 ℓ<Λ 和 ℓ≥Λ。
这两个分量确实属于同一个 TD4，边界不重叠。

## TD3. 低导子的精确诱导 Poisson

令
\[
 I_k(t;hz)=\int_0^\infty F_K(y)y^{-1/2+it}V_t(hzy)e(-ky)\,dy.
\]
约定 Fourier 符号 e(−ky)，τ(\barχ)=Σ_{x mod ℓ}\barχ(x)e(x/ℓ)。
先展开 (w,c)=1 的 j|c，再作 primitive Poisson，严格得到
\[
 H_{\chi_a}(t)=a^{-1/2+it}\tau(\bar\chi)\bar\chi(c)
                 \sum_{k\in\mathbb Z}\chi(k)c_c(k)I_k(t;hz). \tag{TD5}
\]
证明中的代换为 w=ju、y=ju/a、k=r c/j；标量
Σ_{j|c,c/j|k}μ(j)/j=c_c(k)/c，
且 χ(r)\barχ(j)=χ(k)\barχ(c)。因此非单位 k 的 c_c(k) 必须保留。
ℓ>1 时 k=0 仅因 χ(0)=0 为零；ℓ=1 的零频另行支付，不能删除主角色。

对 k≠0 令 d=(c,k)、c=db、k=dr₀。平方自由性给
\[
 \frac{\mu(c)c_c(k)}{\varphi(c)}=\frac{\mu(d)}{\varphi(b)},\quad
 \bar\chi(c)\chi(k)=\bar\chi(b)\chi(r_0),\quad(b,k)=1. \tag{TD6}
\]
TD4 的系数于是为 RP4 的相应系数再乘
μ(ℓ)τ(\barχ)/φ(ℓ)，且 a=ℓdb。此 d 不同于原展开的 d=q。

完整展开 (b,nq)=1、(n,q)=1，写
b=flC、n=fjX、q=ljY。得到符号
μ²(f)μ²(l)μ²(C)μ(j)μ(X)μ(Y)，分母 φ(f)φ(l)φ(C)，以及
\[
 (qa/(nz))^{it}=(\ell d l^2CY/(Xz))^{it},\qquad
 \chi(nzr_0)\bar\chi(qb)=\chi(Xzr_0)\bar\chi(l^2CY).   \tag{TD7}
\]
完整掩码为 RP8 的三条再保留 (h,ℓ)=(d,ℓ)=1 及 f,l,j 的 ℓ-unit；
即 f,l,C 平方自由两两互素，(flC,hkzℓ)=1，
(j,flhdzℓ)=1，(X,jflhdℓ)=(Y,jflhdzℓ)=1。
禁止补加 (C,j)、(C,X)、(C,Y)。C 列禁因子 D₀=flhkzℓ
不依赖 X、Y、j；每个固定 ℓ,χ 的 X/Y 时间系数共同。
长度 C_* = E/(hℓdfl)、N₁=R/(fj)、N₂=Q/(lj)、Z=M/h。

## TD4. 扭曲平方自由列：全部平方除数与 AP 成本

设 (κ,λ) 是对数相位的真实指数对，α=λ−κ≥1/2，
δ₁=1−α∈[0,1/2]。在 t∼T、长度 C_* 的固定壳上，
\[
 \left|\sum_{(C,D_0)=1}
 \frac{\mu^2(C)\bar\chi(C)}{\varphi(C)}C^{it}w(C/C_*)\right|
 \ll_\epsilon(C_*\ell TD_0)^\epsilon\|w\|_{\rm BV}
 \left[\ell^{\delta_1}T^\kappa C_*^{-\delta_1}+T^{-1}\right].
                                                               \tag{TD8}
\]
极短空壳为零；有界非空长度用平凡界支付。
[Robert §5.1–5.2，(20)](https://perso.univ-st-etienne.fr/rool6510/robert-2015-indag.pdf)
给壳内任意子区间的 log 相位和 O(T^κ Y^α+Y/T)。
按 ℓ 剩余类拆分 χ，长度变 Y/ℓ、类数至多 ℓ，因而多付 ℓ^(1−α)。
平移后的 log(y+β)（β∈[0,1]）对大 Y 是 log y 的固定小导数扰动；
有界 Y 用 O(1) 平凡界，因此常数对各剩余类一致。

再完整展开 μ²(C)=Σ_{u²|C}μ(u) 与 v|D₀ 单位掩码。
第一项中的 Σu^(−2α) 至多对数；第二项 Σu^(−2) 收敛，不截掉大 u。
用 C/φ(C)=Σ_{s|C}μ²(s)/φ(s) 后，平方自由性保留 (s,C/s)=1；
φ 卷积只需收敛的 Σs τ(s)/(φ(s)s^α)。部分求和支付 1/C 与 BV 权。
这证明 TD8；没有调用未知的原 μ(n) 消去。
D₀ 含无界 k，不能把其 ε 因子无条件写成 T^ε；
在 |k|∼vD 环先抽出 T^ε max(1,v)^ε，再由 TD6 节的尾支付。

## TD5. 完整低导子聚合

余权按 RP9 作共同 C/X/Y 分离，H³ 的 Fourier–Sobolev 预算
支付 C 列的一个 BV 费用；硬的独立整数壳各留在单变量中。
余权不依赖原 t，I_k 只含固定 h,z,k,t。
固定 ℓ,χ 使用任意复系数均值定理，仍为
\[
 \int_T^{2T}|N_X(t)N_Y(t)|\,dt
 \ll T^\epsilon\sqrt{N_1N_2(T+N_1)(T+N_2)}.            \tag{TD9}
\]
来源为 [Vaughan Theorem 26.A](https://personal.science.psu.edu/rcv4/597-5f25/Class597-26.pdf)。
字符零延拓、全部原单位条件和 μ 都保留在系数中。

记 D=T/K。在 |k|≍D 内，计 z∼M/h 和 k/d∼D/d 后，TD8、TD9 前的
物理系数绝对值是
\[
 \frac{\sqrt{TM/K}}
 {hd E^{3/2}\sqrt{RQ}\varphi(f)\varphi(l)}
 \frac{\sqrt\ell}{\varphi(\ell)}.                     \tag{TD10}
\]
主角色取 ℓ=1、τ=1。TD9 展开为 RP14 的四项。
即使再乘 (fl)^δ₁，δ₁≤1/2 保证所有 f/l/j 和至多对数／除数 ε 费。
全部 h≤2M、d≲D 的改进和为
T^κ E^(−δ₁)Σh^(δ₁−1)Σd^(δ₁−1)≪T^ε T^κ(MD/E)^δ₁；
δ₁=0 时用对数和。这次不丢掉大的 hd。

C_* 中含 ℓ，再多一个 ℓ^δ₁；TD8 总计 ℓ^(2δ₁)。
primitive 个数≤φ(ℓ)，所以逐字符取模后的 ℓ 费为 √ℓ，
求 ℓ<Λ 分别得到 Λ^(3/2+2δ₁)、Λ^(3/2)。
在 1≤η≤2，
\[
 |S_{\rm low}|
 \ll\mathcal D_{200}T^{7/2-2\eta+\epsilon}
 \left[T^{\kappa+\delta_1(1-\eta)}
          \Lambda^{3/2+2\delta_1}+T^{-1}\Lambda^{3/2}\right]
       +\mathcal D_{200}T^{9/2-\eta-12}.              \tag{TD11}
\]
这是包括新 principal 在内的完整低导子，而非只含某一 gcd 频带。

## TD6. 零频、负频和无限尾

RP6 的证明在此逐项适用：相位 t log y−2πky 的二阶导数在 y∼K
归一化后为 −t/ξ²，所以 |I_k|≪D200√(K/T)。
|k|∼vD、v≫1 时十二次非驻相积分给额外 v^(−12)。
非空 k=dr₀≠0 的环只有 O(vD/d) 项，不补虚假的 +1。
负 k、小环保留；小环的 v 计数可和。
大环的 h,d 和多付 v^δ₁、计数 v、D₀^ε，仍被 v^(−12) 支付。
所有无穷和均在这些上界下绝对收敛。

ℓ=1、k=0 由十二次 y-IBP 单独给
D200 T^(1−12)√(RQMK/E)Σh h^(−2)
=O(D200 T^(9/2−η−12))。这正是 TD11 末项；
非主角色的 k=0 则由 primitive 零延拓精确为零。

## TD7. 从原 AFE 构造全 δ 的高导子剖面

不能把 CH.1 的固定 L 包直接改名为本对象。
在 H3 归一化 Ω 中取 u=log(qk/(nm))、y=(nm/s)e^u，
原 t=Tv。由 dt=Tdv 精确得到
\[
 \Omega(u;p)=\int_1^2 W(v)\mathcal A(u,p,v)e^{iTvu}\,dv,
\quad
 \mathcal A=\frac{RSM\,p_N(n)p_N(s)F_R(n)F_S(s)F_M(m)F_K(y)}
                  {\sqrt{ns}\,s\sqrt{my}}V_{Tv}(my). \tag{TD12}
\]
p 是四个归一化 e,n,q,m 参数。KS≍MR 使前因子及其固定缩放导数一致有界；
F_K 使 u 在固定紧区间，完整内包使 mollifier 硬边界冗余。
保持 u 为独立变量，原相位 Tvu 不依赖 p。

置 u=s₀/T。对 p 作八阶、s₀ 作二十阶导数，并在 native v 作四十次
分部积分，得到 Ω(s₀/T;p) 的一致 Schwartz 控制。
所需原振幅混合导数不超过 68 阶；八次 Fourier 频率导数只增加 s₀^8 矩。
因此精确 Fourier 反演为
\[
 \Omega(u;p)=\frac1{2\pi T}\int_\mathbb R
                 \mathcal F(p,t'/T)e^{it'u}\,dt',     \tag{TD13}
\]
F 的 t'/T 二十阶衰减及八阶参数导数受原核范数控制。
t' 是新 Mellin 变量，不与 native t 混淆。取 |t'|∼τ 的八次缩放导数后，
仍留十二阶 τ/T 尾，足供 CH8。

原 y∼K 给 w/a∼K，故可插入固定冗余 w/Xw cutoff，
Xw≍EK/h≍RM/(Qh)。CH5–CH9 的字符 Poisson、产品列重组、
primitive hybrid large sieve 和低／高双尾证明遂可在此新剖面上重跑：
\[
 |S_{\rm high}|\ll_\epsilon\mathcal D_{200}T^\epsilon
 \left[T+T^{2-\eta}+T^{5/2-3\eta/2}
                  +T^{7/2-2\eta}/\sqrt\Lambda\right]. \tag{TD14}
\]
具体中间行、全部 h/f/l/c/j 计数及双尾使用冻结 CH5–CH9 各节，
特别是公式 (CH.7)–(CH.10) 及 CH9 的外层求和，
而不是引用其旧包结论。它们只需要 TD13 已重新建立的共同剖面。
同一 Ω 的 off-congruence 光滑延拓用于低／高投影，完整角色和恢复 TD2。

D200 定义为每个原固定缩放因子在固定归一化支持的 C^200 范数加1之乘积，
再乘
\[
 1+\max_{j+k\le200}\sup_{x>0,\ T\le t\le2T}
 (1+x/T)^{200}x^jT^k|\partial_x^j\partial_t^kV_t(x)|.
\]
按出现次数计算两份 p_N。TD5 的共同权分离、TD6 的 F_K/V 积分
各耗不同因子；TD7 的原剖面携带这些原范数，CH Poisson 符号只耗独立
固定冗余 cutoff。故各自最终上界线性依赖 D200，不再平方它。

## TD8. 真实合计及改善幅度

取实际指数对 A⁴B(0,1)=(1/62,57/62)，δ₁=3/31。
令 Λ=max(2,T^z)、z=5−4η。对 687/550≤η≤5/4，
高导子末项指数为 1；低导子第一项指数为
\[
 749/62-(275/31)\eta\le1.                            \tag{TD15}
\]
左端 η=687/550、z=1/275 时，高导子四项指数为
(1,413/550,689/1100,1)，低导子两项为 (1,2/275)，零频更小。
低 ℓ<Λ、高 ℓ≥Λ 严格互补，因此 TD11+TD14 证明 TD3。
固定常数处理 Λ=2 的有界高度端点。

对照只用 RP 的一般系数主角色账，新的完整主角色可单独由 A³B
付到 81/65≤η≤2；但 η=6/5 时，本点态列＋时间均值方法要到 T
需 4κ+λ≤1/2，不能假装已拥有这个猜想端点。
该诊断不是原问题的 no-go，也不否认进一步联合算术抵消。

## TD9. 严格未付部分

TD2 的完整顶项现在包含全部 primitive 导子及 principal；
不再把 #536 的小 hd 带当整 principal。
但原 d<q 项、其他 canonical 分配、q₀ 外壳、非内部尺度、跨 AFE 尾
以及全部 signed gate 仍未由本稿支付。
原校正即使引用 #532 单独支付，也不能抹去原 d<q。
例如 q=d l 时原 (v,l)=1 变为 (dw−nz,l)=1，仍是耦合条件，
不能直接把它当成顶项的独立单位掩码。

这个门槛只比 5/4 小 1/1100；不登记整个 centered FP3 的新 η 门槛。
有限脚本核对 exact Fourier、三次容斥字符相位、完整 low/high 重组及
有理指数，但不替代解析指数对、均值定理、实际权导数或无限尾证明。
