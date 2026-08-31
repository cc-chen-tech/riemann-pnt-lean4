# 真实 FP3 层的产品标签 L²：保留全部拥挤费用

白话结论：在 #505 已审的同一双整除 gcd 层里，不逐个 u,v 取绝对值，
而先估计完整标签和的中心化 Type 核。不同标签的乘积 uv 的重合次数
只需整数除数函数控制。这样在平衡内部尺度上，局部 T 预算的充分
区域从 E≥T^(7/3) 扩大到 E≥T²；E=T^(9/4) 的真实非空例子为
O(T^(7/8+ε))。这是一个指定原式子族的上界，不是整个 off-diagonal
或 14/17、2/3 零点排除；也没有证明新的 Möbius 符号抵消。

唯一对象仍是冻结 #505（commit
`5b98572f27695b2404d290be3dfcda8274f20285`）的
[D1–D2 原 FP3 层](2026-08-31-physical-squarefree-type-descent.md)。
它继承 MWKF-PHYS-v1 的固定 Ψ、支持、半范数及物理外权。本篇不改
#490/#503/#505 的冻结版本，不引入 canonical a/b/e 推广、reciprocity
或 q₀ 壳扩展。所有公式都只固定一个原平方自由 q₀。

## 1. 先固定真实共同原子，不能先删单位掩码

仍取 e∼E、平方自由 q∼Q、EQ≈S，s=eq、r=n、h=eu、δ=ev，
\((n,q_0eq)=(uv,q)=1\)，\((e,q)=(q_0,eq)=1\)，u,v≠0。
固定 e 后记 U=H/e、V=L/e；标签支撑在 0<|u|≤2U、0<|v|≤2V。
内部 HL≲RS/T，R,Q≥1。

对 Type 分层 d=(k,q)、q=dℓ，使用变量
\[
 n/R,\quad\ell/(Q/d),\quad u/U,\quad v/V.                  \tag{P1}
\]
真实核第二变量仍是 \(ed\ell/S=(eQ/S)(\ell/(Q/d))\)，其余变量
为 ev/L、eu/H。固定盒上的四变量 Fourier 分离有系数绝对和
≪A_J（J≥6）；它对 e,d 一致，不增加 d 的费用。
内部 mollifier 因子 p_N 和光滑 taper 保留。单变量硬支持留在其
因子/允许标签中，不把原核的连续积分支持另切成非光滑 n/ℓ 区域。

每个原子可写成共同 n 列 aₙ、标签 bᵤcᵥ 及模数标量 β_(dℓ)：
\[
 a_n=\mu(n){\bf1}_{(n,q_0ed)=1}\times\text{共同 n 因子},\quad
 \sum_n|a_n|^2\ll R,\quad |b_u|,|c_v|,|\beta_{d\ell}|\le1.   \tag{P2}
\]
β 保留外 μ(q) 和分离的模数因子，固定 e 的 μ(e) 也仍在外面。
原子系数绝对和另由 A_J 支付。单位条件 (n,ℓ)=1 留在 n 列，
(uv,dℓ)=1 留在**整个标签和内**；(ℓ,q₀ed)=1 留在允许模数集合。
尤其不能把不同 ℓ 的 u/v-unit 掩码平滑掉或合成未带掩码的均值。

## 2. 标签和的精确中心投影

固定 e,d,ℓ（ℓ 平方自由、(ed,ℓ)=1），令
\[
 \begin{split}
 W_\ell&=\sum_{u,v\atop(uv,d\ell)=1}b_uc_v,\\
 Z_\ell(w)&=\sum_{u,v\atop(uv,d\ell)=1}b_uc_v
                        e_\ell(-euv\bar d\bar w),\quad w\in U(\ell),\\
 K_\ell(t)&=\sum_{u,v\atop(uv,d\ell)=1}b_uc_v
                        B_\ell(t,euv\bar d).
 \end{split}                                                \tag{P3}
\]
B 是 #505 的完整中心核，不是未中心化 Kloosterman 和。由于每个
euv\bar d 都是模 ℓ 的单位，准确有
\[
 \sum_{w\in U(\ell)}Z_\ell(w)=\mu(\ell)W_\ell.
\]
故 K_ℓ(t) 是单位支撑函数
\(Z_\ell(w)-\mu(\ell)W_\ell/\varphi(\ell)\) 的加性 Fourier。
Parseval 给
\[
 {1\over\ell^2}\sum_{t\bmod\ell}|K_\ell(t)|^2
 ={1\over\ell}\left(\sum_{w\in U(\ell)}|Z_\ell(w)|^2
                         -{|W_\ell|^2\over\varphi(\ell)}\right).
                                                               \tag{P4}
\]
μ(ℓ)²=1 用到了平方自由条件。右端两个和必须使用**同一掩码**。
ℓ=1 时 K₁=0；它不等于原 principal，principal 在 §4 单列付费。

令
\[
 P_\ell(j)=\sum_{uv\equiv j\ (\ell)\atop(uv,d\ell)=1}b_uc_v.
\]
先删除 P4 的非负减项，再将逆频率 \(\bar w\in U(\ell)\) 扩到
所有模 ℓ 的频率，最后用有限 Parseval，得到
\[
 {1\over\ell^2}\sum_t|K_\ell(t)|^2
 \le\sum_{j\bmod\ell}|P_\ell(j)|^2.                         \tag{P5}
\]
乘数 e\bar d 为单位，仅置换乘积剩余类，不改变右端能量。

## 3. 整数产品碰撞，而非外部四阶矩猜想

若标签域非空，则 U,V≥1/2。设 M=⌊4UV⌋≥1、
D_M=max_(1≤m≤M) τ(m)。对非零整数 z=uv，|z|≤M，任一 z 的有符号
表示数 r(z)≤2τ(|z|)≤2D_M，且总表示数≤16UV。
允许任意上述单位删项以及模长≤1 的标签系数，令
\(C_z=\sum_{uv=z,(uv,d\ell)=1}b_uc_v\)。则
\[
 \sum_z|C_z|^2\le\sum_z r(z)^2\le32D_M UV.
\]
每个模 ℓ 剩余类内至多 8UV/ℓ+2 个可能整数产品。一次 Cauchy 给
\[
 \sum_{j\bmod\ell}|P_\ell(j)|^2
 \le256D_M UV(1+UV/\ell)
 \ll_\epsilon(1+UV)^\epsilon UV(1+UV/\ell).                 \tag{P6}
\]
这里的整数端点常数不需要 U,V≥1；空域直接为零。正负标签都已经
计入 r(z)，没有用指数账代替实际整数支撑。P6 不使用 ACZ 或任何
Möbius 方差假设，也不把 unit mask 与正交投影交换。

## 4. 全部 d 层与拥挤费用必须一起求和

固定 e,d 和原子，准确的中心化线性贡献为
\[
 {\mu(d)\over d}\sum_{\ell\asymp Q/d}{\beta_{d\ell}\over\ell}
    \sum_{t\in U(\ell)}U_\ell(-t)K_\ell(t),\qquad
 U_\ell(-t)=\sum_{(n,\ell)=1}a_ne_\ell(-tn).                \tag{P7}
\]
原 Type 下降的 μ(d)、逆元和 1/d 均在，所有 primitive t 也在。
用 #505 已证的 unit-mask 大筛与 P5–P6，对 (ℓ,t) 做一次 Cauchy，
并利用 ℓ≈Q/d，得每个 d 的费用
\[
 \ll_\epsilon{[RQ(1+UV)]^\epsilon\over d}
 \sqrt{R\left(R+{Q^2\over d^2}\right)
                {Q\over d}UV\left(1+{UVd\over Q}\right)}.
                                                               \tag{P8}
\]
ℓ≥2 才有非零核，故 d≤Q。将根号内四项分别取平方根，求和得到
\[
 \begin{split}
 \sum_d\text{(P8)}\ll_\epsilon[RQ(1+UV)]^\epsilon\bigl\{
 &\sqrt{UV}\sqrt{QR(R+Q^2)}\\
 &+UV[\,R\log(2Q)+R^{1/2}Q\,]\bigr\}.
 \end{split}                                                \tag{P9}
\]
前两项的 d 幂为 −3/2、−5/2，拥挤项的 d 幂为 −1、−2。
**第二行不可丢弃**；其中 R^(1/2)Q 不是 (RQ)^(1/2)。
这就是保留 UV/ℓ 产品拥挤后真实付出的费用。

原 principal 由 \(\mu(q)/\varphi(q)\) 乘原 n/u/v 和组成。
对它取绝对值给每 e 的 A₀ RUV Q^ε，已由 P9 的 RUV log(2Q)
覆盖；没有将 principal 隐藏到零中心模态中，也没在平方中删 cross。

## 5. 恢复 e 和原物理外权

\(\sum_{e\asymp E}\sqrt{UV}\ll\sqrt{HL}\)，
\(\sum_{e\asymp E}UV\ll HL/E\)。恢复 Fourier ℓ¹ 预算、固定 μ(e)
以及唯一的 2T/(q₀RS)，在固定幂尺度上有
\[
 \boxed{|\mathcal O_{E,Q}|\ll_\epsilon
 {\mathcal A_J T^{1+\epsilon}\over q_0RS}
 \left\{\sqrt{HL}\sqrt{QR(R+Q^2)}
             +{HL\over E}[R+R^{1/2}Q]\right\}.}             \tag{P10}
\]
有限高度需使用 P9 的显式 log(2Q)，不能免费吸收。

在 q₀=1、R=S≈T³、H=L≈T^(5/2)、E≈T^η、Q≈T^(3−η) 时，
对于 3/2≤η≤5/2，P10 的指数是
\[
 \max(2-\eta/2,\ 3-\eta).                                  \tag{P11}
\]
因此 η≥2 是此 FP3 层的局部 T^(1+ε) 预算充分区，η>2 留正幂余量。
特别是 η=9/4：直接计数 RS/E² 的指数 3/2 变成 7/8（拥挤项为3/4），
相对该计数上界节省 5/8，距 T 的余量1/8。它不声称原和具有匹配下界。

真实非空族：由前篇所引 Bertrand 定理取互异素数 e≈Y⁹、q≈Y³，
S=R=eq、N=8S、T=(8S)^(1/3)≈Y⁴、Kz=Mz=√T、H=L=S/√T。
取 u=v=⌈H/e⌉≈Y<q，n 素数在 (S,2S)。则全部单位、genuine gcd=e、
原 h/δ 壳及 mollifier 支撑成立。连续 x=3√T/4 给
(xn+δ)/s∈[√T/2,2√T]（大 Y）。比较尺度取相邻有限 dyadic 块，
只改变常数。此例不宣称任意给定 W/F 的积分必非零。

对于 3/2≤η<2，principal 的当前绝对估计本身已有指数 3−η>1。
即使改进非零频率，也不能不重新处理 principal 就宣称覆盖该域；
这是本估计的不足，不是原式不可能进一步抵消的反例。

P10 可以从原式逐项分离这个子族，补集仍保留原共同 signed 算子。
其他 genuine-gcd allocations、q₀ 聚合、其余物理包和尾项，以及
全局有符号算术上界仍未证明。这里不登记全局 gate 或零点界完成。

English summary: center the full product-label kernel with the identical unit
mask, use Parseval and the integer divisor bound for uv collisions, then keep
both the summable Type layers and the crowded harmonic cost. The explicit
physical FP3 family satisfies (P10), with balanced threshold E≥T². This is not
a bound for all gcd allocations or a zero-free theorem.
