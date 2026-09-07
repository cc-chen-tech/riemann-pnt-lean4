# 原生困难主角色：先分解原 Möbius 列，再完成 Type-I 商变量

白话结论：在全 h/δ 变换后一个明确的困难主角色投影里，先把原
μ(n) 精确分成短 Type-I 与双长 Type-II。短项的商变量没有 Möbius
权，可以完整 Poisson 展开，再对真实模数平均。包括驻相误差后，
E=T^(6/5)、两个短截断均为 T 时，这个 Type-I 投影得到
O(D200 T^(3/5+ε))；对同对象重跑普通大筛只有 T^(11/10+ε)。
这不是整个主角色或整个 μ(n) 列的界：Type-II 及其他投影仍保留。
没有证明 14/17、2/3 或长 mollifier 的全局渐近式。

English summary: the exact short Type-I component of one native principal
projection admits quotient completion and an average of Ramanujan sums over
the actual moduli. At eta=6/5 and U=V=T the complete projected component,
including the stationary remainder, is O(D200 T^(3/5+epsilon)). The long
Type-II complement and other native projections remain open. This is a local
analytic result with finite guards, not a Lean theorem or a global exclusion.

## NT1. 冻结来源及准确投影

直接父 #556 为 71b1210dd1b7a854c932e6b83c6124157319ed9d；数学展开取
#554 d37e1f2fb0b3c4fe5656fe6feab52587ed8efd0a 的
[LC1–LC5](2026-08-31-physical-low-conductor-common-large-sieve.md)，
以及其中指向的 CG7 unmasked 顶项、AM12 和
[TD3](2026-08-31-physical-full-delta-top-divisor.md)。原定义仍是
49cfacd70c60372757280177c7b63fd4f7760817 的 (4.4)–(4.5)。
单位条件以 AM12/LC3 为准，不恢复旧的 (Y,z)=1。

固定同一内部 AFE 包：q₀=1、N=T³、R,S≍T³、M,K≍√T、
KS≍MR、MK≪T。整个包的支持保证 n,s≤N/2，保留全部
p_N、F_R、F_S、F_M、F_K、W、V_t；D200 完全沿 LC1。
原 h/δ 分割合回，不插入固定 H/L，也不新增联合硬角点。

辅助自然壳记 E≤e'<2E、E=T^η，本文只取这一最低壳。
CG7 的原有符号标记 β^μ 在该壳恒为1：它的除数条件仅允许1。
剥离辅助 q'=1 后，下面 q 一律表示 q'>1。
在 LC2 的诱导字符／reciprocal Poisson 展开中，取
\[
 z=r=\ell=1,\qquad m=h,\quad k=d>0,\quad
 A=hd\asymp T,\quad e'=Ac_0,\quad s=Ac_0q.          \tag{NT1}
\]
这里 h 是 gcd(e',m)，不是原 Fourier h；d 是 reciprocal gcd，
不是原 Ramanujan 展开的顶除数 d=q。h,d 互素且平方自由，
c₀,q 平方自由，(A,c₀q)=(c₀,q)=1，(n,Ac₀q)=1。
ℓ=1 的唯一主角色保留一次。h 由 F_M(h) 支持限制，A≍T
使 k=d≍√T；不在本次局部投影中新增无界 k 和。
这是原精确变换后的线性投影，不是原 h,δ 元组的 literal 子族。

记 C_A=E/A，W_A=S/A，所以 C_A≍C=T^(η−1)、W_A≍W₀=T²。
符号 W₀ 是模数长度，W(t/T) 仍是原光滑权。所有比较常数固定。
以下 U,V 是正 Type 截断，与核 V_t 不同；假定 max(U,V)
严格小于整个 n 支持的下端。本文主例取 η=6/5、U=V=T。

## NT2. 原 μ(n) 的精确分解

定义
\[
 \Gamma_I(n)=\sum_{\substack{bc\mid n\\b\le U,\ c\le V}}
                   \mu(b)\mu(c),\qquad
 \Gamma_{II}(n)=\sum_{\substack{bc\mid n\\b>U,\ c>V}}
                   \mu(b)\mu(c).
\]
由 μ*1=δ₁ 和 μ*μ*1=μ，对每个 n 精确有
\[
 \mu(n)=\mu(n)1_{n\le U}+\mu(n)1_{n\le V}
                      -\Gamma_I(n)+\Gamma_{II}(n). \tag{NT2}
\]
因此本包中 μ(n)=−Γ_I(n)+Γ_II(n)。两项都允许 n 非平方自由：
例如 U=V=1、n=4 时，Γ_I=Γ_II=1 而 μ(4)=0。
不能加 μ²(n)、(b,c)=1，或给商 n/(bc) 加上 μ。
统一有 |Γ_I(n)|≤d₃(n)≪_εT^ε。

对 NT1 的精确积分投影，将 μ(n) 替换为 g(n)，记为 P_E[g]。
于是 P_E[μ]=−P_E[Γ_I]+P_E[Γ_II]。本稿只估计第一项的模。
原负号和第二项不被删除，也不称原 μ(n) 列已被支付。

## NT3. 从原 I_k 得到同一个驻相主项

令 w=c₀q、B=n/w。TD3 中 y 变量换成 u=dy 后，定义
\[
 J_h=\int\!\!\int W(t/T)F_M(h)F_K(u/d)V_t(hu/d)
 u^{-1/2}\exp\{i[t\log(u/B)-2\pi u]\}\,du\,dt.
\]
写 B₀=p_N(n)p_N(Aw)F_R(n)F_S(Aw)，则 NT1 精确为
\[
 P_E[g]=2\sum_{h,d,c_0,q,n}
 \frac{\mu(A)\mu(q)g(n)B_0}
      {e'^2\varphi(c_0)q\sqrt B}\,J_h.              \tag{NT3}
\]
所有 NT1 支持／单位留在求和内。其归一化直接由
μ(a)c_a(k)/φ(a)=μ(d)/φ(c₀)、a=dc₀，及 y=u/d 得到；
并非在旧大筛估计上再乘一次驻相节省。

这里 B≍T、dK≍T。令 v=log(u/B)、β=2πB/T，
E₁(v)=(e^v−1)/v（在0取1），再令 τ=t/T−βE₁(v)。相位精确为
T vτ−2πB，且
\[
 J_h=T\sqrt B\,e(-B)\iint \mathcal A_h(v,\tau)e^{iTv\tau}dv\,d\tau,
\]
\[
 \mathcal A_h=e^{v/2}W(\tau+\beta E_1(v))F_M(h)
 F_K(Be^v/d)V_{T(\tau+\beta E_1(v))}(hBe^v/d).
\]
归一化支持在固定紧集，C⁶ 范数由 D200 支付。W V 的乘积在原
t 支持外光滑延零；不要求在那里单独定义 V。驻点越过光滑边缘
不产生硬边界项，β 只在固定有界正区间变化。

用角频率约定 Â(ξ,ζ)=∫A(v,τ)e^(−i(ξv+ζτ))dv dτ，有
\[
 \iint A e^{iTv\tau}=(2\pi T)^{-1}
              \iint\widehat A(\xi,\zeta)e^{-i\xi\zeta/T}d\xi d\zeta.
\]
先加 Gaussian 正则化再取极限即得此式，不对纯振荡内积分直接
作绝对 Fubini。紧支撑 C⁶ 保证 ∫|ξζÂ|≪D200，因而
\[
 J_h=2\pi\sqrt B\,e(-B)W(2\pi B/T)F_M(h)
       F_K(nh/(Aw))V_{2\pi B}(nh^2/(Aw))
          +O(\mathcal D_{200}\sqrt B/T).             \tag{NT4}
\]
没有额外一维驻相 e(±1/8) 因子。该证明同时保留主项 W(β)=0
的参数，并给同一余项上界；本投影的 k 范围已在 NT1 固定。

## NT4. 实际除数剖面及原慢权

定义（q=1 必须排除）
\[
 \sigma_A(w)=\sum_{\substack{c_0\mid w\\E\le Ac_0<2E\\w/c_0>1}}
                     \frac{\mu(c_0)}{c_0\varphi(c_0)},\qquad
 b_A(w)=\mu(w)\sigma_A(w).                           \tag{NT5}
\]
w 平方自由时 μ(q)=μ(w)μ(c₀)，所以 NT4 的主项严格为
\[
 4\pi\sum_{A\asymp T}\frac{\mu(A)}{A^2}
 \sum_{\substack{w,n\\(w,A)=(n,Aw)=1}}
   \frac{g(n)b_A(w)}{w}\Phi_A(n,w)e(-n/w),            \tag{NT6}
\]
其中
\[
 \Phi_A=B_0W(2\pi n/(wT))
       \sum_{h\mid A}F_M(h)F_K(nh/(Aw))V_{2\pi n/w}(nh^2/(Aw)).
\]
μ(A) 限制 A 平方自由，h|A 的原支持仍由 F_M 保留。
硬的 e' 壳完整留在 σ_A，不把它当作光滑权；Φ_A 不依赖 c₀/q
的分配。|σ_A(w)|≪T^ε C⁻²，w≍W₀。原 n,s 整包内部支持使
mollifier 硬边界冗余；不得另外乘一个联合硬指标。

Φ_A 的 n/R、w/W_A 归一化 C¹² 导数由 D200 τ(A) 一致控制。
原因是 n/w≍T、nh/(Aw)≍K、nh²/(Aw)≍MK，归一化微分
仅作用于这些有界比例和原 V 的加权导数。快相位 e(−n/w)
不包括在该慢权范数里。原 F_R/F_S 光滑支撑延零，不截出新的
literal 硬 n 壳；以 w 的有限倍 dyadic 覆盖只作离散分组。

## NT5. Type 商变量的完整单位 Poisson

固定 b≤U,c≤V，写 B₁=bc、n=B₁m。原单位分成
(B₁,Aw)=(m,Aw)=1。仅展开 (m,A)=1，令 t|A、m=t z，系数 μ(t)。
仍保留 (z,w)=1，不加 (z,t) 或 (z,A/t)。a=B₁t 是 w 的单位。
令 Z=R/a，F(z/Z)=Φ_A(a z,w)。因 aZ=R，F 的归一化 C¹²
范数对 b,c,t 一致，并在正固定紧区间光滑延零。

取 F̂(ξ)=∫F(u)e(−uξ)du；逐单位剩余类 Poisson 给
\[
 \sum_{(z,w)=1}F(z/Z)e(-az/w)
    =\frac Zw\sum_{j\in\mathbb Z}c_w(j-a)\widehat F(jZ/w). \tag{NT7}
\]
固定 w 的级数绝对收敛，式子对任意 Z>0 成立。Z 很短也不引入
额外单点成本：原支撑为空时左侧为0，右侧保留完整相消的级数。
F 仍可依赖 w；以下只用其一致 Fourier 衰减，不假设跨 w 可分离。

## NT6. 三类频率与真实模数平均

先保持所有 σ_A、μ、单位与原权，再在绝对上界中放宽允许 w。
在一个 w∈[W₁,2W₁) 上，W₁≍W₀，分三类：

1. j=0：由于 (a,w)=1，c_w(−a)=μ(w)，全部 w 费用≪D200 Z。
   此均值不是0，也不转移到其他 principal 账。
2. j≠0,a：L=j−a≠0。由 Ramanujan 有限恒等式，|c_w(L)|≤(w,L)，且
   \[
    \sum_{W_1\le w<2W_1}(w,L)
     =\sum_{d\mid L}\varphi(d)\#\{w:d\mid w\}
     \le2W_1\sum_{\substack{d\mid L\\d<2W_1}}\varphi(d)/d
     \le2W_1\tau(|L|).                              \tag{NT8}
   \]
   不补虚假的 +1：d≥2W₁ 时没有正倍数。仅在正上界放宽 w，
   没有使用未知的 μ(w) 平均，也没有把 μ 改成无符号原系数。
   令 K₁=W₁/Z；a、K₁ 只增长固定 T 幂。取任意小 ε₀>0，
   τ(|j−a|)≪T^ε₀(1+|j|)^ε₀。C¹² 衰减及 ε 重命名给
   \[
    \sum_{j\ne0,a}(1+|j|/K_1)^{-12}\tau(|j-a|)
       \ll T^\epsilon
       \begin{cases}K_1,&K_1\ge1,\\K_1^{12},&K_1<1.\end{cases}
   \]
   对 w,j 全部求和后费用≪D200 T^ε W₀。
3. j=a：c_w(0)=φ(w)，不能应用 L≠0 的 NT8。此时 aZ/w=R/w≍T，
   Fourier 尾给 |F̂(aZ/w)|≪D200 T⁻¹²，所以全部 w 费用
   ≪D200 ZW₀T⁻¹²。这不是删除特殊频率，而是明确支付它。

综上，每个 A,b,c,t 的原 w 平均至多
\[
 \mathcal D_{200}T^\epsilon(Z+W_0+ZW_0T^{-12}).       \tag{NT9}
\]
在此使用一致范数与非负支配，故原联合 w 权、极短 Z、非单位
Fourier 频率以及无限 j 尾均已包含，无需谱输入或素数模数限制。

## NT7. 全 A、Type 参数与驻相误差

NT6 外系数为4πμ(A)/(A²w)，剖面另付 C⁻²T^ε。
全部 A≍T 及 h|A 行数≪T^(1+ε)；t|A 的 τ(A) 和 Σ1/t
均为 T^ε。b,c 的项数≤UV、Σ1/(bc)≪log(2U)log(2V)。NT9 给
\[
 |\operatorname{Main}_I|\ll\mathcal D_{200}T^\epsilon
 \left\{\frac{R}{T W_0 C^2}+\frac{UV}{T C^2}
                         +\frac{R}{T C^2}T^{-12}\right\}. \tag{NT10}
\]
该估计允许不均衡 U,V，但需前述整个 n 支持高于两截断。

不能把驻相主项当作原式：NT4 余项在相同全外层也要支付。
用 |Γ_I(n)|≤d₃(n)，对每个 A 的 c₀ 层有 Σ1/φ(c₀)≪T^ε、
q≍S/E 的 Σ1/q≪1、n 计数≪R。A 行数≪T^(1+ε)，
e'≍E；NT3/NT4 的相对 T⁻¹ 余项因此为
\[
 |\operatorname{Err}_I|\ll\mathcal D_{200}T^\epsilon R/E^2.
                                                               \tag{NT11}
\]
等价复算是主项全绝对体积 R/(T C²) 乘 T⁻¹。所有有限 h,d
主环和光滑延零参数都在 NT3 的一致 normal form 内；未混入
其他 k/z/r/ℓ 的尾或把其上界赠予本投影。C⁶ 与 C¹² 估计分别
作用于线性主项／余项，只支付一份原 D200，不将范数平方。

## NT8. 物理指数与新增的局部范围

η=6/5、UV=T^β 时，NT10 的三项与 NT11 的指数依次为
\[
 -2/5,\qquad \beta-7/5,\qquad 8/5-12,\qquad3/5.     \tag{NT12}
\]
因此 U=V=T 时
\[
 |P_E[\Gamma_I]|\ll_\epsilon\mathcal D_{200}T^{3/5+\epsilon}.
                                                               \tag{NT13}
\]
更一般 UV≤T^(12/5) 时同一 Type-I 投影可付 T^(1+ε)。
UV 边界不是整个 μ(n) 投影已闭合的阈值，Γ_II 仍是双长有符号和。

## NT9. 同对象的普通大筛比较，不将总和界赋给子和

为了比较，直接对 NT6 的 Γ_I 列重跑普通倒数频率大筛。
展开 (n,w)=1 后 n=f x,w=f y，系数严格为
\[
 \mu^2(f)\mu(y)\Gamma_I(fx)1_{(y,f)=1},             \tag{NT14}
\]
另有原 A-unit；没有 (x,f)=1。Γ_I(fx) 是共同 x 列，能量
≪(R/f)T^ε，σ_A(fy) 是共同 y 列且模≤C⁻²T^ε。
对 Φ_A 作 n/R,w/W_A 两变量光滑分离，H² 的绝对 Fourier 预算
足够；硬 e' 支持仍全部留在 σ_A，不参与分离。

不同正 y≍Y 的圆周频率1/y间距≳Y⁻²。用
[Kedlaya Theorem 15.5](https://kskedlaya.org/ant/chap-largesieve.html)
的加性大筛和一次 Cauchy，长度 X=R/f、Y=W₀/f 的裸双和
≪T^ε C⁻²√(XY(X+Y²))。有限 Y 时同式可吸收常数。
外层 1/(A²w) 和全部 A、f 费用给
\[
 \mathcal D_{200}T^\epsilon (TC^2)^{-1}
                 (\sqrt{RW_0}+R/\sqrt{W_0}),        \tag{NT15}
\]
因为两项的 f 幂分别为 −2 和 −3/2。η=6/5 时为 T^(11/10)
与 T^(3/5)，连同 NT11 仍只有11/10。新的 NT13 将这个同对象
上界降到3/5，改善1/2；不声称已证明算术和具有相应大小下界。
NT13 的来源是无 μ 商变量的完整完成与模数平均，而非单列范数优化。

## NT10. 原支持非空

无限构造：取互异素数 h,d≍Y，令 T=2πhd、A=hd、M=K=h。
Bertrand 给素数 c₀∈(T^(6/5)/A,2T^(6/5)/A)，再选素数
q∈(T³/(100Ac₀),T³/(50Ac₀))，令 s=Ac₀q，并取素数 n∈(s,2s)。
充分大 Y 时各尺度不同，全部单位成立，n,s≤T³/2。
取 R=S=s，y=nh/s∈(K,2K)，t₀/T=n/s∈(1,2)。
此时 n>U=V=T，且 Γ_I(n)=1、Γ_II(n)=0。
这说明投影的原支持非空，不保证任意预先选定权函数的积分非零。

脚本还检查整数见证 h=101,d=103,c₀=71,q=16338163、
n=20112632646541、T=72821。E 壳用 T⁶≤e'⁵<32T⁶，
驻点 t₀ 的上下界仅用3<π<22/7，原内包 n,s≤T³/2 逐项核对。

## NT11. 未付部分与验证边界

P_E[Γ_II]、NT1 之外的 z/r/ℓ、其他自然 E' 壳、原校正、
辅助 q'=1 和零频等都保留。没有将本结果送给任意有界 n 系数，
也不与 #556 的 gcd(m,k) 收益或固定 H/L 的 Type-II 频带相乘。
q₀ 外层、非内部 AFE、跨尺度统一尾和完整有符号 gate 仍未完成。

有限脚本核对卷积、非平方自由反例、单位 IE、剖面与复相位重组、
精确圆分 DFT、非零 gcd 平均、特殊频率坐标及原支持。它不能替代
Poisson、无限尾和原混合导数的解析证明，也不代表 Lean/main 验收。
本交付仅为两文件数学检查点，不更改任何 Lean 目标或冻结父版本。
