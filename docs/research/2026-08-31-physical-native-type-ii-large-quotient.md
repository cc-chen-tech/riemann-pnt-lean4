# 原生 Type-II 的大无权商：对数相位与共同时间均值

白话结论：保留原 Type-II 中没有 Möbius 权的商，而不是先把整列
平方或加上平方自由掩码，可以支付一个原来仍超预算的大商区域。
在下面明确的 native 主角色投影、E=T^(6/5) 中，商长度
X=T^(17/30) 的原包由直接商完成的 T^(31/30+ε) 改善为
O(D200 T^(59/60+ε))。完整单位容斥、硬除数剖面、原驻相余项
及 Mellin 全尾都计入。小商、其他投影与全局有符号余项仍未解决。
这不是 14/17 或 2/3 的零点排除，也不是新的 Lean 定理。

English summary: one exact native principal projection of the original,
unmasked Type-II sum admits a large-unsigned-quotient estimate. At eta=6/5,
the quotient packet X=T^(17/30) is O(D200 T^(59/60+epsilon)), improving the
same-packet direct-completion bound T^(31/30+epsilon). The proof uses full
unit inclusion-exclusion, the classical (1/6,2/3) exponent pair and a common
Dirichlet-polynomial mean value. Small quotients and the global gate remain
open. Finite guards do not replace the analytic proof.

## LQ1. 唯一原式来源、范围与商长度

父分支 #559 冻结为 12bf9690c08f17e2026c4bf479a52522a9c0b4e6；
本稿实际复用 #558 的
[NT1–NT6](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/7b627068d08fa579695b4414632494fea2946492/docs/research/2026-08-31-physical-native-principal-type-i.md)。
原定义仍为 49cfacd70c60372757280177c7b63fd4f7760817 的 (4.4)–(4.5)。

只取同一内部 native 全 h/δ 包：q₀=1、N=T³、R,S≍T³、
原 AFE 尺度 M_AFE,K_AFE≍√T、MK≪T；整个原支持保证 n,s≤N/2。
NT1 的 z=r=ℓ=1、最低辅助 E 壳、q'>1 和全部原权不变。
下文 q 表示剥离 q'=1 后的 q'>1，A=hd≍T，e'=Ac₀，s=Ac₀q；
A,c₀,q 的平方自由与互素、(n,Ac₀q)=1 全部沿 NT1。
这仍是原精确变换的线性投影，不是 literal 原 h,δ 元组子族。

固定 η=6/5，记 E=T^η、C≍E/A≍T^(1/5)、W₀≍S/A≍T²。
商长度专用 X，**不是**原 AFE 的 M。Type 截断 U,V 低于整个 n
支持下端；例如 U=V=T。保留 b>U、c>V，并用固定光滑 dyadic
标签选 b≍B₁、c≍B₂、m≍X，令 L=B₁B₂≍R/X。
每个标签模≤1，归一化导数一致有界；本文先取
\[
                 1\le X\le T^{4/5}.                     \tag{LQ1}
\]
b/c 阈值是各自单变量硬条件。m 标签光滑，不引入随另一变量移动
的硬边缘；不能把它换成字面的联合硬 n 或 e' 截断。

定义本包的原 Type-II 系数
\[
 g_X(n)=\sum_{\substack{bc m=n\\b>U,\ c>V}}
       \mu(b)\mu(c)\omega_1(b/B_1)\omega_2(c/B_2)\omega_3(m/X).
                                                               \tag{LQ2}
\]
没有 μ(m)、μ²(m) 或 (b,c)=1。非平方自由 n 仍可出现，且
|g_X(n)|≤d₃(n)≪T^ε。本文估计的是 NT3 的精确 P_E[g_X]，
不是 #559 的平方自由子包。全 NSII=NSI 的等式不能免费限制到
同一个 m 包：n=4、U=V=1 时，I 的商是4，II 的商是1。

## LQ2. 原驻相主项与硬剖面不改

由 NT3–NT6，同一线性投影等于
\[
 P_E[g_X]=4\pi\sum_{A\asymp T}\frac{\mu(A)}{A^2}
 \sum_{\substack{w,n\\(w,A)=(n,Aw)=1}}
 \frac{\mu(w)\sigma_A(w)g_X(n)}{w}\Phi_A(n,w)e(-n/w)
       +O(\mathcal D_{200}T^\epsilon R/E^2),            \tag{LQ3}
\]
\[
 \sigma_A(w)=\sum_{\substack{c_0\mid w\\E\le Ac_0<2E\\w/c_0>1}}
                     \frac{\mu(c_0)}{c_0\varphi(c_0)},\qquad
             |\sigma_A(w)|\ll C^{-2}T^\epsilon.        \tag{LQ4}
\]
Φ_A 是 NT6 的真实 B₀、W(2πn/(wT)) 及 h|A 的 F_M/F_K/V_t 和；
n/R、w/W_A 的 C¹² 半范数由原 D200 τ(A) 控制。快相位不纳入
慢权范数。原 e' 硬壳及 q>1 排除全留在 σ_A，不称它光滑。
原内部整包已使 mollifier 硬支持冗余，不另乘联合硬指标。

驻相余项按合并后的 |g_X|≤d₃ 支付一次；不能给每个 Type 元组
另付一个 R/E²。原 D200 只付一次，未乘以此前主项的任何节省。

## LQ3. 完整展开无权商的单位

写 l=bc。原单位为 (l,Aw)=(m,Aw)=1、(A,w)=1。
只展开商的全部单位条件，除数唯一写成 αδ，其中 α|A、δ|w：
\[
       m=\alpha\delta z,\quad w=\delta y,\qquad
       \frac{lm}{w}=\frac{\alpha lz}{y}.              \tag{LQ5}
\]
由 w 的 Möbius 权，系数精确融合为
\[
 \mu(w)\mu(\alpha)\mu(\delta)
   =\mu(\alpha)\mu^2(\delta)\mu(y)1_{(y,\delta)=1}.  \tag{LQ6}
\]
保留 (δ,A)=1、(l,Aδy)=1、(y,Aδ)=1；α|A 的外 μ(α) 不删除。
**z 没有任何剩余单位掩码或 Möbius 权。** 例如 A=2,w=3,l=1,m=4
时，给 z 加 (z,αδ)=1 会破坏原本为0的单位容斥。

令 Z=X/(αδ)、Y=W₀/δ。原相位频率参数为
\[
           \Theta=\alpha LZ/Y=LX/W_0\asymp T.         \tag{LQ7}
\]
非空正整数 z 支持迫 αδ≲X，故 Y≳W₀/X≳T^(6/5)，且
L≍R/X≳T^(11/5)。极短 Z 允许，只要非空就有 Z≳1，常数由
固定支持决定；不为无正整数标签的行虚构一个 +1。

## LQ4. 四维共同原子：先放入原 1/w

在 b/B₁、c/B₂、z/Z、y/Y 四变量上分离真实慢权。
**先把 W₀/w=Y/y 放入该慢权**，外面才是精确的 1/W₀。
这避免在保留有符号和时直接用 1/w 的上确界替换原权。
Y/y 在固定正紧支撑上归一化导数一致有界。

n/R=bcαδz/R、w/W₀=δy/W₀ 的比例归一化后参数均有界；
Φ_A、三标签及这个倒数因子给四维 C¹² 紧支撑慢权。
取固定外 cutoff 等于1在其支持上，作周期 Fourier 分离并保留
这些独立紧支撑因子。若 j∈Z⁴ 为模态，Sobolev–Cauchy 给
\[
 \sum_j |c_j|(1+|j_z|)\ll\|\mathcal W\|_{H^4}
                           \ll\mathcal D_{200}T^\epsilon,       \tag{LQ8}
\]
因为 Σ_j (1+|j|)²(1+|j|²)^(-4)<∞。只在 z 因子上支付一次 BV；
其他三因子只用模长界，不消耗 Fourier 频率的幂。

固定原子，将 bc 合为 l。共同列
\[
 a_l=\sum_{bc=l}\mu(b)\mu(c)a_ba_c1_{b>U,c>V,(bc,A\delta)=1},
 \quad b_y=\mu(y)\sigma_A(\delta y)b_y^{\rm sm}1_{(y,A\delta)=1}
                                                               \tag{LQ9}
\]
分别只依赖 l、y；|a_l|≪τ(l)，|b_y|≪C⁻²T^ε。
硬 e' 壳始终只在第二列中，剩余两列耦合仅是 (l,y)=1。
z 因子为独立光滑原子，BV≪1+|j_z|。原 b,c 单变量硬条件
在 a_l 中保持，不被宣称为光滑函数。

## LQ5. Mellin 主带与全尾

取固定 χ∈C_c^∞(0,∞)，在所有分离原子的
v=(l/L)(z/Z)/(y/Y) 支持上等于1。记
\[
 K_\Theta(v)=\chi(v)e(-\Theta v),\quad
 \widehat K_\Theta(t)=\int K_\Theta(v)v^{it}\frac{dv}{v},\quad
 K_\Theta(v)=\frac1{2\pi}\int\widehat K_\Theta(t)v^{-it}dt. \tag{LQ10}
\]
对固定放大的正带 cT≤t≤CT，覆盖 χ 支持中全部驻点，
|K̂_Θ(t)|≪T^(-1/2)。令 v=e^u，则相位为 tu−2πΘe^u，
二阶导数在紧支撑上一致≍T；原点附近 t 没有未付驻点。
带外反复分部积分给 |K̂_Θ(t)|≪_J(T+|t|)^(-J)，因此其 L¹
尾≪T^(1−J)。χ 光滑延零，无移动硬端点。

Mellin 公式中的所有正尺度 it 次幂完整保留，只有取模时才用其
模为1；没有把原线性和擅自共轭为另一个和。四维 Fourier 全和
由 LQ8 先绝对控制，Mellin 全积分亦绝对收敛后才换序。

## LQ6. 真正无算术权的对数标签

在 t≍T、Z≤X≤T^(4/5) 时，经典指数对 (1/6,2/3) 给任意
子区间的无权和
\[
      \left|\sum_{z\asymp Z} z^{-it}\right|
          \ll_\epsilon T^{1/6+\epsilon}Z^{1/2}+Z/T.  \tag{LQ11}
\]
用的是 T^κ Z^(ℓ−κ)，不是 T^κ Z^ℓ。可直接参照
[指数对定义、Lemma 5.2 与 Proposition 5.10](https://teorth.github.io/expdb/blueprint/exponent-pairs-chapter.html)。
log 相位的固定符号不影响该估计。固定有界短 Z 用平凡界吸收；
Z/T 是可保留的低阶正项，不承担主节省。
对实际 z 光滑因子作 partial summation，恰付 LQ8 中的 BV 权。
此处不把指数对用于 μ(z)、字符或有单位掩码的 z 和。

## LQ7. 剩余 coprime 两列的全除数时间均值

主带对 z 标签取统一模后，剩余
\[
                 Q(t)=\sum_{(l,y)=1}a_lb_y(l/y)^{-it}.
\]
再次完整容斥 r|l,y，令 l=rx、y=rv。每个固定 r 的
a_(rx)、b_(rv) 仍是共同列，r 的相位精确取消。
若融合 μ(r)μ(y)，得到 μ²(r)μ(v)1_(v,r)=1；**没有 (x,r)=1**，
因为 l=bc 仍可非平方自由。原 Aδ 单位也留在这些列中。

普通 Dirichlet 多项式均值加一次 Cauchy 给
\[
 \int_{cT}^{CT}|N_r(t)V_r(-t)|dt
 \ll C^{-2}T^\epsilon
   \sqrt{(T+L/r)(L/r)(T+Y/r)(Y/r)}.                  \tag{LQ12}
\]
可由 [Tao Notes 6, Theorem 1](https://terrytao.wordpress.com/2015/02/13/254a-notes-6-large-values-of-dirichlet-polynomials-zero-density-estimates-and-primes-in-short-intervals/)
的分离采样均值对单位平移积分取得连续版本；也即经典
Montgomery–Vaughan 均值定理。任意起点、长度 O(T) 的区间均可。

先三角估计每个 r 项再求全部 r，平方根内三项的 r 幂为
−4、−3、−2；开方并求和得
\[
 \int|Q(t)|dt\ll C^{-2}T^\epsilon
 \{LY+\sqrt{TLY(L+Y)}+T\sqrt{LY}\log(2LY)\}
                  \ll C^{-2}T^\epsilon LY.          \tag{LQ13}
\]
最后一步用 L,Y≳T，log 归入任意 ε。短行的正整数个数≪L/r、Y/r，
原支持空时为0。全 r 谐和尾已在式中，不缩短多项式长度，不从
unmasked 总和界直接推给其单位子和。LQ13 已含 t 积分，不再乘 T。

## LQ8. 全 α、δ、A 与唯一外权

固定 α、δ 的主带裸和，由 LQ11/LQ13 至多
\[
 C^{-2}T^\epsilon T^{-1/2}L\frac{W_0}{\delta}
 \left\{T^{1/6}\sqrt{\frac X{\alpha\delta}}
                       +\frac X{T\alpha\delta}\right\}. \tag{LQ14}
\]
LQ4 已把 1/w 精确抽为 1/W₀ 乘慢权。全部 A≍T 的 ΣA⁻²≪1/T；
h|A、α|A 的除数预算归入 T^ε。对全 δ≥1，两个幂分别为
δ^(-3/2)、δ^(-2)，都收敛；α 的 −1/2、−1 幂只付 τ(A)。
因此主项为
\[
 |\operatorname{Main}_X|\ll\mathcal D_{200}T^\epsilon
 \left\{\frac{R T^{1/6-3/2}}{C^2\sqrt X}
                       +\frac{R}{T^{5/2}C^2}\right\}.   \tag{LQ15}
\]
带外用全部绝对体积 LYZ=RW₀/(αδ²)，乘 Mellin L¹ 尾及同一
外权，得 D200 T^ε R C⁻²T^(-J)，取 J=12 即足够。
四维分离与这个核尾是两个线性预算，不乘 D200²。
σ_A 的非平滑性没有进入 z 求和或核的导数。

## LQ9. 完整局部定理及同包比较

包括 LQ3 的原驻相余项，以上证明给
\[
 \boxed{|P_E[g_X]|\ll_\epsilon\mathcal D_{200}T^\epsilon
 \left\{\frac{R T^{-4/3}}{C^2\sqrt X}
       +\frac R{T^{5/2}C^2}+\frac R{E^2}
       +\frac R{C^2}T^{-12}\right\}.}                \tag{LQ16}
\]
X=T^λ、η=6/5 的四指数为
\[
         19/15-\lambda/2,\quad1/10,\quad3/5,\quad-47/5. \tag{LQ17}
\]
故 8/15≤λ≤4/5 的本包可付 D200 T^(1+ε)。λ=17/30 时
最大指数59/60；λ=1/2仍为61/60，不能删除小商补集。

同对象的对照需重跑 NT7–NT10，而非把 Type-I 总和界赠予 Type-II：
固定 b,c 及同一光滑 m 包做商完成，配对数≪L T^ε，Σ1/(bc)≪T^ε。
NT9 三项和驻相误差于是给
\[
 \mathcal D_{200}T^\epsilon
 \{R/(TW_0C^2)+L/(TC^2)+R T^{-12}/(TC^2)+R/E^2\}. \tag{LQ18}
\]
其最大指数为 max(8/5−λ,3/5)，λ=17/30 时为31/30。
本稿同包改善1/20，新增商区域 8/15≤λ<3/5；相应 bc 最大尺度
由直接完成的 T^(12/5) 扩到 T^(37/15)。这比较的是已证上界，
不是声称实际和有同量级下界。B₁、B₂ 的有限 dyadic 求和只付对数。

## LQ10. 真实新带非空与交付边界

无限整数支持构造：取互异素数 h≍Y³⁰、d≍Y³⁰，令 T=2πhd，
A=hd、M_AFE=K_AFE=h；选素数 c₀∈(T^(6/5)/A,2T^(6/5)/A)。
再取互异素数 b,c≍Y⁷³、m≍Y³⁴，n=bc m；可用固定的相邻
倍长区间保证 b≠c。Bertrand 在 (n/(2Ac₀),n/(Ac₀)) 给素数 q，
于是 s=Ac₀q∈(n/2,n)。各因子尺度不同，所有单位成立。
选 h∈(Y³⁰,2Y³⁰)、d∈(2Y³⁰,4Y³⁰)，b∈(Y⁷³,2Y⁷³)、
c∈(2Y⁷³,4Y⁷³)、m∈(Y³⁴,2Y³⁴)，则 n,s≤T³/2。
R=S=s、t₀/T=n/s∈(1,2)、nh/s∈(h,2h)，原支持成立；
m≍T^(17/30)、b,c>T。它只证明无限真实允许域，不保证任意
事先给定 W/F/V 权在该域非零。

有限见证保留 NT10 的 T=72821、h=101、d=103、c₀=71、q=16338163，
改取 b=154459、c=154487、m=607，n=14484177872531。
脚本只用精确整数／有理比较验证原内包、驻点、全部单位、b,c>T
和 T^(8/15)<m<T^(3/5)，不是浮点相位图上的假支持。

未支付的是原 II 的小商、其他自然壳／native z/r/ℓ、零模与校正、
q₀ 外层、非内部 AFE 及跨尺度统一尾。也没有把本大商结果与
#559 的全非平方自由估计拼成平方自由小商余项；该拼接需另证。
固定 H/L 的 #560 等结果属于不同投影，不在本稿相乘或混用。

有限脚本检查两次完整单位 IE、额外单位的真实反例、非可分离复
有理权的 root-vector 重组、共同列／全 r 幂、原外权及阈值。
这些是可执行的有限防错守卫，不能替代指数对、时间均值与全尾证明。
文稿与脚本不增加 Lean 接口或把全局目标登记为完成。
