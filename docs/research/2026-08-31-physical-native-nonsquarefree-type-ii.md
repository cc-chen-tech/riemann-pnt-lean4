# 原生主角色：支付非平方自由 Type-II，合法保留平方自由双长余项

白话结论：不能因为原 μ(n) 在非平方自由数上为零，就删除 Type
分解中各自非零的两部分。本稿在 #558 的同一个原生主角色投影中，
把这个实际余项独立估到 D200 T^(14/15+ε)。因此之后可以合法地只
研究平方自由的双长 Type-II；该双长和仍未解决。本结果不恢复
#490 的旧全局删项，不证明整个主角色、14/17、2/3 或全局渐近式。

English summary: in the precise native principal projection of #558, the
nonsquarefree Type-II component is O(D200 T^(14/15+epsilon)). A signed
square-divisor split combines quotient completion for small divisors with
the true sparse common-column energy for large divisors. The remaining
squarefree double-long component is not bounded here. Finite checks guard
identities and scope; they are not the analytic proof or a Lean theorem.

## NS1. 来源、对象及完整原式边界

直接父提交为 #558 的
[7b627068d08fa579695b4414632494fea2946492](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/7b627068d08fa579695b4414632494fea2946492/docs/research/2026-08-31-physical-native-principal-type-i.md)。
本稿使用其 NT1–NT15，不改变任何父定义。原定义继续追溯
49cfacd70c60372757280177c7b63fd4f7760817 的 (4.4)–(4.5)。

固定 NT1 内部 native AFE 包：q₀=1、N=T³、R,S≍T³、M,K≍√T、
KS≍MR、MK≪T；全 h/δ 已按原式重组，不是固定 H/L 的包。
取最低辅助壳 E≤e'<2E、E=T^(6/5)，以及诱导字符／互反 Poisson
投影 z=r=ℓ=1、m=h、k=d>0、A=hd≍T、e'=Ac₀、s=Ac₀q。
这里 h,d 是 NT1 变换后的变量，不是原 Fourier h 和顶除数 d=q。
A,c₀,q 平方自由，(A,c₀q)=(c₀,q)=1，q>1，(n,Ac₀q)=1。
这是精确变换后的线性投影，不是任意原 h,δ 元组的 literal 子族。

记 W₀≍S/A≍T²、C≍E/A≍T^(1/5)。全部 p_N、F_R、F_S、
F_M、F_K、W、V_t 及 NT1 的 D200 保留；整包支持保证 n,s≤N/2。
没有加入联合硬角点，辅助 e' 硬壳仍在 NT5 的除数剖面 σ_A 中。
P_E[g] 表示 NT3 的同一**精确积分投影**，仅将 μ(n) 替换为 g(n)。
各比较常数固定，ε 可任意小，隐常数可依赖 ε 和固定支持常数。

本稿使用的驻相主项及一致余项为
\[
 P_E[g]=4\pi\sum_{A\asymp T}\frac{\mu(A)}{A^2}
 \sum_{\substack{w,n\\(w,A)=(n,Aw)=1}}
 \frac{g(n)\mu(w)\sigma_A(w)}w\Phi_A(n,w)e(-n/w)
 +O_\epsilon(\mathcal D_{200}T^\epsilon R/E^2).       \tag{NS1}
\]
此式要求 |g(n)|≪_εT^ε；下文每个实际系数都满足。σ_A、Φ_A
严格取 NT5/NT6，特别 q=1 仍排除，Φ_A 的归一化 C¹² 由 D200
控制，快相位不放进慢权范数。驻相余项对合并后的 g 使用，
不得再按它的平方除数个数重复乘费。

## NS2. 非平方自由部分的精确关系

令 U,V≥1，且 max(U,V) 低于整个 n 支持的下端。沿 NT2 定义
\[
 \Gamma_I(n)=\sum_{\substack{bc\mid n\\b\le U,c\le V}}\mu(b)\mu(c),
 \qquad
 \Gamma_{II}(n)=\sum_{\substack{bc\mid n\\b>U,c>V}}\mu(b)\mu(c).
\]
本包逐项有 μ(n)=−Γ_I(n)+Γ_II(n)。因此
\[
 (1-\mu^2(n))\Gamma_{II}(n)=(1-\mu^2(n))\Gamma_I(n).
                                                               \tag{NS2}
\]
等式不代表两边为零：U=V=1、n=4 时它们都等于1。
只有独立支付这个带 mask 的原式之后，才能在剩余 II 中取平方自由。

完整有符号平方除数恒等式是
\[
 1-\mu^2(n)=-\sum_{\substack{\nu\ge2\\\nu^2\mid n}}\mu(\nu).
                                                               \tag{NS3}
\]
取 D=T^δ≥1，分 2≤ν≤D 与 ν>D，两个合并系数记为 g_sm、−g_D：
\[
 g_{\rm sm}(n)=-\Gamma_I(n)\sum_{2\le\nu\le D,\,\nu^2\mid n}\mu(\nu),
 \qquad g_D(n)=\Gamma_I(n)\sum_{\nu>D,\,\nu^2\mid n}\mu(\nu).
\]
两者模均≤d₃(n)τ(n)≪T^ε，故 NS1 的驻相余项分别适用，均不乘 D。
ν 由 μ 强制平方自由；n、b c 及商变量不据此强制平方自由。

## NS3. 小平方除数：重叠必须留在商变量长度中

固定 b≤U、c≤V，写 B=bc、n=Bm。精确令
\[
 L_\nu(B)=\frac{\nu^2}{(\nu^2,B)};
 \qquad \nu^2\mid Bm\quad\Longleftrightarrow\quad L_\nu(B)\mid m.
                                                               \tag{NS4}
\]
不要求 (ν,B)=1，也不能将 L 改成 ν²。m=L y 后，原单位先给
(BL,Aw)=1、(y,Aw)=1。只展开 (y,A)=1，写 t|A、y=t z，保留
(z,w)=1；没有 (z,t)、(z,A/t) 等残余 mask。a=BLt 是 w 的单位。
完整符号 −μ(ν)μ(b)μ(c)μ(t)μ(w)σ_A(w) 保留，公共
4πμ(A)/(A²w) 仍在外层，未删 μ(A)。

设 Z=R/(BLt)。归一化权 Φ_A(BLt z,w) 的 C¹² 范数一致，
因为 BLt·Z=R。按 NT7 的约定，原商变量的完整 Poisson 为
\[
 \sum_{(z,w)=1}F(z/Z)e(-az/w)
  =\frac Zw\sum_{j\in\mathbb Z}c_w(j-a)\widehat F(jZ/w).
                                                               \tag{NS5}
\]
固定 A,b,c,ν,t 后，先保留原 w 权和单位，再在正上界中放宽 w。
NT8/NT9 的三项逐项重跑：j=0 给 Z；j≠0,a 以
Σ_{w≍W₀}(w,j−a)≪W₀τ(|j−a|) 给 W₀T^ε；j=a 必须单独
保留，aZ/w=R/w≍T 给 ZW₀T⁻¹²。故三费用仍为
\[
 \mathcal D_{200}T^\epsilon(Z+W_0+ZW_0T^{-12}).     \tag{NS6}
\]
ν≤D 及 a 都至多增长固定 T 幂，ε 重命名吸收 divisor 费用。
即使 Z<1，完整双侧 j 尾仍被 NT6 的衰减证明包含，不截成零模，
也不补虚构的 +1。原权可依赖 w；只使用一致 Fourier 衰减。

## NS4. 小除数全外层费用

Z 项的 ν 求和不损 D 幂，因为有收敛的正 Euler 费用
\[
 \sum_{\nu\ge1}\frac{\mu^2(\nu)}{L_\nu(B)}
 =\prod_p\left(1+\frac{(p^2,B)}{p^2}\right)
 \le \zeta(2)\tau(B).                              \tag{NS7}
\]
p∤B 的因子积≤ζ(2)；v_p(B)=1 的因子为1+1/p≤2，
v_p(B)≥2 的因子为2≤v_p(B)+1。重叠大的 B 因而也已支付。
Σ_{b≤U,c≤V}τ(bc)/(bc)≪T^ε；t|A 及 h|A 同样只付 divisor 费。
中间 W₀ 项只计 ν≤D 的项数，最多 D，不可免费去掉。
用 |σ_A|≪C⁻²T^ε、原 1/w 及全部 A≍T，得到
\[
 |\operatorname{Main}[g_{\rm sm}]|\ll\mathcal D_{200}T^\epsilon
 \left\{\frac{R}{T W_0C^2}+\frac{UV D}{TC^2}
                         +\frac{R}{TC^2}T^{-12}\right\}.         \tag{NS8}
\]
NS1 的驻相误差另为 R/E²。这不是将 #558 的 unmasked Type-I
界赠予子 mask，而是保留 ν/B 重叠后重新完成每个实际商变量。

## NS5. 大平方除数：整个共同列的稀疏性

对 Main[g_D] 完整展开 (n,w)=1，令 n=f x、w=f y。因为原 μ(w)，
系数严格变为
\[
 \mu^2(f)\mu(y)g_D(fx)1_{(y,f)=1},                 \tag{NS9}
\]
另保留原 A-unit。没有 (x,f)=1，f 由 μ²(f) 强制平方自由。
固定 f 后，g_D(fx) 是不依赖 y 的共同 x 列。

令 X=R/f。非零 g_D(fx) 强迫某个平方自由 ν>D 满足 ν²|fx。
由于 f 平方自由，这等价于 (ν²/(ν,f))|x。正支撑 x≍X 的倍数
个数≤O(X(ν,f)/ν²)：若除数大于支撑上端，根本没有正倍数。
因此不增加一个按 ν 求和会失控的 +1。

对任意 f 和 D≥1，有完整正尾上界
\[
 \sum_{\nu>D}\frac{(\nu,f)}{\nu^2}
 =\sum_{d\mid f}\frac{\varphi(d)}{d^2}
                  \sum_{k>D/d}\frac1{k^2}
 \ll\frac{\tau(f)}D.                              \tag{NS10}
\]
d≤D 时内和≪d/D，每个 d 项≪1/D；d>D 时内和≤ζ(2)，
每项≪1/d≤1/D。这里放宽到全部正 ν 仅用于非负上界。
将 |g_D|²≪T^ε 与整个支持并集计数结合，得到
\[
 \sum_{x\asymp X}|g_D(fx)|^2\ll_\epsilon T^\epsilon X/D.
                                                               \tag{NS11}
\]
这对**全部 f**一致，不止小 f 或 ν≍D。原 A-unit 只减正能量。
它不是任意 n 列的普遍稀疏界，而是实际大平方除数系数的性质。

## NS6. 不缩短大筛长度，重跑全部 f 和物理外层

对 NT6 的 Φ_A 做 n/R、w/W_A 两变量光滑分离；H² 的绝对
Fourier 预算由同一 D200 支付，σ_A 的硬壳不参与平滑分离。
令 Y=W₀/f。共同 y 列 μ(y)σ_A(fy)1_{(y,fA)=1} 的平方能量
≪T^εY/C⁴；共同 x 列用 NS11。原 1/w 的归一化光滑部分可并入权。

正 y≍Y 的圆周频率1/y间距≳Y⁻²；用
[Kedlaya, Theorem 15.5](https://kskedlaya.org/ant/chap-largesieve.html)
的加性大筛及一次 Cauchy，固定 f 的裸双和平方至多
\[
 T^\epsilon C^{-4}(X/D)Y(X+Y^2).                  \tag{NS12}
\]
大筛因子仍是 **X+Y²**，不是 X/D+Y²。稀疏性只进入真实列能量。
Y 有界时直接吸收常数；若正 y 支撑为空则原和为空。

乘原 A⁻²w⁻¹，求全部 A,h,f；代入 X=R/f、Y=W₀/f，
两项的 f 幂分别为 −2、−3/2，完整求和收敛。于是
\[
 |\operatorname{Main}[g_D]|\ll\mathcal D_{200}T^\epsilon
 \frac{D^{-1/2}}{TC^2}
       \left(\sqrt{RW_0}+\frac R{\sqrt{W_0}}\right).             \tag{NS13}
\]
没有新谱假设，没有将一次 cancellation 用两次。Φ 的线性分离
付一份 D200，取平方／开方不导致最终 D200²。
NS8、NS13 及 R/E² 合起来才是精确积分投影的界。

## NS7. 14/15 余项及合法的平方自由剩余

写 UV=T^β、D=T^δ。在 η=6/5 下，上述六项指数完整为
\[
 -\frac25,\quad \beta-\frac75+\delta,\quad-\frac{52}5,\quad
 \frac{11}{10}-\frac\delta2,\quad\frac35-\frac\delta2,\quad\frac35.
                                                               \tag{NS14}
\]
取 U=V=T、δ=1/3，两主项同为14/15，得到
\[
 |P_E[(1-\mu^2)\Gamma_{II}]|
 =|P_E[(1-\mu^2)\Gamma_I]|
 \ll_\epsilon\mathcal D_{200}T^{14/15+\epsilon}.     \tag{NS15}
\]
将它与 #558 的 |P_E[Γ_I]|≪D200 T^(3/5+ε) 合回**同一**精确式，
\[
 \boxed{P_E[\mu]=P_E[\mu^2\Gamma_{II}]
                   +O_\epsilon(\mathcal D_{200}T^{14/15+\epsilon}).}
                                                               \tag{NS16}
\]
证明顺序为 −P_E[Γ_I]+P_E[(1−μ²)Γ_II]+P_E[μ²Γ_II]，
不是直接把原 II 的 n 限制为平方自由。
旧 NT9 对此带 mask 列重跑普通能量只有11/10；本稿将它降为14/15，
改善1/6。比较的是证明出的上界，不是实际有符号和的大小下界。

## NS8. 较大截断选项及未证部分

另可取 U=V=T^(11/10)、δ=1/5，NS14 六项均≤1，#558 的整个
Type-I 此时为 T^(4/5+ε)。因此以 O(D200 T^(1+ε)) 的代价，
剩余可改为 μ²(n)Γ_II(n)，b,c>T^(11/10)，商 m=n/(bc)≪T^(4/5)。
在平方自由 n 上才有 b,c,m 各平方自由且两两互素，以及
μ(b)μ(c)=μ(n)μ(m)；这些替换不能搬回原 unmasked Type-I/II。

仅就 NS8/NS13 的这种分账，要各项≤T 必须 δ≥1/5 且
β+δ≤12/5，故 β≤11/5。这是当前方法的费用条件，不是原算术和
的 no-go，也不声称更好的有符号处理不可能。
剩余平方自由双长和、其他 z/r/ℓ 投影、q₀/AFE 的全外层与统一尾
均未支付；不与 fixed H/L、频率带或别的投影直接叠乘节省。

## NS9. 原支持及有限守卫

脚本核查实际整数见证 T=72821、h=101、d=103、c₀=71、
q=16338163、g=3805463，n=g²=14481548644369，s=12067579587919。
这些因子皆素数，全部单位、最低 E 壳、n,s≤N/2、F_K 和 W 的
内部范围成立；U=V=T 时 Γ_I(n)=Γ_II(n)=1 而 μ(n)=0。
它说明这个被支付的非平方自由投影确有原支持，不能预删；
不保证任意给定权函数积分非零，也不是解析估计的数值证明。

运行 `python -B scripts/check_physical_native_nonsquarefree_type_ii.py`。
有限守卫包含完整有符号平方分解、ν/B 重叠、原单位容斥、精确
Euler 有限积、全部 f 支持计数、禁止 (x,f)、有理复权与原剖面的
有限重组、六项指数和实际支持。无限 ν 尾、Poisson 无限 j 尾与
大筛解析依据在 NS3–NS6，而非由这些测试外推。
本稿不改 Lean，不撤销 #490 的非平方自由范围纠错，不声称全局闭合。
