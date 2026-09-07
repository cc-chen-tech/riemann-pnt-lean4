# 原始 MWKF 的 canonical gcd 适配：支付全部 a/b/e 分配

白话结论：产品标签 L² 估计不仅适用于 h、δ 同时被同一 e 整除、
没有其他分配的 FP3 层。对原平方自由模数 s，把只整除 h、只整除 δ、
两边同时整除的素数分别放入 a、b、e，可以唯一还原原式，并保留全部
交叉互素条件。支付所有 a/b/e 行数后，大共同因子 e≥T² 的平衡内部
区域仍满足局部 T^(1+ε) 预算。这扩展了真实 gcd 分配范围；不是新的
e-Möbius 消去，也没有覆盖 e<T²、全部外层或完整 twisted moment。

## CA0. 版本、输入和不变的物理权

原定义源固定为 `49cfacd70c60372757280177c7b63fd4f7760817` 的
`docs/research/2026-08-24-mobius-weighted-off-diagonal.md` (4.4)–(4.5)、
(5.13b)、(5.15)、(6.0)。命名使用 [MWKF-PHYS-v1 的 FP1–FP4](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/7cf2e7d43c4365e38e2aa708d1a250694b698bec/docs/research/2026-08-30-mwkf-frozen-physical-atom.md)。
估计源固定为 `933bb6087d399d006c6963489b7e2cda22e2ba24` 的
[产品标签稿 P1–P10](2026-08-31-physical-product-label-l2.md)，及其父
`5b98572f27695b2404d290be3dfcda8274f20285` 的
[平方自由下降稿 D3–D13](2026-08-31-physical-squarefree-type-descent.md)。

固定一个原平方自由 q₀ 和一个光滑 h/δ 壳。原和为
\[
 \mathcal O={2T\over q_0RS}\sum_{r,s,h,\delta}
 \mu(r)\mu(s)p_N(q_0r)p_N(q_0s)
 \Psi(r/R,s/S,\delta/L,h/H)e_s(-h\delta\bar r).       \tag{CA1}
\]
这里 r,s>0、hδ≠0，(r,s)=(q₀,rs)=1，非零 Möbius 系数使 r,s
平方自由。整数 mollifier 支持、原 Ψ 的连续积分和光滑壳全部不变。
两个 AFE 方向已经包含在唯一的 2T/(q₀RS) 中。

本篇估计只用于 FP §3 的光滑内部箱：HL≲RS/T，尺度在固定 T 的幂
范围内，\(\mathcal A_J=\max_{|\mathbf j|\le J}\|\partial^{\mathbf j}\Psi\|_\infty\)
显式支付，J≥6。不对原积分支持新增不光滑的 n/q 切割。更大 log core
须另付其原半范数。所有 dyadic 约定可取 [X,2X)，从 X=1 开始；
因此整数1不遗漏，也不重复边界。h、δ 两种符号都在。

## CA1. 唯一原式参数化，不是容斥中的一个正项

对 CA1 中一个非零项，定义
\[
 e=(s,h,\delta),\quad a={(s,h)\over e},\quad
 b={(s,\delta)\over e},\quad q={s\over abe},\quad
 n=r,\quad u={h\over ae},\quad v={\delta\over be}.    \tag{CA2}
\]
由于 s 平方自由，每个 p|s 恰落入以下四类之一：只整除 h、只整除 δ、
同时整除两者、两者都不整除。这证明 a,b,e,q 平方自由且两两互素，
并且
\[
 (a,v)=(b,u)=(uv,q)=1,\qquad
 (n,q_0abeq)=(q_0,abeq)=1.                            \tag{CA3}
\]
反过来，任取正平方自由、两两互素 a,b,e,q，n>0、uv≠0，满足 CA3，
置
\[
 s=abeq,\quad r=n,\quad h=aeu,\quad\delta=bev.        \tag{CA4}
\]
逐素数重新检查上述四类即得 CA2。因此 CA2–CA4 在继承原支持后是
精确双射，没有 multiplicity、容斥系数或除数函数损失。准确地有
\[
 (s,h\delta)=abe,\qquad(s,h,\delta)=e.                \tag{CA5}
\]
这里 abe 是完整 genuine gcd，e 只是共同重叠；不得把两者互换。
例如删去 (a,v)=1 就会把本应进入 e 的素数误记进 a。

原模数到约化模数的相位及系数逐项为
\[
 e_s(-h\delta\bar n)=e_q(-euv\bar n),\qquad
 \mu(n)\mu(s)=\mu(a)\mu(b)\mu(e)\mu(q)\mu(n).         \tag{CA6}
\]
第一式只用 hδ=ab e²uv 与模 q 的逆元一致性；没有额外 e 的逆元。
完整权是 p_N(q₀n)p_N(q₀abeq)Ψ(n/R,abeq/S,bev/L,aeu/H)。
若 q=1，e₁=1，逆元相位按唯一剩余类理解。
这是原式真正子族，µ(e) 不可换为 µ²(e)；没有从 signed overlap
容斥式里只抽出第三个正项。

## CA2. 同一产品标签估计所需的共同列与掩码

限制 a∼A、b∼B、e∼E、q∼Q，记 D=ABE，非空支持要求 DQ≈S。
固定 a,b,e，置 U=H/(ae)、V=L/(be)。若某标签域为空，该行严格为0；
非空时 U,V≥1/2。Type 分层使用新的字母 f=(k,q)，q=fℓ，避免与
genuine gcd 混淆。f、ℓ 平方自由互素，(abeq₀,fℓ)=1。

四变量分离仍只在
\[
 n/R,\quad\ell/(Q/f),\quad u/U,\quad v/V             \tag{CA7}
\]
上进行，因为 abe fℓ/S=(abeQ/S)(ℓ/(Q/f))，另外两变量恰为 v/V、u/U。
abeQ/S 在非空 shell 上上下有固定界，故 Fourier 系数绝对和
≪A_J 对 a,b,e,f 一致。与产品稿相同，J≥6 足以支付四变量分离。
算术逆元从不充当实光滑因子。

每个分离原子可取
\[
 \begin{split}
 x_n&=\mu(n)p_N(q_0n){\bf1}_{(n,q_0abef)=1}
                         \times\text{共同 n 因子},\quad\sum_n|x_n|^2\ll R,\\
 y_u&={\bf1}_{(u,b)=1}\times\text{有界 u 因子},\quad
 z_v={\bf1}_{(v,a)=1}\times\text{有界 v 因子},\\
 \beta_{f\ell}&=\mu(f\ell)p_N(q_0abe f\ell)
                         \times\text{有界模数因子}.
 \end{split}                                               \tag{CA8}
\]
固定 µ(a)µ(b)µ(e) 留在外，绝对值≤1；p_N 的原整数支持属于其单变量。
尚有 (n,ℓ)=1 留在 x 列的求和中，(uv,fℓ)=1 留在**完整标签和内**，
(ℓ,q₀abef)=1 留在允许模数集合。这既不要求跨 a,b,e 共同 n 列，
也没有删除那些掩码：对每个 a,b,e 分别用估计，费用下一节全额汇总。

将产品稿 P3 中 e 保留，标签改为 CA8 的 y、z，则 W_ℓ、Z_ℓ、K_ℓ
使用完全相同的 (uv,fℓ)=1 掩码。CA3 新增的两个单变量删项不破坏
整数产品碰撞界：每个 z=uv≠0 的表示数仍≤2τ(|z|)。准确 Type 行为
\[
 {\mu(f)\over f}\sum_{\ell\asymp Q/f}{\beta_{f\ell}\over\ell}
 \sum_{t\in U(\ell)}\left(\sum_{(n,\ell)=1}x_ne_\ell(-tn)\right)
 \sum_{u,v\atop(uv,f\ell)=1}y_uz_v B_\ell(t,euv\bar f). \tag{CA9}
\]
µ(f) 是中心核下降的系数，不是外 µ(e)，也不是新发现的 Möbius saving。
ℓ=1 的中心核为0；原 q=1 项及所有 q 的 principal 不因此消失。

单位条件大筛允许任意 x_n：其容斥只产生 x_(dn)，不要求 µ(n) 的
乘法性。其解析输入为通常 [加性大筛](https://kskedlaya.org/ant/chap-largesieve.html)，
单位 lift、各层预算用已固定的 D3–D9。产品稿 P4 的负均值项使用同一
掩码，P5–P9 的证明原样适用。故每个 a,b,e 行（包括全部 f）有
\[
 \ll_\epsilon\mathcal A_J T^\epsilon
 \{\sqrt{UV}\sqrt{QR(R+Q^2)}
                  +UV[R\log(2Q)+\sqrt R\,Q]\}.        \tag{CA10}
\]
此式允许任意上述有界复系数。它没有对 e 或 n 获得 Möbius 特异抵消。
原 principal 是 µ(q)/φ(q) 乘原单位列和标签和；对 q∼Q 求绝对值给
≪A₀ RUV Q^ε，包含在 CA10 第二项，q=1 单列亦如此。只算一次账。

## CA3. 全部 a/b/e 成本与真正的新覆盖

不能把 CA10 的一行当作整个族。半开 dyadic shell 上，直接计数给
\[
 \begin{split}
 \sum_{a\sim A,b\sim B,e\sim E}\sqrt{UV}
 &=\sqrt{HL}\sum_{a,b,e}{1\over e\sqrt{ab}}
       \ll\sqrt{HL}\sqrt{AB}=\sqrt{HL D/E},\\
 \sum_{a\sim A,b\sim B,e\sim E}UV
 &=HL\sum_{a,b,e}{1\over ab e^2}\ll HL/E.
 \end{split}                                               \tag{CA11}
\]
限制为平方自由、互素只会减少这两个非负预算，不曾从原 signed 和里
删除符号。恢复唯一外权，得到该 canonical 子族的界
\[
 \boxed{|\mathcal O_{A,B,E,Q}|\ll_\epsilon
 {\mathcal A_J T^{1+\epsilon}\over q_0RS}
 \{\sqrt{HL D/E}\sqrt{QR(R+Q^2)}
                 +{HL\over E}[R+\sqrt R\,Q]\}.}       \tag{CA12}
\]
固定有限高度版本保留 CA10 的 log(2Q) 和产品/大筛的除数预算；T^ε
只在已声明固定幂尺度下吸收它们，没有丢掉一个外层幂次。
由 DQ≈S、HL≲RS/T，进一步得到
\[
 \boxed{|\mathcal O_{A,B,E,Q}|\ll_\epsilon
 {\mathcal A_J T^\epsilon\over q_0}
 \left\{\sqrt{T(R+Q^2)/E}+{R+\sqrt R\,Q\over E}\right\}.} \tag{CA13}
\]
因 R+√R Q≤(3/2)(R+Q²)，一个局部 T/q₀ 预算充分条件是
\[
                    E\gtrsim(R+Q^2)/T.                \tag{CA14}
\]
该条件只在此前所述真实光滑内部支持下使用。

平衡内部 R=S≈T³、H=L≈T^(5/2) 中，D≥E，E≥T² 给
Q≈S/D≲T，因而满足 CA14。对这些 a/b/e/q dyadic 子盒求和只新增
固定次 logT；所以在固定 q₀、固定原物理箱内，**全部 canonical 分配中
共同重叠 (s,h,δ)≥T² 的线性子和**满足 O(A_J T^(1+ε)/q₀)。
这比 FP3 的 a=b=1 多出真正的原式区域，不是降低了 e 的阈值。

例如 E=T^(9/4)、D=T^(13/5)、A=B=T^(7/40)、Q=T^(2/5)，CA13 为
T^(7/8+ε)+T^(3/4+ε)。该族直接计数预算为 RS/(DE)=T^(23/20)，
故相对该上界改善 11/40。a、b 都随 T 增长，确实不是 FP3 子族。
这里比较的是两种上界，不断言原和有 T^(23/20) 的下界。

## CA4. 渐近非空族与边界

由 Bertrand 定理在相应倍长区间取互异素数
a≈Y⁷、b≈Y⁷、e≈Y⁹⁰、q≈Y¹⁶；a,b 可用相邻不交倍长区间。
令 S=R=abeq、N=8S、T=(8S)^(1/3)≈Y⁴⁰，Kz=Mz=√T，
H=L=S/√T。取 u=⌈H/(ae)⌉、v=⌈L/(be)⌉，均≈Y³，最终小于
a,b,q。因此 CA3 中交叉标签单位条件全成立。再取素数 n∈(S,2S)，
它大于 a,b,e,q，所以 (n,abeq)=1，取 q₀=1。

有 H≤aeu≤2H、L≤bev≤2L，n,s≤N/4。连续原变量 x=3√T/4 满足
(xn+δ)/s∈[√T/2,2√T]（充分大 Y），KzMz=T，R=S，故原整数域与
连续积分支持相容。有限相邻 dyadic 取整只改变常数。此构造不要求
短区间素数密度，也不声称任意指定 F/W 的积分在这些点必非零。

整数映射没有截断误差，原端点直接继承，hδ=0 不在原和中；e=1、
a=1、b=1、q=1 由上述约定覆盖。若 e>2min(H/a,L/b)，该行为空。
在非空域中只用 (1+UV)^ε，避免 U,V<1 时不合法记号。

## CA5. 可形式化的有限命题与余项账

有限命题：对任意有限支持复权 F(n,s,h,δ)，在平方自由 s、n>0、hδ≠0、
(n,q₀s)=(q₀,s)=1 的域上，CA2 与 CA4 给双射；把 F 拉回为
F(n,abeq,aeu,bev)，并按 CA6 替换 Möbius 系数和有理相位，所得有限和
严格相等。选定 canonical dyadic 子族相当于在原域乘其唯一指示函数。
不涉及无穷交换、解析延拓或假设性范数接口，适合单独形式化。

CA12–CA14 是应用现有产品估计后的解析上界，而不只是上项的有限
恒等式。有限回归脚本只守卫双射、掩码、符号、相位、Type 完成、
权坐标、计数与指数；它不能代替加性大筛或统一平滑预算的证明。

尚未估计的线性补集保留为原共同 signed 算子。若整个余项写成 E+C，
二次能量仍保留 EE*+EC*+CE*+CC*；这里没有逐块删除 cross 项。原 AFE
对角、canonical zero Gram、Ramanujan principal 和反射边界不是可互换
的对象，本篇没有重新加减其中任何一个。全局 principal 的另一套
重组不能未经映射直接用作单个 canonical 子层的估计。

e<T² 的平衡域、其他物理尺度和尾部、原 q₀ 聚合、XI 的 b=A*a_N 及
共同 Π 输出迁移均不在本定理内。PR 合并仅认证这一局部推进；完整
coupled-kernel gate、twisted moment 和零点排除仍未证明。

English summary: uniquely assign each prime of the original squarefree s to
the h-only, delta-only, shared, or residual factor. The exact pullback retains
all cross-unit masks and the original normalization. Paying every a/b/e row
extends the product-label bound to all canonical allocations with shared gcd
at least T² in the specified balanced interior. This is not new Möbius
cancellation or a full off-diagonal theorem.
