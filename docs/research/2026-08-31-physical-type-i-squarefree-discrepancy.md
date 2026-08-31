# 原 Type-I 的公共平方自由因子：全均值误差进入小重叠区

白话结论：先分解原 μ(n)，再合并单位掩码中的公共因子，可以支付
整个 Type-I 的一个明确误差，而不是只控制容斥后的小 f 子部分。
在 E=D≈T^(6/5)、短 cutoff 为对数幂时，该误差为
O(A₈T^(9/10+ε))。**显式均值仍是未估计的有符号和**；因此不宣称
整个 Type-I、centered C 或 coupled-kernel gate 已覆盖。

## TIQ0. 原式、版本与不改变的补集

本篇只用 [CP0–CP5](2026-08-31-physical-canonical-centered-pv.md)
冻结 9448c71da2cb69a0df0c9ebbe4fec6d9e200cd32 的同一个新光滑包。
定义源仍为 MWKF-PHYS-v1 的49cfacd70c60372757280177c7b63fd4f7760817；
canonical 映射为 #507 的 a24e1dca631dcaab04fc023d641ae3463cacff77。
旧硬 h/δ 包不适用；这里没有重新插入联合硬边缘。

固定平方自由 q₀，r=n、s=a₀b₀eq、h=a₀eu、δ=b₀ev。
a₀,b₀,e,q 正平方自由且两两互素，(q₀,a₀b₀eq)=1，
(n,q₀a₀b₀eq)=(u,b₀)=(v,a₀)=(uv,q)=1，uv≠0。
完整系数 μ(a₀)μ(b₀)μ(e)μ(q)μ(n) 和外权 2T/(q₀RS) 不变。
同一个 centered 核是
\[
 1_{(n,q)=1}\{e_q(-euv\bar n)-\mu(q)/\varphi(q)\}.
\tag{TIQ1}
\]
q=1 时此核恒零，其原 principal 不因此删除。

取 a₀∈[A₀,2A₀)、b₀∈[B₀,2B₀)、e∈[E,2E)、q∈[Q,2Q)，
M=A₀B₀、D=ME，非空时 DQ≈S。保留 CP 内部整包支持
q₀n,q₀s≤N/2，n/R∈[1/2,2]；HL≲RS/T，所有尺度为固定 T 幂。
A_J 是原 raw 核乘新 F(h/H)F(δ/L) 的半范数，本文取 J≥8。
特别地，FP1 的原 F_R(n)F_S(s) 已在 Ψ 中；n/R∈[1/2,2]
是光滑支持，不再另乘一个非冗余的 n 硬壳。否则 TIQ9 不能直接使用。

先把 n 的求和域扩至所有正整数：非平方自由 n 的原 μ(n)=0。
之后分解 μ(n) 时不得把平方自由限制留在无符号商中。
取正整数 cutoff U_c,V_c，假设 max(U_c,V_c)<R/2。
原 (9.241) 的有限卷积恒等式逐 n 给
\[
 \mu(n)=-\sum_{bc\mid n\atop b\le U_c,c\le V_c}\mu(b)\mu(c)
       +\sum_{bc\mid n\atop b>U_c,c>V_c}\mu(b)\mu(c).
\tag{TIQ2}
\]
不存在 mixed rectangle 或截断误差。定义原 C=I+II；下文只将
I 写成 M_I+E_I。II 保留原正号、全部 b,c、原 hδ 相位和共同权。
若不满足显示的 cutoff 条件，n≤max(U_c,V_c) 的原有限边界须另留。

## TIQ1. 在原 μ(n) 上分解，然后作精确公共因子重组

固定 a₀,b₀，置 A=q₀a₀b₀、B=bc、n=Bm。B 可有平方因子；
不要求 (b,c)=1。原单位条件给 (B,Aeq)=1 和 (m,Aeq)=1。
分离 (m,q)=1，对其余单位掩码展开
\[
 1_{(m,Ae)=1}=\sum_{w\mid A,\ w\mid m}\mu(w)
                 \sum_{t\mid e,\ t\mid m}\mu(t).
\tag{TIQ3}
\]
由于 (e,A)=1，每个除数的分配 t,w 唯一。置 e=ta、m=twz，
则 μ(e)μ(t)=μ(a)μ²(t)1_(a,t)=1。原式的 Type-I 因此恰等于
\[
 \begin{split}
 I=-{2T\over q_0RS}\sum
 &\mu(a_0)\mu(b_0)\mu(b)\mu(c)\mu(a)\mu(q)\mu(w)\\
 &\times\sum_{z\ge1,(z,q)=1}
   \{e_q(-auv\overline{Bwz})-\mu(q)/\varphi(q)\}
   \sum_{t\in[E/a,2E/a)\atop(t,aABq)=1}\mu^2(t)W(t,z).
 \end{split}
\tag{TIQ4}
\]
外和保留所有原 a₀,b₀,q,u,v，b≤U_c,c≤V_c、w|A、1≤a≤2E。
其条件完整为 a,q 平方自由、**(q,A)=1**、(B,Aq)=1、
(a,ABq)=1、(u,b₀)=(v,a₀)=(uv,q)=1；t 的条件已显示。
没有 (z,a)、(z,t) 或 (b,c) 掩码。a=2E 若为整数也可纳入：
其 t 整数域为空，不改变恒等式。

真实权没有换成模型：
\[
 W(t,z)=p_N(q_0Btwz)p_N(q_0a_0b_0atq)
 \Psi(Btwz/R,a_0b_0atq/S,b_0atv/L,a_0atu/H).
\tag{TIQ5}
\]
t 来自单位容斥，不是新的原 gcd 层；μ²(t) 来自显示的乘法恒等式，
不是把原 μ(e) 偷换成正号。所有 hδ 标签仍在 TIQ5 中。

## TIQ2. 平方自由均值及其统一 z 导数

令 Y=E/a≥1/2、Z=Ra/(BwE)，记
\[
 c(J)=\zeta(2)^{-1}\prod_{p\mid J}{p\over p+1},\qquad
 D_a(z)=\sum_{t\in[Y,2Y)\atop(t,aABq)=1}\mu^2(t)W(t,z)
                 -c(aABq)\int_Y^{2Y}W(t,z)\,dt.
\tag{TIQ6}
\]
这是包含半开端点的定义，不将离散和声称等于密度。
将 μ²(t)=Σ_(d²|t)μ(d) 和单位掩码作有限展开、使用整数 floor 计数，得
\[
 \sum_{t\le x,(t,J)=1}\mu^2(t)=c(J)x+O(\tau(J)\sqrt x),
 \qquad x\ge1/2.
\tag{TIQ7}
\]
证明中 d≤√x 的整数误差为 O(τ(J)√x)；补齐 d>√x 的密度尾
至多 xΣ_(d>√x)d^-2≪√x。x<1 的空整数域也满足该界。
任一左右端点可由同一 O(1) 跳跃费用处理。

以 ξ=t/Y、ζ=z/Z 写 TIQ5 的原四坐标为
\[
 \xi\zeta,\quad {a_0b_0Eq\over S}\xi,\quad
 {b_0Ev\over L}\xi,\quad {a_0Eu\over H}\xi .
\tag{TIQ8}
\]
所有系数在非空包上一致有界；原内部 taper 同样光滑。
固定 t∈[Y,2Y) 时，n/R 支持迫使 ζ∈[1/4,2]。
对 TIQ7 作 Abel 求和，并将每个 z 导数留在 W 中，得到
\[
 Z^j\|D_a^{(j)}\|_\infty
       \ll_j\mathcal A_{j+1}T^\epsilon\sqrt{E/a},\quad 0\le j\le4.
\tag{TIQ9}
\]
D_a 是上述固定 ζ 紧区间上的光滑函数，向外延拓为零。
t 的硬端点 Y、2Y 不依赖 z，没有联合 z 角点；这里没有使用
一般硬 h/δ 包的五变量 Fourier 分离。需要的 t 总变差只多一阶导数。

定义 M_I 为 TIQ4 中替换内层 t 和为 TIQ6 密度积分的完整有符号和，
E_I 则替换为 D_a。于是 I=M_I+E_I 精确；M_I **仍乘同一个 centered
z 核**，不是原 Ramanujan principal，也不是 canonical zero Gram。

## TIQ3. 对误差作全部 z-Poisson，而非只选本原频率

固定外参数，λ=−auv inverse(Bw) mod q 为单位。
记 K(z)=1_(z,q)=1[e_q(λ inverse(z))−μ(q)/φ(q)]，
其完整 Fourier 系数（正号约定）为
\[
 K^+(k)=S(k,\lambda;q)-{\mu(q)\over\varphi(q)}c_q(k),
 \qquad K^+(0)=0.
\tag{TIQ10}
\]
使用标准 Weil–Estermann 界
|S(k,λ;q)|≤τ(q)√q，因为 (λ,q)=1；无需 k 为单位。
可对照 [Tao–Teräväinen §3.5](https://londmathsoc.onlinelibrary.wiley.com/doi/full/10.1112/jlms.12663)。
本篇仅使用该无条件标准输入，不使用该论文的 Siegel-zero 假设结论。
另 |μ(q)c_q(k)/φ(q)|≤1，故所有 k 的非零系数均≪T^ε√q。

以 hatD(ξ)=∫D(z)e(−ξz)dz，完整 Poisson 为
\[
 \sum_z K(z)D_a(z)={1\over q}\sum_{k\ne0}K^+(k)\widehat D_a(k/q).
\tag{TIQ11}
\]
由 TIQ9，hatD 的界是 A₈T^ε Z√(E/a)(1+|ξ|Z)^−4。
同时保留 1/q 和 Z，并求和全部 k，得
\[
 \left|\sum_z K(z)D_a(z)\right|
 \ll\mathcal A_8T^\epsilon\sqrt{Eq/a}
                  \min\{1,(q/Z)^3\}.
\tag{TIQ12}
\]
Z/q≤1 和 >1 分别用积分比较与 Σk^-4；没有漏掉低导子 k。
若仅保留 |k|≤K₁，K₁≥1，剩余尾另有
A₈T^ε√(Eq/a)(1+K₁Z/q)^−3 的绝对 majorant。
有限外参数后此尾可和，故本篇无需将无限频率当作对数多个。
q=1 直接取零，不用 Weil 估计。

令 A*=BwEq/R。对所有 A*>0，
\[
 \sum_{a\ge1}a^{-1/2}\min\{1,(A^*/a)^3\}\ll\sqrt{A^*}.
\tag{TIQ13}
\]
A*≥1 时在 a=A* 分段；A*<1 时左边为
(A*)³Σa^-7/2≪√A*。不能添加破坏小 A* 收益的常数项。
原 a≤2E 的非负预算可扩到此和。因此已付全 a 的误差为
\[
                     \ll\mathcal A_8T^\epsilon E q\sqrt{Bw/R}.
\tag{TIQ14}
\]

## TIQ4. 全外层费用与新控制的误差区域

真实标签数≪HL/(a₀b₀E²)：当 H/(a₀E) 或 L/(b₀E)<1/2 时
对应域为空；否则两个整数 +1 各由实际长度支付。
另有
\[
 \sum_{b\le U_c,c\le V_c}\sqrt{bc}\ll(U_cV_c)^{3/2},\quad
 \sum_{w\mid q_0a_0b_0}\sqrt w\ll T^\epsilon\sqrt{q_0a_0b_0},\quad
 \sum_{a_0,b_0}(a_0b_0)^{-1/2}\ll\sqrt M,\quad
 \sum_{q\in[Q,2Q)}q\ll Q^2.
\tag{TIQ15}
\]
整数1的壳可取尺度1；其他非空尺度≥1/2，故以上费用统一。
还原唯一的 2T/(q₀RS) 后，得到实际 Type-I 均值误差定理
\[
 \boxed{|E_I|\ll_\epsilon
 {\mathcal A_8T^{1+\epsilon}HLQ^2\sqrt M(U_cV_c)^{3/2}
             \over\sqrt{q_0}\,R^{3/2}SE}.}
\tag{TIQ16}
\]
它不是固定 a、t、q 或 w 的单行结果。双 Möbius short 系数保留至
估计步骤；最后误差上界只使用它们的模长，不声称获得 μ 专属 saving。

在 q₀=1、R=S≈T³、HL≈T⁵、E=T^η、D=T^δ、U_cV_c=T^β 的
内部平衡区域，TIQ16 的指数准确为
\[
                    {9\over2}-{3\over2}(\eta+\delta)+{3\over2}\beta.
\tag{TIQ17}
\]
因此 η+δ≥7/3+β 支付这个误差。FP3 的 δ=η=6/5、β=0 给9/10；
δ=η=7/6、β=0 给1。若 β=1/30、η=δ=6/5，仍为19/20。
这些条件不等于整个 centered C 的覆盖；
[DP14，冻结 7cc9646c](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/7cc9646c8b8a8589b920e24652c86bd063f4b1d7/docs/research/2026-08-31-physical-centered-character-poisson.md)
的5/4阈值估计的是
整个指定 centered 包，不能把本篇的误差7/6阈值当作替代它。

TIQ17 的原支持有无限非空族：取互异素数 e≈Y²、q≈Y³，
R=S=eq、N=8S、T=(8S)^(1/3)、Kz=Mz=√T、H=L=S/√T。
a₀=b₀=q₀=1，u=v=ceil(H/e)≈Y^(13/6)<q；另取素数n∈(S,2S)。
所有原单位条件及 genuine overlap=e 成立；原连续变量x=3√T/4
给 (xn+δ)/s∈[√T/2,2√T]。有限 dyadic 取整只改常数。
Type-I 中 b=c=1 确实存在；不宣称某一任意权的误差非零或正密度。

## TIQ5. 下一项真正要估计的是什么

精确剩余为原 C=M_I+II+E_I。可在 TIQ16 区域把 E_I 作为已经支付
的加法误差；**M_I+II 必须保留符号后共同估计**，其余尺度与外层也在。
M_I 的显示系数是 −μ(a₀)μ(b₀)μ(b)μ(c)μ(a)μ(q)μ(w)c(aABq)，
乘 TIQ4 的 centered 核和 TIQ6 的原 t 积分。密度依赖 a、B、q，
不能写成一个全外层共同的常数，更不能直接引用全局 principal 界。
没有证明这个有符号均值小，也没有证明它与 II 抵消。

只对本均值沿同样的 z 完成并取绝对值，固定 a 的费用至多
A₈T^ε(E/a)√q。这里密度≤1，原积分的导数预算是 E/a 而非
误差的 √(E/a)。求全部 a≤2E 支付 log(2E)，求 w|A 只需 τ(A)，
短 b,c 行数为 U_cV_c；原标签计数消去 a₀b₀ 的调和外和。
因此整个均值的一个粗界是
\[
 |M_I|\ll_\epsilon
 {\mathcal A_8T^{1+\epsilon}HLQ^{3/2}U_cV_c\over q_0RSE}.
\tag{TIQ18}
\]
它给出 T^(9/2−η−3δ/2+β+ε) 的平衡预算；η=δ=6/5、β=0 时为3/2，
仍比目标1大。它是当前上界的缺口，不是均值的下界或 no-go。
本篇不重定义 gate，不新增条件性 Lean 接口，不证明完整 twisted
moment、2/3 或14/17；只减少同一实际分解中需联合处理的一项误差。

English summary: split the original n-Mobius factor before coprimality
completion. Fuse the common divisor into an unsigned squarefree variable,
subtract its exact-density integral, and complete the error in the remaining
integer quotient with every frequency and outer cost retained. The resulting
error reaches the target below E=T^(5/4), but its signed mean and Type II do not.
