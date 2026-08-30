# 全平方自由模数：以联合四因子计数支付 Type-II 短乘积

白话结论：先完成三个变量，再把两个 Möbius 因子的乘积一起计数，
可以直接支付非零整数 determinant；不必要求模数接近素数，也
不必把全部非零同余推到 Fourier 尾。原 E≈T^(6/5) 的 smooth
包中，bc≤T^(11/10) 的费用从逐项预算 T^(17/10+ε) 降为
O(A₁₂T^(9/10+ε))。这是新覆盖的真实短乘积范围，不是完整
twisted moment；更长的 signed Type-II 补集仍未支付。

## HY0. 固定来源、归一化与原子

定义源是 [TTC0–18](2026-08-31-physical-type-i-triple-completion.md)
的 779c0cffb51a0e834d39ea86f5571a5d21b1f008，其上游为
MWKF-PHYS-v1 的49cfacd7和 CP 的9448c71d。直接代码父版本是
#526 的1853d6c0f2e1b9573cea3370dcfc323acefdcc1e。
[PII3–12](2026-08-31-physical-type-ii-prime-incidence.md)
固定于 b33add1b6bd494a226e5ab00d3b3ced26b0d17c2。
本篇不修改这些冻结稿，且不使用一般硬 h/δ 包的旧范围声明。

仍仅选择 q₀=a₀=b₀=1 的同一真实 FP3 线性子族：
\[
 r=n,\quad s=eq,\quad h=eu,\quad\delta=ev,\qquad
 e\in[E,2E),\ q\in[Q,2Q)\quad\hbox{squarefree},\quad(e,q)=1.
\tag{HY1}
\]
这里 Q≥2，R≈S≈EQ，所有比较常数固定；uv≠0，
(n,eq)=(uv,q)=1。原系数为 μ(e)μ(q)μ(n)，唯一外权
2T/(RS)。原 principal 已从本 centered 对象分出，不能移来支付
本篇任何成本。Ψ 是 FP1 重插光滑单位分解所得的原核，含原
F_R(n)F_S(s) 和 smooth h/δ 权；整包满足 n,s≤N/2。
假设 HL≲RS/T，所有参数及其非零倒数在固定 T 幂范围。
A_j 是这一个原核（含 taper）的归一化 j 阶导数预算，不能
因写成 Fourier 积分而省去它。

取正整数 U_c,V_c 且 max(U_c,V_c)<R/2。TTC2 逐整数给出
\[
 C=I+II,\qquad
 \mu(n)=-\sum_{bc\mid n\atop b\le U_c,c\le V_c}\mu(b)\mu(c)
       +\sum_{bc\mid n\atop b>U_c,c>V_c}\mu(b)\mu(c).
\tag{HY2}
\]
定义 II_≤ 为 B=bc≤B_* 的第二和，II_> 为其精确补集。
展开前把 n 的平方自由限制用 μ(n)=0 扩展掉；展开后不能补回。
也没有 (b,c)=1 或商变量平方自由条件。若上述截断端点不满足，
须另保留有限 μ 边界，本篇不认证该情形。

## HY1. 全单位容斥与实际非分离权

固定 e,q,b,c，保留 (B,eq)=1。令 n=Bm，展开
1_(m,e)=1=Σ_(d|e,d|m)μ(d)，置 m=dz、a=e/d。于是
\[
 \alpha=a\bar B\bmod q,\quad (aB,q)=(a,B)=1,\qquad
 Z_B={R\over Bd},\quad X={H\over e},\quad Y={L\over e}.
\tag{HY3}
\]
完整系数 μ(e)μ(q)μ(b)μ(c)μ(d)，余下掩码恰为 (zuv,q)=1。
没有 μ(z)、(z,a)、(z,d) 或 (b,c) 掩码。实际权为
\[
 W_B(z,u,v)=p_N(Bdz)p_N(eq)
       \Psi(Bdz/R,eq/S,ev/L,eu/H).
\tag{HY4}
\]
归一化坐标 (z/Z_B,eq/S,v/Y,u/X) 给一致导数预算，不产生 B,d
导数损失。z>0、z≤2Z_B，标签非零、|u|≤2X、|v|≤2Y，权在
三个零坐标附近为零；端点光滑，不附加非冗余硬壳。
若 Z_B、X、Y<1，原整数集合可以为空，直接给零。

## HY2. 使用完整谱，保留所有合数非单位频率

令 e_q(t)=exp(2πit/q)。原 centered 周期核是
\[
 K_{q,\alpha}(z,u,v)=\mathbf1_{(zuv,q)=1}
   \{e_q(-\alpha uv\bar z)-\mu(q)/\varphi(q)\}.
\tag{HY5}
\]
正号有限 DFT 记为 H_q(k,ρ,σ)，负号连续变换记为 Ŵ_B。
TTC4–7 对每个平方自由 q 给出三条完整零坐标面，以及
\[
 H_q(0,\rho,\sigma)=H_q(k,0,\sigma)=H_q(k,\rho,0)=0,\qquad
 |H_q(k,\rho,\sigma)|\le(\tau(q)+1)q\,(q,ak+B\rho\sigma).
\tag{HY6}
\]
乘 B 是模 q 单位，故 gcd 形式不变。合数 q 的其他非单位频率
不能删除：q=6、α=1、k=ρ=σ=2 时 H_q=−9/2。
同样，素数 q=5、α=k=ρ=σ=1 时 H_q=−25/4，不是零；
中心校正常数已在此完整 H_q 内，后面不再另加或另删一项。

完整 Poisson 是
\[
 \sum_{z,u,v}W_B K_{q,\alpha}
 ={1\over q^3}\sum_{k,\rho,\sigma\ne0}
          H_q(k,\rho,\sigma)\widehat W_B(k/q,\rho/q,\sigma/q).
\tag{HY7}
\]
这里三个频率是不为零的整数，不是模 q 单位。
逐轴 J 阶、混合总阶3J的导数界给
\[
 |\widehat W_B|\ll_J A_{3J} Z_BXY
 (1+|k|Z_B/q)^{-J}(1+|\rho|X/q)^{-J}
 (1+|\sigma|Y/q)^{-J}.
\tag{HY8}
\]
J=4 足以使全部频率绝对收敛；下面给出求完所有外层后仍一致
可和的 majorant。有限外和可以与这些绝对收敛和交换。

## HY3. 可直接形式化的联合有限计数

给正整数 a,D,q 和正实数 K',R',S'，令
\[
 \Delta=ak+bc\rho\sigma,\quad
 \mathcal B=\{b,c>0:D\le bc<2D\}.
\]
可以给 b,c 附加任意子集掩码。三频率非零且分别在
|k|≤K'、|ρ|≤R'、|σ|≤S'。记
N_*=2DR'S'，D_*=aK'+N_*，
M₄(N_*)=max_{1≤n≤floor(N_*)}τ₄(n)，空最大值取0。
则严格有限命题为
\[
 \boxed{\sum_{\mathcal B}\sum_{k,\rho,\sigma\ne0\atop\Delta\ne0}
     (q,\Delta)
 \le 8M_4(N_*)K'D_*\sum_{v\mid q}{\varphi(v)\over v}.}
\tag{HY9}
\]
证明：展开 (q,Δ)=Σ_(v|q,v|Δ)φ(v)，置 Δ=vj。
由于本项只含整数 Δ≠0，j≠0，有
0<|j|≤D_*/v。固定 k,j 后
\[
 bc\rho\sigma=vj-ak.
\tag{HY10}
\]
右端为零时原表示数严格为零，不能调用 τ₄(0)。非零时正 b,c
和有符号非零 ρ,σ 至多给 2τ₄(|vj−ak|) 个表示；两个符号选择
正好来自 ρ、σ 的乘积符号。所有原范围、单位条件只减少表示数。
又 |vj−ak|=|bcρσ|≤N_*，非零 k、j 的个数分别≤2K'、
2D_*/v，得到 HY9。**全部 b,c 已被计入 τ₄，不能再乘 D。**
所有尺度小于1的情形也严格成立：非零整数个数没有“+1”；
N_*<1 时原集合为空。

这不是要求每对 b,c 分别抵消。HY9 在三变量完成后联合计数
全部 b,c,ρ,σ，甚至不使用 μ(b)μ(c) 的特殊符号。

## HY4. 非零整数 determinant 与全部无限尾

固定 e,q,d，分一个乘积 dyadic 壳 D≤bc<2D，D≥1。自然尺度取
\[
 K={qDd\over R},\qquad L_1={qe\over H},\qquad L_2={qe\over L}.
\tag{HY11}
\]
对该壳 HY8 可统一放大为
A₁₂ RHL/(Dde²) 乘三个相应衰减因子，比较常数固定。
把每轴分成 |frequency|≤natural scale 和
2^(j−1)natural scale<|frequency|≤2^j natural scale，j≥1。
写 λ_k,λ_ρ,λ_σ 为对应的1或2^j。在该壳 HY9 给
\[
 \sum_{bc}\sum_{\Delta\ne0}(q,\Delta)
 \ll_\epsilon T^\epsilon(\lambda_\rho\lambda_\sigma)^\epsilon
  (\lambda_k K)
    \{a\lambda_k K+2D\lambda_\rho\lambda_\sigma L_1L_2\}.
\tag{HY12}
\]
此处 Σ_(v|q)φ(v)/v≤τ(q)，而
τ₄(n)≪_ε n^ε。只把固定 T 幂的自然尺度吸收到 T^ε；
无限 λ 的增长显式保留。对任意给定目标 ε，可先选较小的
除数界指数，且小于1/2，再重新命名为 ε。

HY6、HY7 的 q/q³，加上 Fourier 体积，给归一化因子
RHL/(Dde²q²)。两项精确化简为
\[
 {RHL\over Dde^2q^2}\,K(aK)={DHL\over eR},\qquad
 {RHL\over Dde^2q^2}\,K(DL_1L_2)=Dq.
\tag{HY13}
\]
因此在该 dyadic 频率壳上，完整 majorant 为常数倍
\[
 A_{12}T^\epsilon
 (\lambda_k\lambda_\rho\lambda_\sigma)^{-4}
 (\lambda_\rho\lambda_\sigma)^\epsilon
 \left\{ {DHL\over eR}\lambda_k^2
       +Dq\lambda_k\lambda_\rho\lambda_\sigma\right\}.
\tag{HY14}
\]
三个独立几何级数均收敛。这同时支付所有大频率尾、很小的
自然频率尺度和所有非零 q 倍数；没有频率间隙假设 Λ。
特别地 Δ≠0 不等于 q∤Δ，非零 q 倍数仍在 HY12 内。
原 K,L₁,L₂ 小于1时，开头若干频率壳只是空集，不能把它们
补成1再计数。本项对固定 e,q,d,D 总费用为
\[
 \ll_\epsilon A_{12}T^\epsilon
              D\{HL/(eR)+q\}.
\tag{HY15}
\]

## HY5. 整数 Δ=0 的全部共振

因为 (a,B)=1、三频率非零，Δ=0 精确等价于
\[
 k=Bt,\qquad\rho\sigma=-at,\qquad t\ne0.
\tag{HY16}
\]
HY6 在此给 |H_q|/q³≤(τ(q)+1)/q，无需 q 为素数。
对每 t，标签表示数至多2τ(a|t|)；由 R≈eq，
|k|Z_B/q≈a|t|。所以全部 d|e 的共振，逐固定 B,e,q 为
\[
 \ll A_{12}T^\epsilon{XY\over B}
       \sum_{a\mid e}\tau(a)a^{-3}
       \sum_{t\ge1}\tau(t)t^{-4}
 \ll A_{12}T^\epsilon {XY\over B}.
\tag{HY17}
\]
两个无限级数收敛；不能把无限 t 的 τ(t) 无条件写成 T^ε。
合数非单位频率在此仍保留，q=2 的整个 centered 核实际为零也
符合上界。这一共振不是未经核对就等于原 reflection 共振。

## HY6. 全部 d/e/q/B 成本与真正的新覆盖

HY15 求 d|e 只付 τ(e)，固定 e,q,D 的两项没有遗漏 d 幂。
再用 Σ_(e≈E)e^(-1)≪1、#e≪E、#q≪Q、
Σ_(q≈Q)q≪Q²，即得非零部分
D{QHL/R+EQ²}。dyadic D≤B_* 的和是 O(B_*)，不是 O(B_*²)。
共振 HY17 用
Σ_(bc≤B_*)1/(bc)≪log²(2B_*)、Σe^-2≪E^-1、#q≪Q，
得到 HLQ/E。保留原唯一外权2T/(RS)，最终为
\[
 \boxed{|II_{\le}|\ll_\epsilon A_{12}T^\epsilon
 \left\{{THLQ\over RSE}
       +{TB_*EQ^2\over RS}
       +{TB_*QHL\over R^2S}\right\}.}
\tag{HY18}
\]
所有 e,q 均可只按整数计数，不需素数密度。论证对任意 b,c
子集且模长≤1的原标量系数都成立：不要求新 Möbius 特异输入。
若 U_cV_c≤B_*，同界也支付 I 的整个矩形，故原式精确留下
II_>；不是先给两个独立能量界再乘它们的 saving。

在 R=S≈T³、H=L≈T^(5/2)、E≈T^η、Q≈T^(3−η)、
B_*≈T^β 时，HY18 的三个指数分别为
\[
 3-2\eta,\qquad 1-\eta+\beta,\qquad \beta-\eta.
\tag{HY19}
\]
取 η=6/5、β=11/10，分别为3/5、9/10、−1/10。
TTC16 逐 bc 的两个指数为9/10和17/10，因此相对那一预算
改善4/5。允许全部平方自由 q，不要求 #526 的小 cofactor。
取 β=η 时，在1≤η≤5/2的平衡非空范围内三项均≤T；
这是 bc≲E 的控制，不是所有 bc 的控制。
A₁₂ 若随 T 增长，必须照付，不能隐去成为无条件的纯 T 指数。

与 #524/#526 的预算只作对比而非相乘；它们的较小短乘积范围
可有更强的单项数值界，本篇不撤回那些局部结论。本证明没有
引用一个新的通用大筛、四阶矩或 Möbius 相关定理。

## HY7. 非空原整数域与剩余账本

给一族不受旧小 cofactor 限制的真实支撑。Y₀→∞，用 Bertrand
在相应倍长区间选择互异素数 e≈Y₀²⁴，
p₁,p₂≈Y₀¹⁸（相邻倍长区间）、b≈Y₀¹⁰、c≈Y₀¹¹。
置 q=p₁p₂、R=S=eq、N=8S、T=N^(1/3)、H=L=S/√T、
K_z=M_z=√T。于是 E≈T^(6/5)、Q≈T^(9/5)，
B=bc≈Y₀²¹<B_*≈Y₀²²，但超过 #524 的 T^(7/10)。
两素因子都≈T^(9/10)，不在 #526 示例 cofactor≤T^(1/10) 内。

选素数 m∈(S/B,2S/B)，m≈Y₀³⁹ 大于之前各素数，令 n=Bm。
在 ceil(H/e),ceil(H/e)+1,ceil(H/e)+2 中选一个与 q 互素的 u，
这是可能的：两素数都>3，各至多排除一个候选。取 v=u。
则 (n,eq)=(uv,q)=1，(s,h,δ)=e，n∈(S,2S)，n,s≤N/4。
又 H≤eu≤2H、L≤ev≤2L，b,c>floor(T^(1/10))。
原 x₀=3√T/4 给 y=(x₀n+ev)/S 在原 AFE 支撑内（大 Y₀）。
全部条件只受固定倍长/dyadic 常数影响。这证明无限整数域非空，
不是宣称任意指定平滑权的积分非零，也不是一个下界。

脚本另检一个小合数见证 e=101、q=77、b=3、c=17、m=163，
N=8eq，保留原单位和连续 AFE 支撑。初选 B=65 的测试见证
不满足该小 T 的 B≤T^(11/10)，已改用 B=51；没有放宽定理域。

仍开放：bc>E 的全部长 signed Type-II、其他 canonical
allocations、q₀外和、非内部尺度及全局尾、原 principal、
canonical zero Gram 与其补集的共同能量交叉项。
本篇不使用 #490 的 PT 主项结论，也不认证 amplified b 系数
的转移；这里 μ(n) 分解后的无符号商不能免费授予另一条线。
有限脚本验证精确算术、反例、计数和指数，不证明解析 Fourier
尾或完整 coupled-kernel gate；解析证明是 HY8–18 的论证。

English: a joint four-factor representation count controls the nonzero
integer determinant after complete three-variable Fourier expansion.
Together with all integer resonances it bounds the original short-product
Type-II sector for every squarefree reduced modulus, with A12 and all
divisor/outer/tail costs retained. Long products and the full moment remain open.
