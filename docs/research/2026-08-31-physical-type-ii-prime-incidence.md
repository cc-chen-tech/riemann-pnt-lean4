# 素数模数上的共同频率：支付双长因子的短乘积部分

白话结论：两个 Möbius 因子都超过 Type-I 截断，并不意味着必须
逐项估计它们的相关。三变量完成后，素数模数的谱恰好是一个
乘积同余减一个常数。先对常数整体反变换，再计算真正的整数
共振，可以控制原 Type-II 中一个此前未付的乘积范围。
例如 E≈T^(6/5)、bc≤T^(7/10) 时得到 O(A₁₄₄T^(3/5+ε))，
而沿上游逐 bc 的费用是 T^(13/10+ε)。这不是 Möbius 特异的
消去；全部长乘积、合数约化模数和原 principal 仍然开放。

## PII0. 固定来源与真实线性子族

直接上游是 [TTC0–TTC18](2026-08-31-physical-type-i-triple-completion.md)，
固定提交 779c0cffb51a0e834d39ea86f5571a5d21b1f008；其原式仍是
MWKF-PHYS-v1 的49cfacd7及 CP 的9448c71d新 smooth 包。
不沿用一般硬 h/δ 包的旧声明，也不改动这些冻结版本。

本篇只选择 q₀=a₀=b₀=1 的真实 FP3 子族：
\[
 r=n,\quad s=eq,\quad h=eu,\quad\delta=ev,
 \quad e\in[E,2E)\text{ squarefree},\quad
 q\in[Q,2Q)\text{ prime},\quad(e,q)=1.
\tag{PII1}
\]
保持 (n,eq)=(uv,q)=1、uv≠0、原系数 μ(e)μ(q)μ(n)，
以及唯一外权 2T/(RS)。q 是约化模数；只取其素数列是一项
线性投影，不把它称为全部原 s 或全部 q 家族。
假设 R≈S≈EQ，比较常数固定，Q≥2；原整包支撑 n,s≤N/2。
Ψ 含原 F_R(n)F_S(s) 及重新插入的 smooth h/δ 分片，
没有额外非冗余硬壳。HL≲RS/T，所有参数及非零倒数均在
固定 T 幂内。A_j 支付该原核的全部归一化 j 阶导数。

取 max(U_c,V_c)<R/2 的正整数截断，逐 n 仍是 TTC2：
\[
 C=I+II,\qquad
 \mu(n)=-\sum_{bc\mid n\atop b\le U_c,c\le V_c}\mu(b)\mu(c)
        +\sum_{bc\mid n\atop b>U_c,c>V_c}\mu(b)\mu(c).
\tag{PII2}
\]
令 II_≤ 为第二项再限制 B=bc≤B_*，II_> 为其精确补集。
没有 (b,c)=1 条件，没有商变量平方自由限制；n 的原平方自由
限制必须在展开 μ(n) 前以 μ(n)=0 扩展掉。
若截断不满足上述端点条件，原有限 μ(n) 边界须保留，不在本篇内。

## PII1. 全单位容斥后的实际权

固定 e,q,b,c 且 (B,eq)=1，写 n=Bm，展开
1_(m,e)=1=Σ_(d|e,d|m)μ(d)，置 m=dz、a=e/d。于是
\[
 \alpha=a\bar B\pmod q,\qquad (aB,q)=(a,B)=1,
 \quad Z={R\over Bd},\ X={H\over e},\ Y={L\over e}.
\tag{PII3}
\]
剩余内掩码恰为 (zuv,q)=1。每行完整符号是
μ(e)μ(q)μ(b)μ(c)μ(d)，没有 μ(z)、(z,d) 或 (z,a) 掩码。
真实非分离权为
\[
 W(z,u,v)=p_N(Bdz)p_N(eq)
       \Psi(Bdz/R,eq/S,ev/L,eu/H).
\tag{PII4}
\]
归一化坐标是 (z/Z,eq/S,v/Y,u/X)，故无 B,d 的导数损失。
z>0，z≤2Z；标签非零且 |u|≤2X、|v|≤2Y，权在零点附近为零。
允许 Z,X,Y<1：空整数域直接为零，不把 Fourier 自然尺度补成1。

## PII2. 素数谱的完整差，不能逐频率取绝对值

以 TTC3 的正号有限 Fourier 约定，在素数 q 上精确有
\[
 \mathcal H_q(k,\rho,\sigma)
 =q^2\mathbf1_{(k\rho\sigma,q)=1}
   \left\{\mathbf1_{q\mid ak+B\rho\sigma}-{1\over q-1}\right\}.
\tag{PII5}
\]
证明是 TTC4 的两种 Ramanujan 取值；乘 B 不改变同余。
任一坐标非单位时三个坐标面恒等式使 H_q=0；这里特别依赖
q 为素数。q=6,k=ρ=σ=2 的非零谱反例禁止推广这一掩码。
q=2 时两个花括号项相等，整个原 centered 核为零，亦被包括。

对负号连续 Fourier 变换，完整 Poisson 因而写成
\[
 {1\over q}\sum_{(k\rho\sigma,q)=1\atop q\mid ak+B\rho\sigma}
       \widehat W(k/q,\rho/q,\sigma/q)
 -{1\over q(q-1)}\sum_{(k\rho\sigma,q)=1}
       \widehat W(k/q,\rho/q,\sigma/q).
\tag{PII6}
\]
三个频率均遍历全部整数；单位条件已排除每个整数零坐标。
每轴 J 阶、混合总阶3J的衰减使 J≥2 时所有和绝对收敛。
下面分别支付整数共振、常数项和非零同余尾；不删除任何一项。

## PII3. 常数项整体反变换的预算

普通 Poisson 在每个 k mod q 单位余类上给精确式
\[
 \sum_{(k\rho\sigma,q)=1}\widehat W(k/q,\rho/q,\sigma/q)
   =\sum_{z,u,v\in\mathbb Z}W(z,u,v)c_q(z)c_q(u)c_q(v).
\tag{PII7}
\]
没有新增 q³ 因子。该式不要求 W 分离。
对任意 L>0，直接用 floor 而非渐近计数有
\[
 \sum_{1\le n\le2L}|c_q(n)|\le4L,\qquad
 \sum_{0<|n|\le2L}|c_q(n)|\le8L.
\tag{PII8}
\]
因为 |c_q(n)|≤1+q1_(q|n)，正倍数个数≤floor(2L/q)≤2L/q。
故三变量的绝对 majorant 为 O(ZXY)，即使自然尺度小于1
也不需整数 +1。此处**离零支撑必要**；若允许 u=0 就不能这样计数。
于是 PII6 的整个常数项满足
\[
 |\mathrm{Const}_{B,d,e,q}|\ll\mathcal A_0\,{ZXY\over q^2}.
\tag{PII9}
\]
不从 HL≲RS/T 推出各自 H/S、L/S 的额外界，也不要求 X,Y<q。
这是新 Fourier 常数项，不是原 Ramanujan principal 或 zero Gram。

## PII4. 整个整数共振：所有除数与长 b,c 一起收费

定义整数 Δ=ak+Bρσ。在 Δ=0 部分，(a,B)=1 且三频率非零
强制唯一参数化
\[
 k=Bt,\qquad\rho\sigma=-at,\qquad t\ne0.
\tag{PII10}
\]
保留其 q 单位条件；估计时可以删此条件作上界。
每个 t 的有序带符号标签因子最多2τ(a|t|)个。
因为 R/(eq) 在固定紧区间，|k|Z/q≈a|t|，由原3J阶界
\[
 |\widehat W(k/q,\rho/q,\sigma/q)|
 \ll_J\mathcal A_{3J}ZXY
 (1+|k|Z/q)^{-J}(1+|\rho|X/q)^{-J}(1+|\sigma|Y/q)^{-J}
\tag{PII11}
\]
得到 J≥4 时每 B 的所有 d|e 共振之和至多
\[
 \ll_J\mathcal A_{3J}{XY\over B}
       \sum_{a\mid e}\tau(a)a^{1-J}
       \sum_{t\ge1}\tau(t)t^{-J}
 \ll_J\mathcal A_{3J}{XY\over B}.
\tag{PII12}
\]
最后两和由收敛的 ζ(J−1)²和 ζ(J)²支付，未把无限 t 的
τ(t) 写成统一 T^ε。所有 d，包括 d=e，都已恢复。
这不是把旧 GE 的另一坐标共振与本项认定为相同，不能重复扣除。

## PII5. 非零 q 倍数与所有无限尾

令 Λ≥2，假定实际参数满足
\[
 B_*\Lambda^2\left({4EQ\over R}+{16E^2Q^2\over HL}\right)
          \le {Q\over2}.
\tag{PII13}
\]
自然频率为 K=q/Z、L₁=q/X、L₂=q/Y。在矩形
|k|≤ΛK、|ρ|≤ΛL₁、|σ|≤ΛL₂ 内，
\[
 |\Delta|\le\Lambda aK+B\Lambda^2L_1L_2\le Q/2<q.
\]
所以 q|Δ 时只有整数 Δ=0；所有非零 q 倍数都在矩形外。
自然尺度<1时矩形的非零整数域可能为空，这也不改变论证。

对任意 L>0、Λ≥2、J>1，有统一引理
\[
 \sum_{n\ne0}(1+|n|/L)^{-J}\ll_J L,\qquad
 \sum_{|n|>\Lambda L\atop n\ne0}(1+|n|/L)^{-J}
       \ll_J L\Lambda^{1-J}.
\tag{PII14}
\]
LΛ≥1 用积分加首项；LΛ<1 用 L^Jζ(J)≤LΛ^(1−J)。
因此不能直接调用只对整数截断≥1写出的 TTC12，但 PII14
严格补齐了这个端点。用 PII11 和三个矩形外侧的并集，PII6
的非零 incidence 尾逐 B,d,e,q 至多
\[
 \mathcal A_{3J}{ZXY\over q}KL_1L_2\Lambda^{1-J}
       =\mathcal A_{3J}q^2\Lambda^{1-J}.
\tag{PII15}
\]
这里已求完所有频率，不把矩形外补集直接删掉；J 的代价明确
计入 A₃ⱼ。有限外和与以上绝对收敛和可合法换序。

## PII6. 全外层、覆盖增量与非空范围

以下只用模长界，保留 b,c 的原符号直到上述重组完成。
任意截断掩码下都有
\[
 \sum_{bc\le B_*}{1\over bc}\ll\log^2(2B_*),\qquad
 \#\{(b,c):bc\le B_*\}\ll B_*\log(2B_*).
\tag{PII16}
\]
共振用 PII12 及全部 e,q 数量，费用 HLQ/E；常数用
PII9、Σ_(d|e)1/d≪T^ε、Σe^-2≪E^-1、Σq^-2≪Q^-1，
费用 RHL/(EQ)≈HL。尾用 PII15、Σe τ(e)≪ET^ε、Σq q²≪Q³，
费用 EQ³B_*Λ^(1−J)。无需素数密度估计；都可放大成整数求和。
恢复唯一 2T/(RS)，得实际子族定理
\[
 \boxed{|II_{\le}|\ll_{J,\epsilon}\mathcal A_{3J}T^\epsilon
 \left\{{THLQ\over RSE}+{THL\over RS}
       +{TEQ^3B_*\over RS}\Lambda^{1-J}\right\}.}
\tag{PII17}
\]
同一证明适用于任意带原 (B,eq)=1 掩码的 b,c 子集。
特别地，若 U_cV_c≤B_*，I 的整个矩形也包含其中；可以把
I+II_≤一起支付，只需固定常数，而不是相乘两次 saving。
所以在该素数列子族上精确剩下 II_>，不丢任何 mixed 能量项。

在 R=S≈T³、HL≈T⁵、E=T^η、Q≈T^(3−η)、B_*=T^β、
Λ=T^ω 时，PII13 的渐近充分条件是
β+1+2ω<3−η。三个成本指数精确为
\[
 3-2\eta,\qquad0,\qquad4-2\eta+\beta-(J-1)\omega.
\tag{PII18}
\]
例如 η=6/5、β=7/10、ω=1/25、J=48：频率间隙为1/50，
三个指数为3/5、0、21/50。因此需要 A₁₄₄，而非免费 A₁₂。
取 U_c=V_c=floor(T^(1/10))，原 II_≤确含两因子都超过截断
且乘积大于 T^(1/5) 的新部分。沿 TTC16 逐 bc 付费，两个指数
是1/2与13/10；新最大3/5，相对该预算改善7/10。
这仅在显示的高阶原半范数受控时是 T 幂次估计。

无限真实非空族可用 Bertrand 构造：Y₀→∞，选互异素数
e≈Y₀¹²、q≈Y₀¹⁸、b≈Y₀³、c≈Y₀³（b,c用相邻倍长区间），
设 R=S=eq、N=8S、T=(8S)^(1/3)、H=L=S/√T、K_z=M_z=√T。
B=bc≈Y₀⁶，小于 B_*≈Y₀⁷而大于两短截断乘积≈Y₀²。
再选素数 m∈(S/B,2S/B)，其尺度≈Y₀²⁴，大于前四个素数，
置 n=Bm、u=v=ceil(H/e)。于是 n∈(S,2S)、(n,eq)=1，
u=v≈Y₀¹³<q，(uv,q)=1，(s,h,δ)=e，且 n,s≤N/4。
原连续 x₀=3√T/4 给 y=(x₀n+ev)/S 在原 AFE 支撑内。
PII13 左右之比为 O(T^(-1/50))，最终严格满足；有限 dyadic
取整只改变固定常数。这不宣称任意指定平滑权的积分非零。

本篇不使用新的通用谱定理。已发表的 Bettin–Chandee 型覆盖表
仍保留；[Wright Theorem 2.1](https://arxiv.org/html/2604.25177v1)
要求固定分母因子，[Pascadi Theorem 1.1](https://link.springer.com/article/10.1007/s00039-026-00746-0)
估计固定模数 Kloosterman 双线性和，不能仅凭本篇 Δ 的出现
直接套到全部 μ(b)μ(c)μ(e)μ(q) 物理和。此处的新费用来自
原核的精确素数谱及离零支撑，不是叠加这些论文的节省。

仍未付：II_> 的长乘积、合数约化 q、其他 canonical allocations、
外 q₀ 与尺度尾、原 principal 和完整共同能量的交叉项。
有限脚本只检验恒等式、计数、指数和支持，不认证解析导数界、
Poisson 无限尾或完整 coupled-kernel gate。

English: for prime reduced modulus, the complete three-coordinate spectrum
is an incidence constraint minus an explicit constant. Reassembling the
constant and all integer resonances bounds the original double-long-factor,
short-product Type-II sector with every divisor and Fourier tail paid.
The long-product signed complement and the full twisted moment remain open.
