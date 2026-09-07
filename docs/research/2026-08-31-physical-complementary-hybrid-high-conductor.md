# 互补除数顶项：新高导子投影的混合大筛约化

白话结论：把完整 h 整数格的 Ramanujan 除数展开中 **仅 d=q 的一项**
改写为模 e/gcd(e,m) 的同余，保留薄带权带来的 T 频率，再对一条真正
光滑的长标签作角色 Poisson。例如 η=6/5、Λ₀=T^(1/5) 时，可支付这个
展开项的新高导子部分；一般参数的费用见 (CH.1)。
它不是原 centered 和的完整子族覆盖；低导子、新主角色、其他除数项和
原校正项全部仍在，不能据此降低 14/17 或 2/3 的未证门槛。

English summary: a complementary-modulus projection and one hybrid character
Poisson transform bound the new high-conductor component of the d=q divisor
term. This is not a bound for the whole original centered packet. All low
conductors, the new principal projection, other divisor terms and the original
correction remain explicit. The argument uses ordinary hybrid large sieve,
not a new signed Möbius correlation theorem or an asymptotic large sieve claim.

定义源固定 #519 的 `614624c83da5bfe41b20a5b1c6f4629d941da806`：
[`physical-full-h-ramanujan-lattice`](2026-08-31-physical-full-h-ramanujan-lattice.md)
H1–H3、H5。下文是数学证明及有限守卫，不是 Lean 定理或最终 main 验收。

## CH1. 精确对象与交付命题

固定 q₀=1 的内部完整 h 点核包。保留原平方自由 e,q、
(e,q)=(n,eq)=(v,q)=1、m>0、v≠0 及全部实际权 Ω。
取平衡域 R=S≈T³、M≈T^(1/2)、L≈T^(5/2)、E=T^η、Q=S/E、V=L/E，
1≤η≤5/2，所有比较常数固定。M 是正整数 m 的尺度，不是 canonical 分配。
使用 H3 真正的五变量点核半范数 B_J；其 core 条件和整包内部支持不变。
唯一物理外权是 2T/(RSM)。固定阶 B_J 的一致性来自 H3 的原核导数控制。

令 t₀=nm+ev>0。精确恒等式为
\[
 \mu(q)C_q=\sum_{d\mid q,\ d\mid t_0}\mu(d)d-\frac{c_q(m)}{\varphi(q)}.
\]
本稿只研究 d=q 项，系数 μ(e)μ(n)μ(q)q，关系 nm+ev=qk。
它是有符号展开项，**不是从原 centered 和删去一些整数元组得到的子集**。

CH2–CH4 定义其新模数 a=e/gcd(e,m) 的 primitive 投影。
记仅保留新导子 ℓ≥Λ₀≥2 的分量为 S_top,≥Λ₀（若域为空则为零）。证明
\[
 |S_{\mathrm{top},\ge\Lambda_0}|
 \ll_\varepsilon \mathcal B_{100}T^\varepsilon
 \left[T+T^{2-\eta}+T^{5/2-3\eta/2}
                  +\frac{T^{7/2-2\eta}}{\sqrt{\Lambda_0}}\right]. \tag{CH.1}
\]
在 η=6/5、Λ₀=T^(1/5) 时四指数是 1、4/5、7/10、1。
不加此新导子限制，末项仍是 11/10。此命题没有支付 CH10 的余项。

## CH2. 唯一 gcd 分配及两次完整容斥

先取 h=(e,m)、e=ha、m=hz₀。因 (q,h)=1，关系强制 h|k，写 k=hw。
于是 av=qw−nz₀，(h,a)=(z₀,a)=1；没有 (z₀,h)=1。
原 (v,q)=1 在该关系和 (n,q)=1 下恰好等价于 (z₀,q)=1。

完整展开 (n,q)=1，令 n=fx、q=fy₀；随后完整展开 (z₀,y₀)=1，
令 y₀=ly、z₀=lz。得到
\[
 e=ha,\ n=fx,\ q=fly,\ m=hlz,\ k=hw,\qquad
 av=fl(yw-xz),
\]
以及精确符号
\[
 \mu(h)\mu(a)\mu(f)\mu(x)\mu(y)\mu(l)^2. \tag{CH.2}
\]
所有独立互素条件为
\[
 (h,a)=(f,l)=(fl,ha)=1,\qquad
 (x,fha)=(y,flha)=(z,fa)=1. \tag{CH.3}
\]
同余 xz=yw mod a 自动强制 w 为 a-unit。不可新增 (x,l)、(z,h)、
(w,hfl) 或 (x,y)。容斥展开的单项无需各自满足被展开的原互素条件；
只有完整有符号和恢复它们。原 q 权是 fly≈Q，其归一化 y 因子留在权中。

设互补 k 尺度 Kc=RM/Q（不是 AFE 的 K）。因 L/(RM)≈1/T，原支持上
k≈Kc>0，可插入在该支持恒为 1 的固定光滑 w/(Kc/h) cutoff。
固定 h,f,l 后各列长度为
\[
 A=R/f,\quad B=Q/(fl),\quad Z=M/(hl),\quad X_w=Kc/h,
 \qquad AZ=BX_w=RM/(hfl). \tag{CH.4}
\]

## CH3. 实际薄带的 Mellin 分离

取 u=log(qk/(nm))=log(yw/(xz))，则
\[
 v/V=(nm/L)(E/e)(e^u-1).
\]
实际带符号的非零 v cutoff 因而给 |u|≲1/T。令 u=s/T 后，
剖面对 s 和归一化 e,n,q,m 的导数均受 B_J 控制，因为 RM/(TL)≈1。
在 s 上加冗余固定 cutoff，采用
\[
 W(u;p)=\frac1{2\pi T}\int_{\mathbb R}F(p,t/T)e^{itu}\,dt. \tag{CH.5}
\]
F 在 t/T 上快速衰减；p 表示四个归一化物理参数。
即使 |t|≈τ<T，也不能把 1/T 改为 1/τ 或删掉。
这里 t 是新的 Mellin 变量，不是已经包含在 Ω 中的原 AFE 积分变量。

原独立离散 dyadic 限制仍留在各单变量列或模数行。不能另外把联合硬角点
塞进宣称光滑的 W；我们只用 H3 的整包内部支持。冗余 w cutoff 在分离后
是固定 C_c^∞ 因子，不带原 Fourier 展开频率。
投影后的单项在非同余点用同一 Ω 光滑延拓，v=fl(yw−xz)/a 此时可非整数；
完整角色和才恢复原同余格。这不是将单个投影称为原整数子族。

## CH4. 新角色投影的完整定义

在 a 的单位群上用
\[
 1_{xz\equiv yw\ (a)}=\frac1{\varphi(a)}
       \sum_{\chi\bmod a}\chi(xz)\overline{\chi(yw)}.
\]
先单独保留 principal；它是新投影主项，不等于原 Ramanujan 校正，
也没有由上游 global principal 定理自动支付。
其余字符唯一写成 a=cℓ、χ primitive mod ℓ>1；平方自由性给 (c,ℓ)=1。
固定 h,c，令 ℓ≈Λ=E/(hc)，权为 1/(φ(c)φ(ℓ))。

具体而言，S_top,≥Λ₀ 是以下精确角色展开中 ℓ≥Λ₀ 的和：
\[
 \frac{2T}{RSM}\sum_{h,c,\ell,f,l}
 \frac{\mu(h)\mu(c)\mu(\ell)\mu(f)\mu(l)^2}
      {\varphi(c)\varphi(\ell)}
 \sum_{\chi\bmod\ell}^{*}\sum_{x,y,z,w}
 \mu(x)\mu(y)fly\,
 \Omega\!\left(\frac{hc\ell}{E},\frac{fx}{R},\frac{hlz}{M},
        \frac{fl(yw-xz)}{c\ell V},\frac{fly}{Q}\right)
 \chi(xz)\overline{\chi(yw)}. \tag{CH.6}
\]
各整数范围来自 CH1–CH3；保留 (h,cℓ)=(fl,hcℓ)=(f,l)=(c,ℓ)=1。
单列 mask 为 (x,fhc)=(y,flhc)=(z,fc)=(w,c)=1；
ℓ-unit 条件由 primitive χ 的零延拓保留。
所有平方自由符号、真实 dyadic 支持和 q=fly 权均在式中。

仅对 w 的 c-mask 再作容斥 j|c，令 w=jb。保留 μ(j)、barχ(j)j^(it)
及所有原外层标量；(j,ℓ)=1。其他 c、h、f、l 的条件留在共同列。

## CH5. 仅对长光滑 w 列作混合 Poisson

对 |t|≈τ≥1 和 X=Xw/j，primitive Poisson 精确给
\[
 \sum_b\bar\chi(b)b^{it}w_0(b/X)
 =\frac{\tau(\bar\chi)}\ell\sum_r\chi(r)
       \int_0^\infty x^{it}w_0(x/X)e(-rx/\ell)\,dx. \tag{CH.7}
\]
ℓ>1 时 r=0 系数严格为零；ℓ=1 的新 principal 没有被删掉。
驻点位于 x*=ℓt/(2πr)，故 r 与 t 同号，自然对偶长度和振幅是
\[
 D=\Lambda\tau/X=\Lambda\tau h j/Kc,\qquad X/\sqrt{\Lambda\tau}.
\]
抽出 exp(it log(x*)−it) 后，留下 χ(r)|r|^(−it)，其余为模长一行因子
和受控光滑符号；负 r 的 χ(−1) 保留。因此 x,z,r 都有 χ(.)·(.)^(−it)
方向。在 |t|≤1 用 τ=1 的普通 Poisson，避免 log(t) 奇点。

所有 r 环使用真实整数 dyadic 区间，长度至少 1/2。只有中央区间的上端
小于 1 时才能说它为空，不能把带隐含支持常数的阈值写成一概 D<1。

## CH6. 共同系数与混合大筛

取模后共轭完整复系数 y 列，将 y,z,r 组成一条 χ(.)·(.)^(−it) 产品列，
x 单独作另一列。这是模长恒等式，不是原复线性和相等。
产品表示数由 τ₃ 控制；全部 mask 仍是其单变量因子。
在固定 h,f,l,c,j 及分离 atom 后，两列对 ℓ、χ、t 的系数共同，
长度为 A=R/f 和
\[
 N_2=BZD=\frac{Q^2\Lambda\tau j}{f l^2R},\qquad
 \|a\|_2^2\ll T^\varepsilon A,\quad
 \|b\|_2^2\ll T^\varepsilon N_2. \tag{CH.8}
\]
实际短于支持阈值的 B,Z 列为空；短 D 的处理是 CH8 的真实对偶环，
不是虚构 O(D) 个整数。

使用 [Conrey–Iwaniec–Soundararajan (1.6)](https://arxiv.org/pdf/1105.1176)：
\[
 \sum_{\ell\le2\Lambda}\sum_\chi^*\int_{-C\tau}^{C\tau}
   \left|\sum_{n\le N}a_n\chi(n)n^{it}\right|^2dt
 \ll(\Lambda^2\tau+N)\sum_n|a_n|^2.
\]
这是普通 primitive hybrid large sieve；没有调用该文的 asymptotic
large sieve 或特殊 L-function 系数引理。额外 ℓ/φ(ℓ) 只花 T^ε。
允许模数的非负扩和只发生在 Cauchy 后，不事先更改原线性表达式。

## CH7. 归一化和四项费用

两列能量平方根之前的行系数为
\[
 \frac{QKc}{h j\varphi(c)\Lambda^{3/2}T\sqrt\tau}.
\]
乘上 √(A N₂)，一次 Cauchy 与混合大筛给
\[
 \frac{Q^2Kc}{h f l\varphi(c)\Lambda T\sqrt j}
 \sqrt{(R/f+\Lambda^2\tau)
       (Q^2\Lambda\tau j/(fl^2R)+\Lambda^2\tau)}.
\]
展开平方根得到
\[
 \frac{Q^2Kc\Lambda\tau}{hfl\varphi(c)T\sqrt j},\quad
 \frac{Q^2Kc\sqrt{R\tau}}{hf^{3/2}l\varphi(c)T\sqrt j},\quad
 \frac{Q^3Kc\sqrt\Lambda\tau}{hf^{3/2}l^2\varphi(c)T\sqrt R},\quad
 \frac{Q^3Kc\sqrt\tau}{hf^2l^2\varphi(c)T\sqrt\Lambda}. \tag{CH.9}
\]
以下记为 C₁,…,C₄，均尚未乘唯一物理外权。

## CH8. 统一符号、有限导数预算和两类无限尾

本节证明 CH5–CH7 需要的统一性，而非只取驻相首项。分两次做绝对可和
Fourier 分离：CH3 剖面的四个归一化物理参数加 t/τ，以及 Poisson 符号的
ℓ/Λ、t/τ、r/Rdual。各自至多六维，八阶导数足够 l¹ 预算；w₀ 保持固定。

**剖面。** 在紧支撑 s 上分部积分 20 次，加至多八阶参数导数，得到
B₂₈(1+|t|/T)^(−20)。缩放 t/τ 导数最多花 (1+τ/T)^8，
故分离预算 ≤C B₂₈(1+τ/T)^(−12)。B₁₀₀ 是安全统一选择，不能替换为 B₆。

**中央符号。** 对同号 r,t，x=x*z 后相位是 t(log z−z+1)。在 z=1
附近用固定 Morse 坐标把相位化为 −ts²/2。精确归一化积分是
√τ∫A(s;t/τ,rX/(ℓτ))exp(−its²/2)ds。其参数振幅导数按链式法则保留；
频率导数不会白付 τ，因为固定 A 时
\[
 t\partial_t\left[\sqrt t\int A(s)e^{-its^2/2}ds\right]
 =-\frac{\sqrt t}{2}\int sA'(s)e^{-its^2/2}ds.
\]
重复此恒等式与普通 Gaussian 振荡界，至多 20 阶固定 w₀ 导数足以
控制八阶缩放参数导数。t<0 作共轭相位计算。远离驻点部分留给下一步，
此为精确光滑分割，没有遗漏渐近余项。

**非驻相环。** 置 s₀=Rdual/D。小 s₀ 时相位导数 ≳τ；大 s₀ 时 ≳τs₀。
20 次分部积分后再取至多八阶参数导数，固定 w₀ 的 C⁴⁰ 已足够，
得到符号 l¹ 上界
\[
 C(1+|\log s_0|)^8\quad(s_0\le1),\qquad
 Cs_0^{-10}(1+\log s_0)^8\quad(s_0\ge1). \tag{CH.10}
\]
低环的 log⁸ 来自对 |r|^(−it) 求导，不能误写成低环上一致常数。
|t|≤1 时先普通 Poisson，再人工插入 |r|^(−it) 和补偿因子，
同样得到 (CH.10)，不出现 log(t)。

**求和。** Rdual=s₀D 环把产品列长度和能量乘 s₀，所以 C₁,C₂ 乘 √s₀，
C₃,C₄ 乘 s₀。小环端的几何级数能支付 log⁸，大环的 s₀^(−10) 支付
最大 s₀ 成本；D 很小时只存在大 s₀ 环，同一上界仍有效。
τ>T 的剖面衰减 12 阶支付 C₁,C₃ 的 τ/T 及 C₂,C₄ 的 √(τ/T) 增长；
τ≤T 的和被 τ=T 主导。无穷环/τ 上除数范数额外的小 ε 幂也被这些余量
吸收，原各有限参数均在 T 的固定幂范围内。预算线性依赖 B₁₀₀，
不是 B₁₀₀²：剖面携带该范数，Poisson 符号只使用固定 w₀ 的范数。

所用非驻相、Morse/Gaussian 与参数导数原则见
[Tao, 247B Notes 8, Lemmas 2.6–2.8](https://www.math.ucla.edu/~tao/247b.1.07w/notes8.pdf)。
上面的恒等式和环费用给出了本处具体统一性；有限脚本不替代这段证明。

## CH9. 全部外层求和与局部结论

在 τ=T 代入 Λ≈E/(hc)。f,l 和均收敛或仅有调和损失，
∑_{j|c}j^(−1/2) 或 τ(c) 花 T^ε。对 h 的真实正整数范围求和时，
C₁,C₂,C₃ 分别用 h^(−2)、h^(−1)、h^(−3/2)，
c 和分别用 1/(cφ(c))、1/φ(c)、1/(√cφ(c))，得到
\[
 RMS,\qquad QRM\sqrt{R/T},\qquad Q^2M\sqrt{RE}.
\]
新导子 ℓ≥Λ₀ 给 c≤2E/(hΛ₀)。C₄ 用
\[
 \sum_{c\le C}\frac{\sqrt c}{\varphi(c)}\ll_\varepsilon C^{1/2+\varepsilon},
\]
其 h^(−1/2) 因子因而变为调和 h^(−1)，得到 Q²RM/√(TΛ₀)。
乘一次 2T/(RSM) 就得到 (CH.1)。没有漏掉 a/e 的行数：a=cℓ 的 ℓ 和
恰是 primitive 混合大筛的模数和，h、c 仍按上式完整求和。

不能利用原支持 v≠0 或 nm+ev>0 来删除大筛中的正范数长度项；
原整数对角被排除，不代表 Cauchy 后的范数费用消失。

## CH10. 明确保留的余项及有限核验

本稿没有支付：新 a-principal、1<ℓ<Λ₀、全部 d<q 的原除数展开项、
原 −c_q(m)/φ(q) 校正，以及其他原 gcd/q₀/尺度分配和 global tails。
不把新 principal 交给未作精确映射的旧 principal 定理；不声称新 Möbius
有符号相关界、完整 FP3 新覆盖或全局零点排除。

配套 `scripts/check_physical_complementary_hybrid_high_conductor.py`
核对完整双 IE、实际整数映射、原单位条件等价、平方后的有理费用和指数。
五个错误变体分别检测：μ(l) 代替 μ(l)²、漏 μ(f)、多加 (x,l)、多加(z,h)、
漏 (z,f)。这些是有限恒等式证据，不是解析证明、Lean 或 CI 证书。
原 #519 的证明和源分支保持不变。本稿也不供应旧 Hecke-entry hybrid
接口的未证全局消去，不将不同原子/不同范数节省相乘。
