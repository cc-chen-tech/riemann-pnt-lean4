# 固定光滑 H/L：素数 e 与全部平方自由 q 的完整 centered 包

白话结论：直接在原 q 的完整双频谱中消去零轴，再拆 raw 与减项，
三掩码共同列就不再要求 q 带一个很大的素因子。本稿支付 e 为素数、
q 为任意平方自由数的同一完整 fixed smooth H/L 包；不是只支付某个
角色或频带。η=6/5 的新增模数域由旧 T^(11/10) 预算降到 T。
仍保留实际 A30 核费用；完整 twisted moment 和 coupled gate 未证明。

父版本为 #560 **05b18cf98b55787fdfd39c4a9420be9d90fbcefd**。
上游 [TM0–8](2026-08-31-physical-three-mask-cofactor.md) 已付
q=cp、c≤T^(3/7) 的整包；本稿去掉这一模数限制，仍要求 e prime。

## AQ0 唯一原式、权重与范围

令 p_N(x)=1−log(x)/log(N)，原线性和是
\[
 {2T\over RS}\sum_{\substack{e\ {\rm prime},\ q\ {\rm SF}\\
 E\le e<2E,\ Q\le q<2Q,\ (e,q)=1}}
 \mu(e)\mu(q)\sum_{\substack{n\ge1\\(n,eq)=1}}
 \mu(n)p_N(n)p_N(eq)
 \sum_{u,v\ne0}\Psi_{\rm sm}(n/R,eq/S,ev/L,eu/H)1_{(uv,q)=1}
 \left\{e_q(-euv\bar n)-{\mu(q)\over\varphi(q)}\right\}.       \tag{AQ0}
\]
固定 q0=a0=b0=1；r=n,s=eq,h=eu,δ=ev。内部尺度为
R≈S≈EQ≈T³，H≈L≈T^(5/2)，E≈T^η，7/6≤η≤5/4；
U=H/E，V=L/E，D1=Q/U，D2=Q/V≈√T，ν=RD1D2/(EQ)≈T。
原 e/q 半开壳保留；整包 n,eq≤N/2，不插新的联合 N 边缘。
Ψ_sm 是 FP1 重插原 F 的光滑 H/L 分解，不赋给旧 literal 硬包。
沿 [RH1–6](2026-08-31-physical-prime-pair-reciprocal-hybrid.md)、
[LP1–4](2026-08-31-physical-prime-pair-principal-loglabels.md) 的同一核，
A30 是原归一化坐标中核连同两 taper 的总阶≤30半范数。
不自动把 A30 当 T^ε，也不改变唯一外因子 2T/(RS)。

## AQ1 完整零轴先消去，不能先拆减项

在 (ne,q)=1 时定义正号双 DFT

 S_q(ρ,σ)=Σ_(u,v unit q) e_q(−e inverse(n)uv+ρu+σv),
 H_q(ρ,σ)=S_q(ρ,σ)−μ(q)c_q(ρ)c_q(σ)/φ(q).

直接先求 u 或 v 的有限和给

 S_q(0,σ)=μ(q)c_q(σ)，S_q(ρ,0)=μ(q)c_q(ρ)，
 H_q(0,σ)=H_q(ρ,0)=0.                                  (AQ1)

q=1 原 centered 核恒零。q>1 时，在完整 H_q 中先删整数 ρ=0 或 σ=0，
然后才拆 raw 与 Ramanujan correction；两项的零轴分别不为零。
非零 q 倍数频率可以全部保留，不另删非单位双频。
这是有限 DFT 恒等式，不是此前未成立的全局零频主项 vanishing。

对任意 D>0，有绝对可和的非零整数估计

 Σ_(r≠0)|c_q(r)|(1+|r|/D)^−6 ≪ D τ(q).                 (AQ2)

因为 |c_q(r)|≤Σ_(d|(q,r))d，且 Σ_(j≠0)(1+|dj|/D)^−6≪D/d；
D/d<1 时仍成立，没有 +1，关键正是 j=0 已在完整谱中消去。
乘 Poisson 的 UV/q²、correction 的 1/φ(q)、全部原 e/q/n 行数，
再乘 2T/(RS)，得到

 |correction_(ρσ≠0)|≪A30 T^ε T UV D1D2/Q³
                    =A30 T^(1+ε)/Q.                 (AQ3)

不能把这条界交给原零轴、LCM global principal 或其他包。

## AQ2 raw 的互反与三个 e-mask 误差

Z_q=(S_q/q)e_q(−nρσ inverse(e))，精确互反给

 S_q/q=Z_q e_e(−nρσ inverse(q)) e(nρσ/(eq)).           (AQ4)

因此 raw 的归一化是 UV/q 乘 Z_q。由下一节逐素数式可用
|S_q/q|≤τ(q)。全部 n-q 单位条件始终保留，不产生 n=qj 扩和。
先取 e|ρσ 的原 raw 尾，原 n-unit 不动；六次对偶衰减给
A30 T^(13/2−7η+ε)。其余 e-unit 标签上展开 e 的全部角色。

e 非主角色以零延拓保留 n/标签的 e-unit。e 主角色部分单独扩和：
先加 n=e m、仍保留标签 e-unit；再加 e|ρσ、n unrestricted。
两差项互斥，分别为 A30 T^(4−3η+ε) 与 A30 T^(13/2−8η+ε)。
前者保留 μ(em)，不错误因子化。三个费用可直接由 raw 平凡预算
T UV D1D2/Q=TQ，及非零 e 倍数标签的 D_i^5/e^6 比例重算。
这里完全不需要 q=cp、p>e 或 p>U；也没有 CQ 的第二 CRT 分支。

## AQ3 任意 SF q 的三掩码精确分解

这是 TM1 取 c=q,p=1 的有限等式。每个素数 l 记
N=1_(l|n)，R_l=1_(l|ρ)，S_l=1_(l|σ)，
w_l=1−1/[l(l−1)]，α_l=(l−2)/(l−1)，β_l=1/(l−1)，
A_l=w_l−α_l(R_l+S_l)−β_l R_l S_l。则

 Z_q=Σ_(λa=q) Σ_(χ primitive modλ)
 τλ(barχ)/[λφλ] χ(−nρσ)barχ(ea) ∏_(l|a)A_l.          (AQ5)

λ=1 的唯一角色保留；mod2 没有 primitive 角色。
CRT 互补 a 不可漏，非单位标签落在 A_l 而非被丢弃。
乘 n-q 单位指示，λ-unit 交给 χ；其余逐素数准确为

 (1−N)A=w−wN−αR−αS+αNR+αNS−βRS+βNRS.               (AQ6)

七种非空分配给 n/ρ/σ，令 f,j,k SF，g=lcm(f,j,k)，a=gz，
(g,z)=1，n=fm，ρ=jr，σ=ks，κ=fjk/g 为整数。原系数变成

 μ(e)μ(λ)μ(g)μ(z)μ(fm) v_g(f,j,k) w(z)，q=λgz。

不添 μ(f)，不添 (m,f)/(m,z)。所有 f,j,k|g，|v_g|≤1，0<w(z)≤1。
(λ,g)=1 为模数行限制，(z,g)=1 在共同 z 列，(z,λ)=1 由 χ(z) 零延拓。
原 (e,q)=1 必须继续分账，不能再以“大素数”自动互素代替。

## AQ4 原子共同性、原 q 硬壳及导子重复

固定 g,f,j,k、λ≈B、z≈Q/(Bg) 和双频 ρ≈J1,σ≈J2。
六个共同光滑坐标为

 m/(R/f)，e/E，λ/B，z/(Q/(Bg))，r/(J1/j)，s/(J2/k)。

原 chirp 为 e(κmrs/(eλz))，参数 X=RJ1J2/(EQ)=νθ，
θ=J1J2/(D1D2)，没有新的 κ 导数费。原 q 壳用整数端点的半整数
间隙作 log(q/Q) 精确插值；系数≪min(1,1/|h|,Q/h²)，ℓ1≪log Q。
每项只给 λ/z 列乘对数相位，不进入两 Weyl 标签权；没有截断误差，
不把插值导数收费到 A30。e 壳独立，不再有 c 截断或 p 标签。
六维 H⁴ 分离满足 4>6/2+2/3；12+12+4≤30 支付加权原子与双尾。
所有非空整数标签块的变换后长度≥1/2。

e 非主角色 ψ 与 λ primitive χ 融合时，(e,λ)=1，

 τe(barψ)τλ(barχ)barψ(λ)barχ(e)=τ_(eλ)(overline(ψχ)). (AQ7)

真实系数为 τ_(eλ)/[λφ(eλ)]，角色为
(ψχ)(−κmrs)(barψ barχ)(z)。原 (e,g)=1 留在模数行；
(e,z)=1 由 ψ(z) 零延拓实现，所以 κ 仍与 eλ 互素。
现在 e 不必大于 λ，(e,λ)→eλ 不再单射。对固定导子 v=eλ，
标签 e 至多 τ(v) 个；同一个 Fourier 原子的两列完全相同，先合并
行标量或在正大筛中支付重复次数。v≲EQ≈T³，因此只费 T^ε，
不能错误宣称唯一大素数，也不额外乘 E。

## AQ5 非主部分：全部 λ 都可支付

N1=R/f，另一 product 列长
K=QJ1J2/(Bgjk)=QD1D2 θ/(Bgjk)；非自然双频不得漏 θ。
一次 [CIS 普通 hybrid large sieve (1.6)](https://arxiv.org/pdf/1105.1176)
给未乘原外权的界

 A30 T^ε UV/[QB√(EB(1+X))]
 √{N1K[N1+(EB)²(1+X)][K+(EB)²(1+X)]}.                (AQ8)

仅用普通大筛，不用 CIS 的特殊系数渐近式。自然双频尺度物理四项为

 T^(7/2−5η/2) B^(−5/2)/(fgjk)，
 T^(2−η) B^−1/(f√(gjk))，
 T^(5/2−3η/2) B^(−3/2)/(gjk√f)，T/√(fgjk)。          (AQ9)

没有正的 B 次幂，故无需此前 λ≤c≤T^(3/7) 的限制。

## AQ6 主部分：新的 e-q 条件在乘积列内部

支付 AQ2 的两个主部分差项后，e 并入共同 ez 列，长度 N2=S/(Bg)。
其内部卷积使用归一化 Eμ(e)/φ(e)，单独提出 1/E；μ(z)w(z)、z SF、
(z,g)=1、(e,g)=1、**(e,z)=1** 均留在这个卷积中。
这些只依赖乘积的因子与固定 g，不依赖 λ；χλ(ez) 同时实施
(e,λ)=(z,λ)=1。没有把任意模数相关系数塞进共同列。
该有界除数卷积的 ℓ2 只费 T^ε，不能重复提取一次 1/φ(e)。

Gauss 绝对系数准确是 1/[φ(e)√λ φλ]，上界≪T^ε/(EB√B)。
两个平滑标签用 [Petrow–Young Corollary 1.3](https://arxiv.org/pdf/1811.02452v3)
的 cube-free primitive Weyl 界；λ=1 保留 ζ 极点和平移近零段，
按 TM5/GW7–8 的普通时间均值处理，不删除 principal。
保留标签权 (1+|ωr|)^(1/3+ε)(1+|ωs|)^(1/3+ε)，
先取模后才作等模共轭分组，不能共轭原线性系数。
Mellin 驻相 X^−1/2 之后，对 (N1,N2) 的共同两列一次 CS 与大筛给

 A30 T^ε UV/(QE) X^(1/3)B^(−7/6)/√(jk)
 √{(R/f)(S/(Bg))[R/f+B²X][S/(Bg)+B²X]}.               (AQ10)

自然尺度物理四项为

 T^(10/3−2η)B^(−13/6)/(fg√(jk))，
 T^(7/3−2η)B^(−2/3)/(f√(gjk))，
 T^(7/3−2η)B^(−7/6)/(g√(fjk))，
 T^(4/3−2η)B^(1/3)/√(fgjk)。                         (AQ11)

现在 B≤2Q/g；末项至多 T^(7/3−7η/3)/√(fgjk)，仍可付。
第一项 B=1 要求 η≥7/6；没有把它转给 global LCM principal。

## AQ7 所有外层、短双频与无限尾

七种分母均不少于 √(fgjk)，每 g 加权分配和≤7^ω(g)/g；
Σ_(g≤2Q)7^ω(g)/g≪Q^ε。其余 λ/z dyadic 只加对数。
即使 λ 接近 Q，也不多乘一个 q/e 行数。
非自然块仍用 X=νθ、真实 K；AQ8 自然比较多项式可取 √θ+θ，
AQ10 可取 θ^(1/3)max(1,θ) 并保留除数亚幂。
X≤1 是统一短段，非空 J1J2≈X≥常数；X≥1 主 Mellin 段保留
X^−1/2，外时间环六阶衰减支付大筛至多一次幂增长。
两 dual 尾各 (1+ratio)^(-8+ε) 支付上述比较与整数乘积除数费用。
λ=1 的极点近零和平滑标签频移按 TM5 全留；原子 H⁴ 付加权 ℓ1。
先对有限截断作恒等式，再以此正可和 majorant 放开所有求和/积分。
只付一次 A30，不用自然双频的数值检查替代无限可和性证明。

## AQ8 完整结果与真正新增的模数族

由 AQ1–7，原 AQ0 的整个线性 centered 包满足
\[
 |\mathcal C_{e\ {\rm prime},\ q\ {\rm SF}}|
 \ll_\epsilon A_{30}T^{1+\epsilon},\qquad 7/6\le\eta\le5/4.  \tag{AQ12}
\]
同包旧 DP14（模数限制只在正大筛后扩和）在 η=6/5 给 11/10；
本次改善 1/10 是上界预算比较，不是原和的下界，也不叠乘 #560。
新增域包括 q=p1p2、p1≈p2≈T^(9/10)，两种 prime complement
均大于 T^(3/7)，故 #560 不覆盖。没有只重证已付的 log-cofactor。

无限真实非空族可由 Bertrand 取 e≈Y⁶、互异 p1,p2≈Y^(9/2)，
q=p1p2，R=S=eq≈Y15，T=(8S)^(1/3)≈Y⁵，N=8S，
Kz=Mz=√T，H=L=S/√T。在 q/√T 附近选 u=v 避开 p1,p2；
候选区间长≈q/√T≫p1+p2，初等计数即保证存在。
n prime∈(S,2S) 给所有原单位、n,s≤N/4；x=3√T/4 使原 y 支持非空。
有限例 e=1009,p1=167,p2=173 在附脚本中精确核对整数单位与壳，
浮点只用于展示原实支持，素性为有限试除并显式限定 n<2^64。
不声称任意核积分非零或 positive density。

合数 e、全 canonical/q0、其他尺度、full h/δ、跨 AFE/HL 尾、
actual amplified 及共同能量 EE*、EC*、CE*、CC* 仍不在本定理范围。
有限交付包括全 q 双 DFT/非分离权逆变换、非单位频率、三掩码原 μ、
导子重复、Gauss 融合、ez 内部互素及全部有理指数；这些不认证解析
大筛、Lean 或 main，也不把局部 PR 当作完整 twisted-moment 证明。
