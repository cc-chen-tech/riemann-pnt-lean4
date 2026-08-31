# 固定 H/L：低导子短容斥项与小余因子完整包

白话结论：新模 e 含小素因子时，非单位双频不能删除。本篇用已发表的
hybrid Weyl 界处理两个光滑角色标签，再把剩下两列共同送入大筛。
E≈T^(6/5) 时，低导子 ℓ<T^(1/5)、容斥除数 d≤T^(2/15) 的有符号
子和可支付 T 预算。这不是“gcd≤D 的投影”，也不是完整 principal。

另重证一个可合回完整原式的真实子族：e=h₀p，p 为素数，h₀ 平方自由、
h₀≤T^(2/15)。它的全部剩余低导子项都强迫双频含大素因子 p，可以
付清尾项。因此这一小余因子族的整个 fixed H/L centered 包为
O(A₃₀T^(1+ε))。其余平方自由 e、合数 q、外层和完整 gate 仍未解决。

## GW1. 唯一上游、原式与两个不同的截断

Git 父版本为 #553 **a4f2b4565eeeafff81a8deba2efa4169f0425276**。
原式严格为 [GH1–GH4](2026-08-31-physical-general-gauss-high-conductor.md)：
q₀=a₀=b₀=1，q∈[Q,2Q) 素数，e∈[E,2E) 平方自由，2E<Q；
R≈S≈EQ≈T³，H≈L≈T^(5/2)，E≈T^η，1≤η≤5/4。
原 μ(e)μ(q)μ(n)、两 taper、(n,eq)=(uv,q)=1、原 smooth Ψ 和唯一
2T/(RS) 不变。A₃₀ 包含原核及两 taper 的总阶≤30归一化半范数。
仍要求原整包 n,eq≤N/2，不回溯使用一般硬 H/L 包。

记 U=H/E，V=L/E，Dᵢ≈√T 为 GH 双频自然长度，ν=RD₁D₂/(EQ)≈T。
GH3 给 C_sf=F+O_q−B_nq−B_qd，三个差项都在 A₃₀T 预算内。
F 的周期/连续相位为 e_e(−nρσ inverse(q))e(nρσ/(eq))。
用 GH6 全角色展开，e=cℓ，χ primitive mod ℓ，得到
\[
 {\mu(\ell)\tau_\ell(\bar\chi)\over\varphi(c)\varphi(\ell)}
 \chi(-n)\bar\chi(q)\bar\chi(c)\chi(\rho\sigma)
                   \sum_{d\mid(c,\rho\sigma)}\mu(d)d.        \tag{GW1}
\]
再乘原 μ(q)μ(n)、UV/q、共同 Φ（已含 taper）和 chirp。
χ 是模 ℓ 的 primitive 零延拓，不是模 e 的诱导零延拓。
ℓ=1 时 χ 对全部整数为1，principal 也有完整 d 和。

对1≤Z≤E、1≤D≤2E，定义 F_<,≤ 为 GW1 中 ℓ<max(2,Z)、d≤D 的
准确子和，F_<,> 为其 d>D 补集。已有高部 F_≥ 来自 GH。
\[
                 F=F_\ge+F_{<,\le}+F_{<,>}.                  \tag{GW2}
\]
这只是线性恒等式；d 是 Ramanujan 容斥除数，不能把它改称原 gcd。
不删交叉项，也不声称这些部分是正交能量。

## GW2. 先重排 c，再保留完整两次单位容斥

令 j=gcd(d,ρ)、k=d/j，ρ=jr、σ=ks，(r,k)=1。写 c=da，则
e=ℓda 平方自由。χ(d)barχ(c)=barχ(a)，角色部分成为
χ(−n)barχ(q)barχ(a)χ(r)χ(s)，实系数保留 μ(ℓ)μ(d)d。
原额外 n-mask 是(n,da)=1；ℓ-unit 由 χ 实现。准确展开
\[
 1_{(n,a)=1}=\sum_{f\mid(n,a)}\mu(f),\quad n=fm,\ a=fb,
 \qquad 1_{(r,k)=1}=\sum_{v\mid(k,r)}\mu(v),\quad r=vz.      \tag{GW3}
\]
固定 d,j,k,f,v 后，保留 μ(f)μ(fm)，不把 μ(fm) 因子化。
平方自由性给(f,b)=(fb,dℓ)=1；共同 m-mask 是(m,d)=1，共同 b-mask
是 b 平方自由且(b,df)=1；ℓ 行保留平方自由及(ℓ,df)=1。
不添加(m,b)=1或(m,f)=1。χ(f)barχ(f)=1；χ(v) 是保留的单位标量。
准确剩余系数为
\[
 {\mu(\ell)\mu(d)d\mu(f)\mu(fm)\mu(v)\mu(q)
       \tau_\ell(\bar\chi)\chi(-1)\chi(v)
   \over\varphi(\ell dfb)}
                   \chi(m)\bar\chi(bq)\chi(z)\chi(s).        \tag{GW4}
\]
chirp 变为 e(mvzs/(ℓbq))，所有原归一化权仍同一个。

对 ℓ≈L₀≥1、双频 J₁,J₂≥1/2 的块，六个共同坐标是
\[
 m/(R/f),\quad b/(E/(L_0df)),\quad q/Q,\quad\ell/L_0,
       \quad z/(J_1/(jv)),\quad s/(J_2/k).                  \tag{GW5}
\]
e/E 是中间 b 与 ℓ 归一化坐标的乘积。X=RJ₁J₂/(EQ)≈J₁J₂，
不除以 d/f/v。空整数标签块为0，非空时两缩放标签长度都≥1/2。
e/φ(e) 按 d,f,b,ℓ 的互素乘积分入算术列，E/e 分入光滑核；
Gauss 归一化模长为 d√L₀ T^ε/E，不丢 φ 或再乘 A₃₀。

## GW3. 硬 e 壳的精确分离，不假装为光滑原权

原 E≤e<2E 在重排后是联合条件 E≤ℓdfb<2E。它既不是单独模数行，
也不能放入统一 C∞ 核。对整数 e，先改写为 ceil(E)≤e≤ceil(2E)−1。
在两个半整数端点之间，构造以 log(e/E) 为变量的光滑阶梯 h_E；
过渡宽度在 e 变量至多1/4，因此在全部整数点精确等于该指示函数。
在固定较大 log 区间上零延拓再周期化，支撑不碰接缝。
\[
 \operatorname{Var}(h_E)\ll1,\quad\|h_E''\|_1\ll E,
 \quad |\widehat h_E(k)|\ll\min(1,(1+|k|)^{-1},
                         E(1+|k|)^{-2}),
 \quad\sum_k|\widehat h_E(k)|\ll\log(2E).                  \tag{GW6}
\]
绝对收敛 Fourier 级数是精确等式，没有 Perron 截断误差。
每个频率只给 ℓ 行及 b 共同列乘同一对数相位；不进入两个 Weyl 标签。
故只支付 log(2E)，不对 A₃₀ 收取 E 阶导数或额外频率权。

## GW4. 已发表 Weyl 输入如何作用于真实光滑标签

[Petrow–Young, Corollary 1.3](https://arxiv.org/pdf/1811.02452v3) 给
cube-free primitive χ 的 |L(1/2+it,χ)|≪_ε[ℓ(1+|t|)]^(1/6+ε)。
这里 ℓ 平方自由，满足条件。对固定 ψ∈C_c∞((0,∞))，平滑 Mellin
反演移至1/2线可得
\[
 \left|\sum_{n\ge1}\chi(n)\psi(n/J)n^{it}\right|
 \ll_\epsilon\sqrt J[\ell(1+|t|)]^{1/6+\epsilon}
           +1_{\ell=1}J(1+|t|)^{-B}.                        \tag{GW7}
\]
ℓ>1 无极点；ℓ=1 的极点项准确为 J^(1+it)hatψ(1+it)，不是删除它。
平滑 Mellin 衰减与 L 的多项式增长支持移线及无限积分。
这不是任意 BV 或硬截断角色和的 Weyl 界。

chirp 的 Mellin 表示沿用 LP12：驻相段 |t|≈X，幅度≪X^−1/2，
时间宽 X。两标签长度 J′=J₁/(jv)、J″=J₂/k≤C X。任意 log 原子
频移 ω 都保留：GW7 加上近 t+ω=0 时的平凡界，给
\[
 |L_{\chi,J'}(t+\omega)|\ll_\epsilon
 \sqrt{J'}L_0^{1/6+\epsilon}X^{1/6+\epsilon}
                       (1+|\omega|)^{1/3+\epsilon}.          \tag{GW8}
\]
负整数标签保留 χ(−1)，以绝对值取 log，在线性式中不翻转 it；
负时间的绝对值估计可用共轭。正负 ρσ 决定 chirp 符号。
两个标签合计 L₀^(1/3+ε)X^(5/6+ε)/√(dv) 乘两个 ω 权。
六维 H⁴ 足够，因为4>3+2/3+2ε。双 Fourier 各12次 IBP、参数总阶4，
原导数28≤30；所以加权原子 ℓ¹≤A₃₀∏(1+λᵢ)^−8，λᵢ=Jᵢ/Dᵢ。
硬壳 GW6 的额外频率不进这两个标签权，A₃₀ 只乘一次。

## GW5. 跨 ℓ 的共同两列及所有外层费用

固定 d,j,k,v,f,L₀，m 列长 N₁=R/f，bq 产品列长 N₂=S/(L₀df)，
能量分别≪N₁T^ε、N₂T^ε。μ(fm)、b 的全部 masks/φ 因子及素数 q
留在共同系数内；产品碰撞以 τ₂ 支付。ℓ-unit 由 χ 零延拓实现，
模数标量可在正大筛量中扩和。非空 b 支撑保证 N₂≥cQ，端点无 +1 损失。
按 [CIS (1.6)](https://arxiv.org/pdf/1105.1176) 普通 hybrid primitive
大筛，仅作一次共同 (ℓ,χ,t) Cauchy。未乘原2T/(RS)时得到
\[
 {A_{30}T^\epsilon UV\over QE}L_0^{5/6}\sqrt d\,X^{1/3}
 \sqrt{{R\over f}{S\over L_0df}
           (R/f+L_0^2X)(S/(L_0df)+L_0^2X)}
                 \prod_i(1+\lambda_i)^{-8+\epsilon}.        \tag{GW9}
\]
已放大 v^−1/2≤1；j|d、v|d/j 合计只是有限除数费用。
ℓ=1 用普通时间均值，公式 L₀=1 同样有效。不能再乘角色或模数个数。
GW9 根号展开后的四个成本是
\[
 RSX^{1/3}L_0^{-1/6}d^{-1/2}f^{-2},\quad
 R\sqrt S X^{5/6}L_0^{4/3}f^{-3/2},\quad
 S\sqrt R X^{5/6}L_0^{5/6}d^{-1/2}f^{-3/2},\quad
 \sqrt{RS}X^{4/3}L_0^{7/3}f^{-1}.                           \tag{GW10}
\]
f≤2E/(ℓd)，末项 f^−1 收取 log(2E)；其余 f 和收敛。
d≤D 的费用依次为 √D、D、√D、D；j/v 除数费吸收入 T^ε。
dyadic L₀≤max(2,Z) 中第一项 L₀^−1/6 可和，其余付 Z^(4/3)、
Z^(5/6)、Z^(7/3)。不重收已经缩短的 d/f 行数。

## GW6. 双无限频率、时间尾与明确支付的子和

一般 X=νθ、θ=λ₁λ₂ 的四项相对自然尺度增长依次为
θ^(1/3)、θ^(5/6)、θ^(5/6)、θ^(4/3)。显式保留无界 X^ε 的
max(1,θ)^ε，不把它全藏入 T^ε；与双8阶衰减在大小方向都可和。
X 有界时原 J₁,J₂ 均有界，非空 d/v 分配也有界；用统一 Schwartz
Mellin 和宽度1的大筛即可，由自然尺度四项的同一 majorant 覆盖。

非驻相内段 Mellin≪X^−B，外环 |t|≈W≥CX 时≪W^−B；改用平凡
标签 J₁J₂/(dv)≪X/d，不要求 ω 小。相对驻相标签至多增 X^(1/6)，
而幅度多 X^(1/2−B)，B≥3足够；外环大筛至多再增 W/X，可和。
因此全部硬壳/原子/Fourier/Mellin 截断有一致可和 majorant，可以换序。
这仅支付本 fixed H/L 包内部尾，不是所有 H/L 或 AFE 外层。

恢复原外权，得到
\[
 |F_{<,\le}|\ll_\epsilon {A_{30}T^{1+\epsilon}\over RS}{UV\over QE}
 \{RS\nu^{1/3}\sqrt D+R\sqrt S\nu^{5/6}Z^{4/3}D
       +S\sqrt R\nu^{5/6}Z^{5/6}\sqrt D
       +\sqrt{RS}\nu^{4/3}Z^{7/3}D\}.                       \tag{GW11}
\]
Z=T^z、D=T^γ 时四指数为
\[
 10/3-2\eta+\gamma/2,\quad7/3-2\eta+4z/3+\gamma,\quad
 7/3-2\eta+5z/6+\gamma/2,\quad4/3-2\eta+7z/3+\gamma.        \tag{GW12}
\]
η=6/5、z=1/5、γ=2/15 给(1,1/3,1/6,−7/15)。普通 hybrid 不处理
标签时，同一短 d 子和的首项仍是11/10；这里净改善1/10。
对于任意平方自由 e，这只给 C_sf=F_<,>+O(A₃₀T^(1+ε))。

## GW7. 新的完整原子：小余因子乘大素数

现进一步在原 GH1 选 e=h₀p，h₀≤B=T^(2/15)、p 素数、(h₀,p)=1。
h₀ 不是 canonical a₀/b₀，它们仍为1。E≈T^(6/5) 保证
p≥E/B>√(2E)、Z、B（有限小 T 吸收入常数），因此 p 标签唯一。
高 ℓ 的 GH10 固定 c 后允许此 e-family 作为模数行标量，原界不变。
低 ℓ<Z 必须整除 h₀；d|e/ℓ 要么 d|h₀、d≤B，要么 p|d。

不能直接对 GW11 已得的 signed 总和删 e 行。这里重证所需共同性。
在短 d 的 e=ℓdfb 中，大素数 p 不在 ℓ/d。按它在 f 还是 b 分两类：
f 有 p 时 p 固定、b 不含 >√(2E) 的素因子；f 没有 p 时，b 恰有
一个这样的素因子 p=P_big(b)。这些都是固定 f 后的共同 b 条件。
原 e≤2E 保证不会有两个大素因子；正大筛扩和时也保留该共同限制。
余因子条件分别是 ℓd(f/p)b≤B 或 ℓdf(b/p)≤B，都是整数乘积 cutoff。

再次按半整数端点精确插值，log 周期 P=O(log(2E))。其 variation
仍 O(1)，二阶 L¹≪B+1；周期 Fourier 係数≤min(1,1/|k|,
P(B+1)/k²)，故 ℓ¹≪log(2E)，连同 GW6 至多 log²(2E)。低端接缝放在所有正整数
log 取值之外。每个 mode 只给 ℓ/b 两列乘相位；P_big(b)^−iω 是
共同 b 系数的一部分，模长1。不进两个标签频移，不收 A₃₀ 导数。
于是 GW9–GW11 在此真实 e-family 上重跑后仍成立。

剩余 p|d 的低角色项，先对完整周期係数取上界
\[
 {1\over\varphi(e)}\sum_{\ell\mid h_0}\ell^{3/2}
                       \sum_{d\mid e/\ell}d
       \ll_\epsilon T^\epsilon h_0^{3/2}\le T^\epsilon B^{3/2}. \tag{GW13}
\]
用的是 #χ*≤ℓ、|τℓ|=√ℓ、有限除数界，不是正性断言。
p|ρσ 强迫 p|ρ 或 p|σ。保留原 Φ 的6阶非零倍数尾，得
\[
 |F_{<,>}|\ll A_{30}T^\epsilon {T\over RS}EQR{UV\over Q}B^{3/2}
   [(D_1B/E)^6D_2+D_1(D_2B/E)^6]
       \ll A_{30}T^{-9/10+\epsilon}.                         \tag{GW14}
\]
e/q/n 的全部行数已付；O_q、B_nq、B_qd 原上界也允许此限制。
所以新的完整物理结论是
\[
 \boxed{|C_{e=h_0p,\ h_0\le T^{2/15}}|
            \ll_\epsilon A_{30}T^{1+\epsilon},\qquad\eta=6/5.} \tag{GW15}
\]
高/低/差项来自同一个原式，不把 saving 相乘。它超出旧平衡半素数域：
h₀ 可以含多个小素因子，或随 T 增长但远小于 √E。

无限非空原支持可取 h₀≈Y、p≈Y¹¹、q≈Y¹⁸ 为互异素数，e=h₀p，
R=S=eq、T=(8S)^(1/3)、N=8S。则 h₀≈T^(1/10)<T^(2/15)。
沿 GH 的构造取素数 n∈(S,2S)，H=L=S/√T，u=v=ceil(H/e)，
x=3√T/4；原单位条件、n,s≤N/4 和正 AFE 支撑都非空。
Bertrand 与有限 dyadic 取整即可；不声称任意给定积分非零或正密度。

GW15 不覆盖其余平方自由 e、合数 q、其他 canonical/q₀、full h/δ、
跨 AFE 尾或实际 amplified 系数。EE*、EC*、CE*、CC* 不被删去。
完整 coupled-kernel、twisted moment 和零点目标仍未证明。
附有限脚本仅检验恒等式、masks、端点与成本账，不替代 Weyl 输入、
大筛、全部解析换序或最终 main/Lean 验收。
