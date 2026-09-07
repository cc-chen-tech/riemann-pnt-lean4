# 物理双 completion 的全部频率：零差带求值与显式 signed 补集

白话结论：canonical 零点之外的频率可以全部写回原 zeta 变量的整数差，因而补集不必只用 `H−L−G` 定义。把**零差整条频率带**一起结账，延拓常数 κχ 精确地被离散格点的 2γ 替代；但 log T 级长 Möbius Gram 仍在，并未消失。这是全局 adapter 与零带求值的增量，不是新的幂次节省，也不是完整 twisted moment 证明。

沿用 [PA](2026-08-30-mwkf-physical-reflection-adapter.md) 的固定 χ、精确 AFE、原系数 a 和主项矩阵 L，以及 [ZW](2026-08-30-mwkf-canonical-zero-weight.md) 的 g、G、λ。T≥2，N≤T³，W 为固定实光滑紧支撑权。所有傅里叶变换取 e(x)=exp(2πix)。本篇整数差 j 与此前 κ-Poisson 的 j、Type quotient 的 h **不是同一个标签**。

## 1. 从 (4.5) 的原 hδ 相位到全部双对偶频率

先固定互素正整数 r≠s，令 b=r−s、m=|b|、ε=sgn(b)。选 β 满足 sβ≡1 (mod m)，m=1 时 β=0。则 α_b=(1−sβ)/b 为整数，α_b≡r̄ (mod s)，包括 s=1 的约定。下文 γ 专指 Euler 常数。因此精确互反式是

\[
 e(-h\delta\bar r/s)
 =e(\beta h\delta/b)e(-h\delta/(bs)).                 \tag{SF1}
\]

令 f(x,δ) 是 (4.4) 去掉 e(−hx/s) 后、乘 PA7 正则化的完整函数。可先保留一个 dyadic box，也可在固定 r,s 上重组全部原 partition。定义

\[
 \psi(h,\delta)=e(-h\delta/(bs))\int f(x,\delta)e(-hx/s)\,dx.
                                                               \tag{SF2}
\]

f 与 ψ 都是 Schwartz：两个 zeta 变量均至少 1/4，V 在其乘积上任意阶衰减；线性变换、部分 Fourier 变换和乘二次相位保留 Schwartz 空间。因此下列双 Poisson 与删轴均绝对收敛，不需要以条件收敛换序解释。有限模 m 的 Gauss 和为

\[
 \sum_{a,c\bmod m}e(\beta ac/b+(\nu a+\omega c)/m)
 =m e(-s\nu\omega/b).                                      \tag{SF3}
\]

证明是先求 c：唯一存活的 a≡−εsω (mod m)。故

\[
 \sum_{h,\delta\in\mathbb Z}e(\beta h\delta/b)\psi(h,\delta)
 ={1\over m}\sum_{\nu,\omega\in\mathbb Z}
       e(-s\nu\omega/b)\widehat\psi(\nu/m,\omega/m).          \tag{SF4}
\]

这是带有限周期乘子的 [Poisson 公式](https://dlmf.nist.gov/1.8.iv)。m=1 仍有全部整数 ν,ω，**不是只剩 (0,0)**。

先对 h 作 Fourier 反演，再置 u=−δ/b−sξ，得到

\[
 \widehat\psi(\xi,\zeta)
 =sm\int f(u,-b(u+s\xi))e(\zeta b(u+s\xi))\,du.             \tag{SF5}
\]

在 ξ=ν/m、ζ=ω/m 上，SF3 的相位与 SF5 的常数相位精确消去。令 j=−εν、k=εω；这是 Z² 的双射。第二个 zeta 变量为 u+j，于是

\[
 {1\over s}\sum_{h,\delta\in\mathbb Z}
    e(-h\delta\bar r/s)\widehat f_\delta(h/s)
 =\sum_{j,k\in\mathbb Z}\int f(u,sj-bu)e(ku)\,du.           \tag{SF6}
\]

sm、1/m 与原 1/s 已全部计入。两侧再乘 2/√(de)，d=qr,e=qs；没有额外 q、|b| 或两个 AFE 方向的再一次因子 2。

### 原来删除的两条轴

记 SF4 左边为 P，H₀=Σδψ(0,δ)，D₀=Σhψ(h,0)，O₀=ψ(0,0)。则 (4.5) 的双非零部分严格为

\[
 P-H_0-D_0+O_0.                                             \tag{SF7}
\]

原第一层零频是 H₀−O₀；原 AFE 对角是 D₀，经 /s 的 Poisson 恢复后恰为 n=sℓ、m₁=rℓ，即 m₁s=nr。加回二者才恢复 P。χ 延拓改变产生的补偿按 PA8 保留。SF6 的 j=0 则是 **m₁=n**，与该 AFE 对角不是同一条轴。

## 2. 不再供应任意补集矩阵：显式物理系数与截断

对所有 d,e≤N（包括 d=e），定义

\[
 \begin{split}
 \Phi_{d,e}(u,v)={\chi(u)\chi(u+v)\over\sqrt{u(u+v)}}
 \int W(t/T)V_t(u(u+v))
        (e/d)^{it}((u+v)/u)^{it}\,dt,\\
 A_{d,e}(j,k)=\int\Phi_{d,e}(u,j)e(ku)\,du.
 \end{split}                                                \tag{SF8}
\]

当 u≤0 或 u+v≤0 时置零。对 d≠e，SF6 正是此式；d=e 时不除 r−s，而是直接先按 m₁−n=j 重组原 AFE，再在 n 上 Poisson。由此有逐矩阵元的物理恒等式

\[
 H_{d,e}={2\over\sqrt{de}}\sum_{j,k\in\mathbb Z}A_{d,e}(j,k).
                                                               \tag{SF9}
\]

在 k 上恢复整数格后，右侧是原 (2.4) 的两个方向合计，而非模型核。Φ 是 Schwartz，A 在两个整数标签上任意阶衰减。更定量地，对整数 a≥2 令

\[
 S_a(\Phi)=\sup_v(1+|v|)^a\left(\|\Phi(\cdot,v)\|_1
                +(2\pi)^{-a}\|\partial_u^a\Phi(\cdot,v)\|_1\right).
\]

分部积分（χ 的平坦端点消除边界）给出

\[
 |A(j,k)|\ll_a S_a(\Phi)(1+|j|)^{-a}(1+|k|)^{-a},\quad
 \sum_{\max(|j|,|k|)>Y}|A(j,k)|\ll_a S_a(\Phi)Y^{1-a}.       \tag{SF10}
\]

这里还有**对 d,e 一致的物理界** S_a(Φ)≪a,W,χ T^{2a+2}。证明：置 y=u+v，在支撑上 u,y≥1/4，1+|v|≪1+uy。原 (2.5) 与乘积法则给出
|∂u^ℓΦ|≪ℓ,B T^{ℓ+1}(uy)^{-1/2}(1+uy/T)^{-B}。
权 (1+|v|)^a 花 T^a，取 B>a+1；置 x=min(u,y)，剩余积分至多
∫₁/₄^∞ x^{-1}(1+x²/T)^{-B+a}dx≪log(2T)。因 |(e/d)^{it}|=1，此处无 N 或 log(d/e) 损失。

对原 Selberg 系数，Σd≤N|a_d|/√d≤2√N。因此将 SF9 **整个矩形**截为 |j|,|k|≤Y≥1，二次型误差满足

\[
 |E_Y|\ll_{a,W,\chi}N T^{2a+2}Y^{1-a}.
 \quad Y=\lceil T^4\rceil\Longrightarrow |E_Y|\ll T^{9-2a}.
                                                               \tag{SF11}
\]

故任意指定 B>0，取 a≥(B+9)/2 即得 O(T^{-B})。边界包含 |j|=Y 或 |k|=Y，尾是严格大于 Y。相同方法给 SF7 的原轴收敛；若坚持原 h 截断，则使用 PA4，不把 SF11 当作单个 h-box 的局部界。全有限 N 求和、所有 gcd、原 dyadic partition 都在此之前重组，既不丢空尺度补偿，也不支付任意多次 Cauchy。

## 3. 零差整条频率带的精确求值

定义离散的、延拓无关的权

\[
 D(t)=2\sum_{n\ge1}{V_t(n^2)\over n},\qquad
 \Omega_{\rm eq}(t)=W(t/T)D(t).                              \tag{SF12}
\]

在 j=0 上对全部 k 作 Poisson，χ(n)=1，给出

\[
 2\sum_k A_{d,e}(0,k)
 =\int\Omega_{\rm eq}(t)(e/d)^{it}dt,\quad
 2A_{d,e}(0,0)=\int\Omega_\chi(t)(e/d)^{it}dt.                \tag{SF13}
\]

现在不是把连续零点误称为离散 m₁=n 子和：**只有整条 k 带**才恢复该子和。单独 k≠0 的精确公共权为 Ωeq−Ωχ。

在原直线 Re z=2 绝对收敛地展开，

\[
 D(t)={2\over2\pi i}\int_{(2)}
       {g_t(z)G_t(z)\zeta(1+2z)\over z}\,dz
      =\lambda(t)+2\gamma+E_{\rm eq}(t).                    \tag{SF14}
\]

原点留数使用 [ζ 在 1 的 Laurent 展开](https://dlmf.nist.gov/25.2)；gG=1+λz+O(z²)，ζ(1+2z)=1/(2z)+γ+O(z)，外因子 2 不可漏掉。

为明确全部深移线项，取正整数 B，zₖ=−sₜ−2k、K_B={k≥1:2k+1/2<B}。定义

\[
 r_k^{\rm eq}(t)={2(-1)^k\over k!}
 {G_t(z_k)\pi^{-z_k}\Gamma(-k-it)\over
       \Gamma(s_t/2)\Gamma((1-s_t)/2)}
 {\zeta(1+2z_k)\over z_k}.
\]

则 Eeq 等于新直线 (−B) 积分的两倍，加 4Re Σk∈K_B rkeq。k=0 的两个 gamma 极点仍被 G 消去；其余不能删除。ζ(1+2z) 在该固定垂线上及其固定阶导数至多多项式增长，由函数方程和右半平面的绝对收敛级数即可得出。它在 |Im z|≤t/2 上与 t 无关，故 ZW10 的带导数界保持；外区与移动留数的多项式成本被 Gaussian 吸收。水平边积分也趋零。因此对任意 A,j≥0，

\[
 E_{\rm eq}^{(j)}(t)\ll_{A,j}t^{-A-j},\quad
 \Omega_{\rm eq}-\Omega_\chi
 =W(t/T)(2\gamma-\kappa_\chi+O_A(t^{-A})).                  \tag{SF15}
\]

这是本次可以求值的**整条非零 k 修正**。它抵消延拓常数，不抵消 λ(t)。不能仅凭它的权少一个 log T，便把其长 Möbius 二次型判作 O(T^{1+ε})。

## 4. 一个共同坐标上的完整 signed operator

以下矩阵均作用于原 a_d；PA 的 c_d=a_d/√d 只是一种明确的归一化，不把除数卷积 B 直接代入这里。定义

\[
 \begin{aligned}
 (K_{\rm eq})_{d,e}&={1\over\sqrt{de}}
           \int\Omega_{\rm eq}(t)(e/d)^{it}dt,\\
 (K_{\ne})_{d,e}&={2\over\sqrt{de}}
           \sum_{j\ne0,\ k\in\mathbb Z}A_{d,e}(j,k),\\
 (J_\chi)_{d,e}&={2\mathbf1_{d\ne e}\over\sqrt{de}}
           \sum_{(j,k)\ne(0,0)}A_{d,e}(j,k)
           +\mathbf1_{d=e}H_{d,d}-L_{d,e}.
 \end{aligned}                                                \tag{SF16}
\]

于是逐矩阵元、同一有限系数空间中，

\[
 \boxed{R=H-L=G_\chi+J_\chi=K_{\rm eq}+K_{\ne}-L.}          \tag{SF17}
\]

这给 PA18 的 Jχ 一个**显式物理频率表达式**。其对角不是 0；原 AFE 对角、第一层 h=0、SF7 删轴及 PA8 延拓补偿已通过 SF7 的重组逐项结清，并没有被假设小。实 W 下 V_t 实值，交换 u 与 u+j 得到 overline(A_{d,e}(j,k))=A_{e,d}(−j,−k)，其中平移产生的 e(−kj)=1。因此这些总矩阵是 Hermitian；对实 a 二次型取实值。若使用实对称算子，可取实部，二次型不变。

令 M_N(t)=Σd≤N a_d d^{-1/2-it}。零差完整 Gram 的二次型为

\[
 a^*K_{\rm eq}a=\int W(t/T)(\lambda(t)+2\gamma+E_{\rm eq}(t))
                          |M_N(t)|^2dt.                    \tag{SF18}
\]

此处 a 为原实 Selberg 系数（复系数需同步更改相位/共轭约定）。W≥0 时大 T 下 K_eq 正半定，且 SF18 与 log T∫W|M_N|² 双边可比。其 O(T^{1+ε}) 上界仍未证明。去掉 mollifier d=e 对角至多减去 O(T log T log(2N))；那不是原 AFE 的 m₁e=nd 对角。

若以 E=K_eq−L、C=K_ne，唯一的全局平方必须保留

\[
 RR^*=EE^*+EC^*+CE^*+CC^*.                                  \tag{SF19}
\]

C 也**不自动有零行和或零列和**。要使用 PA20 的加权中心化，应再显式分离其低秩边际，不能删掉它们；更不能把 j≠0 直接等同于 TT* 的非零 determinant。这里没有证明通用全算子范数界。

## 5. 与 reflection packet 的接合和本次边界

SF9 恢复的是 PA17 的整个 H。再按 PA3 恢复整数格并令 x=dn、y=em₁，才能应用 PA10–PA16 的共同乘积截断与完整 Mellin 家族，严格得到 FF−FR−RF+RR；两个 mixed 项都保留。单个 k 的积分仍有连续 u，不能逐 k 把 dn、em₁当作整数来做除数 reflection。两个表示之间是**全局重组**，不是 packetwise 等距声称。

可同时使用 Y=⌈T⁴⌉ 的 SF11 尾和 PA15 的共同 X 尾：对目标 O(T^{-B})，选择 a≥(B+9)/2、X≥T^{7+2B/3}。这是分别与同一个完整 I 比较后相加的误差，不声称两个截断交换。N 的末端 a_N(N)=0，严格反射端点 D>N 及 kN<x 仍按 PA11，不存在额外 floor 半权。

新增的有限 helper 检验 SF1/SF3 的有符号短模数、SF5 的相位/Jacobian、有限周期完成的两条删轴和整数差与原 AFE 对角的区别。有限周期 DFT 的 (0,0) 汇总含连续 Fourier 别名，**不把它当作 canonical 零点**；这些测试不证明连续 Poisson、移线或渐近上界。解析结论由上文证明给出。

本次新增的是：全部双频率物理 adapter、显式补集、物理截断尾，以及零差整条频率带的权。它排除了“格点恢复频率自动消掉 log T 零 Gram”的期待；没有排除其与 j≠0、LCM、reflection 的进一步全局抵消。没有新增参数覆盖或证明缺少的 T² saving，完整 coupled-kernel gate 和 twisted moment 仍未完成。

验证记录：新增有限测试 26 项先因缺失 adapter 失败、实现后通过；本轮可运行 Python 套件 1434 passed、1 skipped。环境未提供 Flint，明确排除 `test_weil_interval_auxiliary.py` 与 `test_weil_interval_ccm.py` 两模块；不将它们计为通过。独立数学复核核对 SF1–SF19，未发现阻断项。本轮未改 Lean，测试及复核都不构成完整 twisted-moment 的机器证明。
