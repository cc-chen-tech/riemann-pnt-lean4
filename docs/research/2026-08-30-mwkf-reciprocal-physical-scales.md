# Reciprocal windows 的物理尺度修正与未消失的离散边界

白话结论：MRSTT 的短区间定理确实能控制这里的平滑倒数相位，并非
“几乎所有窗口”就不能用于全区间。但是在不平衡箱中，必须先把第二次
Poisson 的长度改成 `M=AS/R`。这样可以修复**临界平滑模型**的总账。
亚临界模型还有真实的整数计数边界；它在部分箱中可吸收，但并未在
整个多面体上消失。这不是完整 twisted-moment 证明。

**范围。** 本文独立核对了
[候选推导的固定版本](https://github.com/cc-chen-tech/riemann-pnt-lean4/blob/7cc472d45f934f7465a8543273a3bb866ef8da5a/docs/research/2026-08-25-mwkf-alternative-routes-spike.md#L21820)
中 cubic reciprocal-window 路线。未修改其分支；以下结论不依赖该版本
的状态布尔量。(RP1)–(RP3) 是物理尺度恒等式；(RP4)–(RP8) 是有明确
平滑假设的解析引理；(RP9) 是可直接形式化的有限命题；(RP10)–(RP11)
给出部分边界覆盖。(RP12) 保留真正的剩余条件。

## 1. 第一次 Poisson 决定第二次变换的长度

选择长模数方向，记原 entry 长度为 `R≤S`，`r_entry=A b`，`E=R/A`。
此处 `A` 始终是 Type allocation 的整数乘积，不能改名为 Fourier 长度。
第一次 quotient Poisson 的实际因子是

\[
 \widehat U(mE/s)=\widehat U\!\left({mR\over As}\right),
 \qquad s\asymp S,
 \qquad \boxed{M={AS\over R}}.
\tag{RP1}
\]

来源是候选稿的 (4.845ao)，不是渐近估计。`m≈A` 只在 `R≈S` 时成立。
若 Fourier 尾在自然长度外按对数截断，支持是 `|m|≲M log^K T`，不是
`A log^K T`。例如允许箱
`(ρ,σ,m_zeta,k_zeta,ℓ,h,κ)=(2,3,1,0,2,2,0)` 给出 `S/R=T`。

这里还可以直接检验振幅，而不引入任意人为核。令 `τ=S/R`、`s=Sx`。
若错误地用 `y=m/A`，真实 quotient 因子变成

\[
 \Phi(x,y)=\widehat U\!\left({y\over\tau x}\right),
 \qquad
 \widehat\Phi_2(x,\xi)=\tau x\,U(-\tau x\xi).
\tag{RP2}
\]

这是 Fourier 反演和尺度变换的精确公式。取 `e=r=1,j=-1`，则在
`ξ=jA/(Sx)` 处右边是 `τx U(A/R)`。固定 `U(A/R)≠0` 时，它有 `τ`
大小，不能用统一的 polylog seminorm 上界。按自然 `M` 长度作平滑尾
截断只给 Schwartz 小误差，不消除这个因子。这个例子反驳的是原坐标
中的**统一振幅界**，不是实际 Selberg 余项的目标估计。

## 2. 修正后的 complementary-divisor Poisson

以后 `e` 表示 Ramanujan 分解的 cofactor，`r` 表示去除互素条件后的小
smooth cofactor，均不再是原 entry。置

\[
 D=S/e,\qquad d=rn,\qquad X=D/r,\qquad
 Z=Akl,\qquad M=AS/R.
\]

令 `W` 支持在固定正紧区间；`Φ(x,y)` 在 `x≈1` 上平滑，在 `y` 上紧
支撑或 Schwartz。假定所需的混合导数及其 `y` 加权积分只有固定对数
损失。该假设只对已实际分离的**平滑部分**使用，不包含未展开的算术
掩码。定义包含所有整数 `c` 的局部模型

\[
 \begin{aligned}
 C&={1\over e^2}\sum_n{\mu(n)\over rn}W(n/X)
      \sum_{c\in\mathbb Z}\Phi\!\left({n\over X},{rnc-Z\over M}\right)\\
  &={M\over r^2e^2}\sum_{j\in\mathbb Z}\sum_n{\mu(n)\over n^2}W(n/X)
      \widehat\Phi_2\!\left({n\over X},{jM\over rn}\right)
      e\!\left(-{jAkl\over rn}\right).
 \end{aligned}
\tag{RP3}
\]

证明：在 `c` 积分中代入 `y=(rnc-Z)/M`，Jacobian 为 `M/(rn)`，平移
相位是负号。然后逐个 `n` 使用 Poisson。`n` 和因 `W` 有限；Fourier
`j` 和一般**无限但绝对收敛**，不能把精确 Poisson 称作有限截断恒等式。
有限截断的误差见下文。若原 packet 只含 `c≠0`，必须另外减去

\[
 C_{c=0}={1\over re^2}\sum_n{\mu(n)\over n}W(n/X)
                 \Phi(n/X,-Akl/M).
\tag{RP4}
\]

`c=0`、`j=0`、AFE 显式 diagonal、以及 (PA) 的 canonical zero Gram
是不同对象，不能因为都叫“零项”就相互删除。

原 quotient 的 `m=0` 也须独立登记。对整数 `r,Z`，由 `m=rnc-Z`
可知其贡献恰为
\[
 C_{m=0}={1\over re^2}\sum_n{\mu(n)\over n}W(n/X)
                 \Phi(n/X,0)\,1_{rn\mid Z}.
\tag{RP4a}
\]
若同时排除 `c=0,m=0`，则用
`C-C_{c=0}-C_{m=0}+1_{Z=0}C_{c=0}`；交集仅在 `Z=0` 时出现。
若 `Φ(x,0)=0`，(RP4a) 为零；否则其中的整除掩码不是 (RP5) 的平滑
振幅，不能免费套用 MRSTT。把 `m` 再作细 dyadic 分割时，也必须重付
其相对于自然尺度 `M` 的导数成本。

## 3. MRSTT 输入与滑窗：这一部分成立

使用
[MRSTT, Theorem 1.1(i), v2 (2026-01-23)](https://arxiv.org/html/2411.05770v2#S1.Thmtheorem1.1)。
固定环面及其 Lipschitz 函数后，该定理在 `Y≥X^(1/3+ε)` 的几乎所有
窗口上，对固定次数多项式相位给出任意对数幂消去；其最大范数还允许
窗口内的算术级数。多项式系数可以随窗口改变，异常集合测度同样有
任意对数幂节省。以下是对此输入的独立推论。

固定 `1/3+ε<ν<1-ε`、`Y=X^ν`。若 `|B|Y^4/X^5≤T^(-b) log^C T`
有固定 `b>0`，且 `X` 与 `T` 具有固定正幂比较，则对每个 `L>0`

\[
 \max_{I\subset[X,2X]}
 \left|\sum_{n\in I}\mu(n)e(B/n)\right|
 \ll_L X\log^{-L}T.
\tag{RP5}
\]

**证明及误差。** 在每个窗口 `(z,z+Y]` 将 `B/n` 展开到三次，余项
统一为 `O(|B|Y^4/X^5)`。对任意区间 `I`，取
`I°=I∩[X+Y,2X-Y]`；精确连续滑窗恒等式为

\[
 \sum_{n\in I^\circ}v_n={1\over Y}\int_X^{2X-Y}
           \sum_{z<n\le z+Y}v_n1_{I^\circ}(n)\,dz.
\]

每个内部整数被覆盖的测度恰是 `Y`；端点是零测集。好窗口用 MRSTT
最大范数；坏窗口用 `O(Y+1)`。合计误差为
`O_L(X log^(-L)T + Y + X|B|Y^4/X^5)`。后两项幂次更小，得到 (RP5)。
这里没有假设某个预定离散网格避开异常集合，也没有要求单条 Möbius
仿射直线满足二阶 Chowla 估计。

置 `λ=jM/D`、`Gλ(x)=W(x) Φhat₂(x,λ/x)`。恒等式
`x d/dx = x∂x-ξ∂ξ`（沿 `ξ=λ/x`）以及
`ξ∂ξ Φhat₂=-Fourier_y[∂y(yΦ)]` 给出

\[
 \|t^{-2}G_\lambda(t/X)\|_\infty
 +\int|\partial_t(t^{-2}G_\lambda(t/X))|\,dt
 \ll X^{-2}\log^C T.
\tag{RP6}
\]

这是在**修正坐标**中使用已声明混合 seminorm 假设的结果。Abel 求和
将 (RP5) 变为每个保留 `j` 模式 `≪X^(-1) log^(-L)T`；并非对任意
带 `n` 算术掩码的振幅也成立。

## 4. 修正不会破坏临界模型的三次 Taylor 裕量

取 `u=max(ρ,σ)`、`a=ℓ+h`、`p=2u-a`。必要多面体条件是
`1/2≤u≤3, 0≤a≤2u-1`。置
`η=ρ_Q=ε=1/1000, ν=17/50`，并限制
`e≤T^η, r≤D^ρ_Q`。于是 `X≥T^x`，`x=(u-η)(1-ρ_Q)`。

临界区间应为 `M≥D log^(-K₀)T`，即 `A≥(R/e) log^(-K₀)T`。
令 `P=S²/(HL)=T^p`，`|kl|≲P log^C T`。保留模式
`|j|≤(1+D/M)log^Kmode T` 只有 polylog 个。由 `A≲R≤S`，
`|jAkl/r|≲eXP log^C T`。故

\[
 4(1-\nu)x-p-\eta
 \ge {3938033\over12500000}>0.
\tag{RP7}
\]

最低值出现在 `u=1/2,a=0`；这是仿射函数的直接计算。MRSTT 两侧
窗口裕量为 `17/3000` 和 `659/1000`。因此 (RP5) 的条件确实成立。

更重要的是，归一化总账也能修复。恢复单个 outer `A^(-1)` 后，每个
模式的无对数系数是

\[
 {1\over A}{M\over r^2e^2}X^{-1}
       ={1\over reR}.
\tag{RP8}
\]

假设 `|α(A)|≤τ_K(A)`、`A≈A₀≲R`，所有其余已分离参数的总变差只有
对数损失，且 `r` 只含 `Ae` 的素因子。保留模式的计数至多
`(1+R/(Ae))log^Kmode T`。于是完整临界模型由

`(HL/S) P = S`，
`Σ_e (e^(-2)+A₀/(eR)) Σ_{r Ae-smooth} 1/r ≪ log^C T`

和 (RP5) 给出 `O_L(S log^(-L)T)`。`S/R` 并没有留下额外幂次，但这
依赖同步改正长度、临界区间及 `A₀≲R`，不能只在一个公式中补因子。

**Fourier 尾。** 固定积分分部阶数 `J>2` 后，振幅有
`(1+|j|M/D)^(-J) log^C_J T` 衰减。超出上述 cutoff 的总尾，连同其他
固定对数损失，至多 `S log^(C+K₀-Kmode(J-1))T`。先选 `J`，再选
`Kmode`，最后选 MRSTT 的任意对数幂，足以满足任意固定目标。这是
对数尾控制，不是从 polylog cutoff 自动得到 `O(T^(-100))`。

## 5. 亚临界不能只付连续密度

以下有限命题不需要 MRSTT。给定实数 `D,r>0,M≥0,Z`，令

\[
 C_* =\left\lfloor{|Z|+M\over D}\right\rfloor,
 \qquad H_C=\sum_{1\le c\le C}1/c,\quad H_0=0.
\]

则精确整数和满足

\[
 \boxed{
 \sum_{\substack{n\ge1,\ D\le rn\le2D\\c\in\mathbb Z\setminus\{0\}}}
 {1\over rn}\,1_{|rnc-Z|\le M}
 \le {4M\over rD}H_{C_*}+{2C_*\over D}.}
\tag{RP9}
\]

**证明。** 有效 `c` 必须满足 `1≤|c|≤C_*`。固定 `c` 后，允许 `n`
的实区间长度最多 `2M/(r|c|)`，整数个数最多此长度加 1；再用
`1/(rn)≤1/D` 并对两个符号求和。`C_*=0` 两边都为零。所有整数端点
均包含，floor 不省略。附加模长不超过 1 的权或算术掩码只会减小此
正上界，故这也是直接可形式化的有限和命题。

`D=5,r=1,M=0,Z=30` 给出 `(n,c)=(5,6),(6,5),(10,3)`，左边 `7/15`，
连续长度项却为零。此例说明一般计数必须有边界；它**不**反驳物理
`M≈AS/R` 类的某个可能更精细的联合平均估计。

若 `|Z|≲AP`，(RP9) 在原 `e^(-2)` 权下给出

\[
 |C_{c\ne0}|\ll {M\over reS}\log T
                         +{AP+M\over S^2},
\tag{RP10}
\]

这里先对固定有限支持的、有界模型取绝对值；对数扩张支持只增加已
登记的对数因子。第二项来自整数 `+1`，不能略去。记
`B_*=max_{A,e} #{r≤D^ρ_Q:r Ae-smooth}`、`E₀=T^η`。完整 dyadic
outer 相对目标 `S` 的边界预算至多

\[
 \log^C T\,E_0B_*{A_0P+M_0\over S^2},
 \qquad M_0=A_0S/R.
\tag{RP11}
\]

这是将 `A,kl,e,r` 的真实计数全部付完的结果。对 `Ae≤T^C`，Rankin
上界 `B_*≤(D^ρ_Q)^b ∏_{p|Ae}(1-p^(-b))^(-1)` 对任意固定 `b>0`
成立。后一个有限 Euler product 为 `T^o(1)`，再取任意小固定 `b`
得 `B_*=T^o(1)`，**不是**统一 polylog。因此，写 `A₀=T^α` 后，
(RP11) 的两个幂次是 `η+α-a+o(1)` 和至多 `η-u+o(1)`。

在亚临界条件 `eM≲S log^(-K₀)T` 下，(RP10) 第一项的总账可用
`Σ_e e^(-2)` 吸收成任意目标对数幂。第二项只在有固定裕量
`a>α+η` 时由当前绝对估计闭合。示例：

| 平滑模型箱 | `u,a,α` | 边界相对 `S` 的主指数 | 当前边界结果 |
|---|---|---|---|
| balanced maximal | `3,5,≤3` | `≤-1.999` | 幂次更小 |
| unbalanced maximal，短 entry 为 `T²` | `3,4,≤2` | `≤-1.999` | 幂次更小 |
| balanced 小 shift | `3/5,1/5,3/5` | `401/1000` | 当前计数不覆盖 |

最后一行允许 `A₀≈R log^(-K)T`，所以幂次仍是 `α=3/5`，却可以处在
亚临界区间。它是**这个证明账本**的残余证据，不是实际余项的下界。
加大对数 cutoff 不能吸收一个正的固定幂。

## 6. 与 signed operator 的真实接口

现在可接受的结论是：

\[
 \boxed{\text{统一平滑模型假设}
       \Longrightarrow\text{修正后的临界 reciprocal-window 估计};
 \quad\text{完整 physical gate 尚未推出}.}
\tag{RP12}
\]

还必须补齐：

1. 从原 (4.5)/Type packet 到 (RP3) 的等式，逐一展开所有涉及 `n,c,h,δ`
   的 gcd、互素及 squarefree masks。不能把 `n` 相关掩码写成仅依赖
   `A,e,r,k,l` 的 outer 常数；也不能同时依赖 squarefree 支持又把
   对应 quotient 当无权整数。若用无约束 Type 重组，则要证明这些
   层确已重组，并允许其产生的全部 allocation 支持。
2. 对 (RP11) 未覆盖的箱，证明新的**联合加权除数平均**，或保留符号
   与完整 packet 重组得到更弱而足够的估计。逐个 reciprocal 模式的
   MRSTT 对数消去不能代替这项离散边界工作。
3. 将 `c=0`、Fourier 零轴、另一 AFE 方向与 reflected 交叉项接回
   [完整物理 adapter](2026-08-30-mwkf-physical-reflection-adapter.md)
   的 `R=H-L=Gχ+Jχ`。本文没有提供新的 canonical zero Gram 识别或
   稠密共同字符补集的加权范数 saving。

因此不采信候选稿的“完整无条件渐近式已证明”状态；也不把两个
must-fix 解释为路线不可能。当前新增的可用输入是修正后的临界引理、
有限边界公式和其明确覆盖区。配套脚本只验证这些坐标与计数；没有
Lean 化解析定理，没有关闭 `MWKF_ck(3)`。
