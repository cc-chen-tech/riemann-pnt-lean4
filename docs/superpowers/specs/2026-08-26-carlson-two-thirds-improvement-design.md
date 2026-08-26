# Carlson 在 `sigma = 2/3` 处的指数改进：数学设计

## 1. 目标与证明状态

目标是区分并精确记录三种逻辑层级：

1. Carlson 原两端点框架内只改变 mollifier 长度；
2. 在 Carlson 检测器内引入新的 mollified large-values / 谱估计；
3. 直接换用 Ingham、Huxley 或其他零密度定理。

本设计只把第 2 类称为 Carlson 型改进。第 3 类仅作比较。Lean 中已经闭合的
代数、指数优化和条件装配，不得被描述为第 2 类解析输入本身的证明。

## 2. Carlson 原框架的精确 minimax

令 mollifier 长度为 `X = T^x`，并令 `1/2 < sigma < 1`。两端点指数为

\[
 E_L(\sigma,x)=1+x(1-2\sigma),\qquad
 E_U(\sigma,x)=(1+x)(2-2\sigma).
\]

两者之差是

\[
 E_L(\sigma,x)-E_U(\sigma,x)=2\sigma-1-x.
\]

因此：

- 当 `x <= 2 sigma - 1` 时，最大值是 `E_L`，且其最小可能值在右端取得；
- 当 `2 sigma - 1 <= x` 时，最大值是 `E_U`，且其最小可能值在左端取得。

故对所有实数 `x`，

\[
 \max(E_L,E_U)\ge 4\sigma(1-\sigma),
\]

且等号当且仅当 `x=2 sigma-1`。这给出狭义 no-go：凡证明只保留这两个
正能量端点上界、最后取其最大值的 Carlson 方法，单独重调长度不可能改善指数。

在 `sigma=2/3` 时：

\[
 E_L=1-x/3,\qquad E_U=2/3+2x/3,
\]

唯一最优长度为 `x=1/3`，最优最大值为 `8/9`。

## 3. 固定端点节省的通用公式

若解析输入真正把两端点改成

\[
 E_L-\delta_L,\qquad E_U-\delta_U,
\]

则新交点为

\[
 x_*=2\sigma-1-\delta_L+\delta_U.
\]

同样的分段线性论证给出唯一最优值

\[
 q_{\rm new}(\sigma)=4\sigma(1-\sigma)
 -2(1-\sigma)\delta_L-(2\sigma-1)\delta_U.
\]

特别地，在 `sigma=2/3`：

\[
 q_{\rm new}=\frac89-\frac23\delta_L-\frac13\delta_U.
\]

该公式只适用于对旧两条直线的固定节省。若新输入改变了整个插值几何，必须直接
计算新指数，不能事后把它假装成均匀端点节省。

## 4. 候选路线审计

### 4.1 两尺度 Selberg mollifier（主候选）

先纠正一个容易混淆的归一化：Deshouillers--Iwaniec / Conrey 的 `4/7`
结果不是仓库当前尖截断

\[
 M_Y(s)=\sum_{n\leq Y}\mu(n)n^{-s}
\]

的三项式均方界。已发表结果覆盖的是 Selberg 权
`mu(n) P(log(Y/n)/log Y)`；Conrey 的 Theorem 2 在 `P(u)=u`、`Q=1`
时给出长度 `Y=T^theta`, `theta<4/7` 的临界边界均方 `O(T)`。
来源：Conrey, *More than two fifths of the zeros of the Riemann zeta
function are on the critical line*, J. reine angew. Math. 399 (1989),
Theorem 2；其谱输入来自 Deshouillers--Iwaniec, *Power mean-values for
Dirichlet's polynomials and the Riemann zeta-function II*, Acta Arith. 43
(1984), 305--312。

为同时保留右边界的精确倒数消去，取两个尺度

\[
 a=57/100,\qquad b=571/1000,\qquad a<b<4/7,
\]

并定义

\[
 w_T(n)=\begin{cases}
 1,&n\le T^a,\\
 \dfrac{\log(T^b/n)}{(b-a)\log T},&T^a<n\le T^b,\\
 0,&n>T^b.
 \end{cases}
 \qquad
 M_T(s)=\sum_n\mu(n)w_T(n)n^{-s}.
\]

这是两个标准线性 Selberg mollifier 的精确线性组合：

\[
 M_T=\frac{b}{b-a}M_{T^b}^{\rm Sel}
      -\frac{a}{b-a}M_{T^a}^{\rm Sel}.
\]

故由 Conrey Theorem 2 分别控制两项，再用
`|u+v|^2 <= 2|u|^2+2|v|^2`，得到临界边界

\[
 \int_0^T|\zeta(1/2+it)M_T(1/2+it)|^2dt\ll_{a,b}T(\log T)^B.
\]

另一方面 `w_T(n)=1` 对所有 `n<=T^a`，所以 `zeta(s)M_T(s)-1`
的 Dirichlet 系数到 `T^a` 为止严格为零。正对角测试因此给出：临界边界
的 `T` 项不可消除，但远右边界仍有 `T^{a(1-R)}` 的幂次衰减；这不是
启发式 Möbius 消去。

### 4.2 L2 三线插值产生的显式指数

对 `F_T=zeta M_T-1` 使用 Gaussian/Hilbert-valued L2 三线定理。取

\[
 R=1000,\qquad \varepsilon=1/10000.
\]

在 `sigma=2/3` 的插值参数是

\[
 \lambda=\frac{2/3-1/2}{1000-1/2}=\frac1{5997}.
\]

保留 `T^epsilon` 后得到的实际指数为

\[
 q_*=1-\frac{18981}{99950}+\frac{1499}{14992500}
     =\frac{12146849}{14992500}.
\]

它严格小于

\[
 q_{\rm target}=\frac{467}{576}=\frac89-\frac5{64},
\]

且余量为

\[
 \frac{467}{576}-q_*=\frac{409373}{719640000}>0.
\]

极限右边界指数为 `1-a/3=81/100`，也严格小于 `467/576`，余量
`11/14400`。因此两尺度 Carlson 路线的目标纸面结论是

\[
 N(2/3,T)\ll T^{467/576}(\log T)^6.
\]

这是第 2 类 Carlson 型改进；它不是引用 Ingham 的 `3/4` 定理替换整个证明。
纸面归一化现已闭合：Conrey 原文 Theorem 2 的印刷条件允许 `R=0`，取
`Q=1,P(u)=u` 后 `sigma_0=1/2,V=zeta`；原文 (50) 对
`Delta=U^(1-eta)`、`U<=w<=2U` 一致。逐局部窗做 pole-free Hilbert-L2 三线，
再以 `O(U/Delta)` 个窗覆盖 dyadic 壳，窗口数与局部均方中的 `Delta` 正好相消。
完整推导见 `2026-08-27-carlson-two-scale-paper-proof.md`。因此纸面结论已是已发表
Conrey/DI 输入之上的无条件 Carlson 型定理；尚未闭合的是把这些解析步骤全部
翻译进 Lean，而不是数学上的未证明谱估计。

### 4.3 保留 Möbius 符号的 dispersion / Kuznetsov

已发表覆盖的是上面的 Selberg taper，经 Vaughan identity 后调用
Deshouillers--Iwaniec 的不完全 Kloosterman 和谱大筛；它处理非对角项，但不
消去正对角。它不直接覆盖仓库的尖截断权。更广的 `MWKF_ck(3)` 双 Möbius
Region-D 命题仍未证明，不能用它替代这里的两尺度分解。

### 4.4 局部高度窗口

使用 Conrey (50) 的规定宽度 `Delta=U^(1-eta)`，每个局部窗的临界边界均方
为 `O(Delta)`，覆盖 `[U,2U]` 需要 `O(U/Delta)` 个窗；两因子相消，最终仍是
长度 `U`。因此局部化本身不给额外幂次节省，也不造成 `U^eta` 损失。这里不能
用单个宽度 `U` 的 Gaussian 再只引用 `[0,U]` 全局均方，否则尾部没有被控制。

### 4.5 高阶矩 / large values

若命题仅给 `2k` 阶矩而没有适配本 detector 的 large-values 分布式估计，
Hölder 会同时改变阈值与测度因子，不能直接记作固定 `delta_U`。目前未找到
一个已发表命题可在保持尖核心消去的同时，单独给出可量化的额外
`delta_L` 或 `delta_U`；数值记为 `0`，保持开放。

### 4.6 只统计 forcing 特殊零点族

若要产生幂次改进，需证明一个只对 forcing 族成立、指数优于全体
`N(sigma,T)` 的已发表或独立定理。目前没有这样的无条件输入，因此保持开放。

### 4.7 候选路线账本

| 路线 | 精确输入/归一化 | 改善位置 | 幂次 | 对角/反例测试 | 已发表覆盖 |
|---|---|---|---|---|---|
| 仅重调尖截断长度 | 原 `E_L,E_U` | 无 | `delta_L=delta_U=0` | 两条正端点在 `x=1/3` 相交 | 完全覆盖，且已证 no-go |
| 单段 Selberg 权 | `mu(n)P(log(Y/n)/log Y)` | 临界均方 | 单独使用时为 `0` | 固定小 `n` 的权不等于 `1`，远右边界只剩对数衰减 | Conrey `theta<4/7` 覆盖临界均方，但不足以改幂次 |
| 两尺度 plateau/taper | 本节 `a=57/100,b=571/1000`；逐窗 Conrey (50) + pole-free Hilbert 三线 | 改变整个 L2 插值几何 | `delta=5/64` | 临界正对角保留 `Delta`；核心以下卷积系数严格为零 | Conrey/DI 已发表；纸面归一化与 Carlson 装配已闭合，Lean 解析翻译待完成 |
| 高阶矩/large values | 需给 detector 的分布式 `2k` 阶命题 | 未定 | 当前 `0` | 仅 Hölder 不产生所需固定节省 | 未找到直接覆盖 |
| 尖截断 Möbius dispersion | 需直接控制当前 sharp 权的非对角 | 上端/临界均方 | 当前 `0` | 正对角不可消；必须从非对角取得节省 | DI/Conrey 不直接覆盖 sharp 权 |
| 局部高度窗口 | Conrey (50), `Delta=U^(1-eta)` | 无损传递局部均方 | `0` | `O(U/Delta)` 个窗与每窗 `Delta` 相消 | Conrey 原文一致局部式覆盖 |
| forcing 特殊零族 | 需特殊族计数定理 | 终端 density | 当前 `0` | 必须验证该族确实小于全部零点 | 未找到已发表覆盖 |

这里两尺度路线不能代入第 3 节的固定端点节省公式：它让“外层长度控制临界
均方、核心长度控制右边界衰减”，从而改变了两条旧直线本身。直接插值计算才是
合法的指数账本。

## 5. `14/17` 链的影响

令 forcing 内部仍使用 `q_F=8/9`，density 使用
`q_D=467/576=8/9-5/64`。一般单层矛盾的幂次差为

\[
 2\lambda(\beta-\sigma)-\lambda(1-\beta)(q_F+q_D).
\]

在 `sigma=2/3`, `beta=14/17` 处，新余量为

\[
 \frac{3}{17}\cdot\frac5{64}=\frac{15}{1088}.
\]

等价阈值是

\[
 \beta>\frac{4/3+q_F+q_D}{2+q_F+q_D}
       =\frac{1747}{2131}.
\]

因此直接进入总指数的额外 forcing 损失必须小于 `15/1088`；若损失写成
`(1-beta) epsilon_F`，则需 `epsilon_F<5/64`。现有 `MWKF/QCT` 的参数接口并未
自动给出这个定量损失，仍需单独桥接。

## 6. Lean 边界

本分支先无条件形式化：

- 两端点 minimax 与唯一性；
- 带 `delta_L, delta_U` 的通用优化公式；
- `sigma=2/3` 的所有精确有理数计算；
- 分离 `q_F` 与 `q_D` 的 single-layer contradiction；
- 从一个实际 density certificate 到 `14/17` 排除链的条件装配。

Lean 中的无条件改进零密度 theorem 只有在以下已闭合纸面步骤全部形式化后才
允许出现：

1. 两尺度 Selberg mollifier 的 Conrey/DI 归一化 certificate；
2. Gaussian/windowed L2 三线传递；
3. Carlson/Titchmarsh 局部零点计数到 dyadic/global `N(2/3,T)`；
4. 对数损失吸收为显式 `B`（目标取 `B=6`）。

这些门不得用 `axiom`、`sorry` 或承载数学内容的 typeclass instance 绕过。
