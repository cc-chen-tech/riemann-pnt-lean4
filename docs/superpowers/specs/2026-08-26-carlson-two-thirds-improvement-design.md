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

### 4.1 平滑、多段或变分 mollifier

精确命题需求是：在保持检测器归一化 `M_X(s)` 的常数项为 `1`、并保留零点
检测恒等式的前提下，证明某一端点二次型获得 `T^{-delta}` 的一致节省。
仅优化对角常数或对数次幂不能给出 `delta>0`。正对角是非负且不能靠符号消去。

结论：目前没有覆盖本归一化并给出固定幂次节省的已发表输入；只属候选，不是定理。

### 4.2 高阶矩 / large values

Deshouillers--Iwaniec, *Power mean values of the Riemann zeta-function II*,
Publ. Math. Debrecen / Acta Arith. 48 (1984) 的 Theorem 4（以原文归一化复核）给出
sharp Möbius mollifier 的二次均值型界

\[
 \int_0^T |\zeta(1/2+it)M_X(1/2+it)|^2\,dt
 \ll_\varepsilon T^\varepsilon
 \left(T+T^{1/2}X^{7/8}+X^{5/3}\right).
\]

原文 PDF：
<https://www.impan.pl/shop/en/publication/transaction/download/product/104164>。

取

\[
 x=57/100,\quad R=1000,\quad \varepsilon=1/10000.
\]

则

\[
 \tfrac12+\tfrac78x=799/800<1,\qquad \tfrac53x=19/20<1.
\]

用 Titchmarsh--Heath-Brown §9.16 的 Carlson 检测器
`F=zeta M-1`, `h=1-F^2`、右边界衰减和三线插值，插值参数是

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

固定 `x=57/100` 的旧下端点为 `81/100`，也严格小于 `467/576`，余量
`11/14400`。因此目标纸面结论是

\[
 N(2/3,T)\ll T^{467/576}(\log T)^6.
\]

这是第 2 类 Carlson 型改进；它不是引用 Ingham 的 `3/4` 定理替换整个证明。
但是无条件 Lean 定理仍要求把 DI Theorem 4 及 Titchmarsh §9.16 的局部到全局
装配形式化出来。

### 4.3 保留 Möbius 符号的 dispersion / Kuznetsov

DI Theorem 4 正是已发表的此类谱输入在当前临界均值问题上的覆盖。它改善的是
临界线 mollified mean square 及随后插值得到的 Carlson 上端结构，而不是消去
正对角。更广的 `MWKF_ck(3)` 双 Möbius Region-D 命题仍未证明，不能用它替代 DI。

### 4.4 局部高度窗口

取 Gaussian 窗口宽度 `Delta=U/log U`，用 `O(log U)` 个窗口覆盖 `[U,2U]`。
局部化只产生对数损失；它本身没有 `T^{-delta}`，但可使 L2 三线论证合法并避免
粗糙的水平边界逐点上界。

### 4.5 只统计 forcing 特殊零点族

若要产生幂次改进，需证明一个只对 forcing 族成立、指数优于全体
`N(sigma,T)` 的已发表或独立定理。目前没有这样的无条件输入，因此保持开放。

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

无条件改进零密度 theorem 只有在以下解析门全部构造后才允许出现：

1. DI mollified mean-square certificate；
2. Gaussian/windowed L2 三线传递；
3. Carlson/Titchmarsh 局部零点计数到 dyadic/global `N(2/3,T)`；
4. 对数损失吸收为显式 `B`（目标取 `B=6`）。

这些门不得用 `axiom`、`sorry` 或承载数学内容的 typeclass instance 绕过。
