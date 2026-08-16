# Weil source-function 主路线

## 主对象

论文的有限 Guinand--Weil dictionary 对每一类来源给出一个标量函数
\(\psi(x)\)。对应矩阵不是额外定义，而是其 Loewner 差商：

\[
Q_\psi(m,n)=
\begin{cases}
\dfrac{\psi(m)-\psi(n)}{m-n},&m\ne n,\\[6pt]
\psi'(n),&m=n.
\end{cases}
\]

`WeilSourceKernel.lean` 将一类来源表示为：

```lean
structure WeilSourceData where
  value : Int -> Real
  derivative : Int -> Real
```

全局有限 dictionary 核定义为 prime、pole、archimedean 三类 source
data 的和。

## 为什么这比选择某条闭式作为主定义更稳健

辅助 S/CC/XC 公式和 CCM hypergeometric/Lerch 公式都是同一 source
kernel 的计算表示。它们的作用是：

- 独立计算同一个有限矩阵；
- 通过严格区间 overlap 排除实现错误；
- 产生 proof-carrying LDL 证书。

无限维对象则直接由 source function 和 Weil 显式公式定义，不需要把
某个数值闭式提升为无限维定义。

## 已形式化结论

`WeilSourceKernel.lean` 已给出：

- source data 的 Loewner kernel；
- source 加法与 kernel 加法的一致性；
- prime、pole、archimedean 三源分解；
- 所有 cutoff 的 exact centered nesting；
- 一个 cutoff 的正性向所有较小 cutoff 传递；
- pole source 与 CCM rank-two 表示兼容时的全局核等式；
- source kernel 与 CCM 的所有有限 cutoff 等式；
- “所有 source cutoff 正定”到连续无限二次型的抽象传递入口。

## Pole source 已具体化

`WeilPoleSource.lean` 已定义论文的有理 source

\[
\psi_0(n)=C\frac{n}{n^2+\beta^2},
\qquad
\psi_0'(n)=
C\frac{\beta^2-n^2}{(n^2+\beta^2)^2},
\]

并精确证明其 Loewner 核为

\[
Q_{\mathrm{pole}}(m,n)=
C\frac{\beta^2-mn}
{(m^2+\beta^2)(n^2+\beta^2)}.
\]

取

\[
\beta=\frac{L}{4\pi},
\qquad
C=\frac{2L\sinh^2(L/4)}{\pi^2},
\]

Lean 进一步把该矩阵识别为：

- auxiliary 路线的展开有理 pole 公式；
- CCM 路线的两个归一化向量组成的 rank-two 公式。

因此 `PoleSourceCompatible` 对论文的具体参数已有构造，不再是抽象
假设。

## Prime source 已具体化

`WeilPrimeSource.lean` 将固定 cutoff 下有限多个素数幂的 value 与
derivative 数据包装为 `finitePrimeSourceData`，并证明：

\[
K_{\mathrm{source,prime}}(m,n)
=K_{\mathrm{aux,prime}}(m,n)
\]

对所有整数 \(m,n\) 成立。对应的每个 finite cutoff 也逐项相等，并
自动满足 exact centered nesting。

这一步结合 `WeilPrimeLoewner.lean` 的整数相位周期恒等式，因此不是
数值近似，也不依赖 Arb overlap。

## Archimedean source 已定义

`WeilArchimedeanSource.lean` 直接按论文定义

\[
S(r,x,L)=
\int_0^L
\sin\left(2\pi x\left(1-\frac yL\right)\right)
\cos(ry)\,dy
\]

及

\[
\psi_{R,T}(x)=
\frac1{2\pi^2}
\int_{-T}^T h_+(r)S(r,x,L)\,dr.
\]

同时定义了对 \(x\) 微分后的 cosine integrand，并将整数节点上的
value/derivative 包装为 `finiteArchimedeanSourceData`。由此：

- 每个固定 \(L,T\) 得到一个全局整数 source kernel；
- 所有 centered cutoff 自动 exact nesting；
- \(T_1,T_2\) 之间的 source increment 已定义；
- source increment kernel 等于两个 finite-\(T\) kernel 的差。

不再需要把 CCM hypergeometric/Lerch 表达式作为无限对象的定义。

最后尚需证明的兼容命题已经命名为
`ArchimedeanSourceIncrementCompatible`：

\[
Q_{\psi_{R,T_2}-\psi_{R,T_1}}
=
Q_{\mathrm{rank\text{-}two},[T_1,T_2]}.
\]

证明它需要严格完成积分下微分以及论文中的整数节点 sine-chord
闭式。完成后，现有 actual-tail 非负性和 \(B_T\) 上界将直接传递到
source kernel。

## Archimedean 的二维代数也已完成

`WeilArchimedeanSourceAlgebra.lean` 对一般参数证明：

\[
f(x)=A\frac{x}{a^2-x^2}
\]

的 Loewner 核满足

\[
L(f,f')(m,n)
=\frac A2\left[
\frac1{(a-m)(a-n)}
+\frac1{(a+m)(a+n)}
\right].
\]

证明同时覆盖：

- \(m\ne n\) 的差商；
- \(m=n\) 的真实导数；
- 两侧所有分母的非零条件。

取 \(a=T/\rho\) 且 \(A=2w(T)\)，右侧就是现有
`paperArchimedeanRankTwoDensity` 使用的两个 Cauchy 向量。因此
archimedean 兼容性中已经不再有二维矩阵代数，剩余仅为一维积分
计算：

\[
S(T,n,L)=
\frac{2\sin^2(LT/2)}{\rho}
\frac{n}{(T/\rho)^2-n^2},
\]

以及对 \(x\) 微分后的整数节点公式。

## 计算路线与解析路线的职责

计算路线：

\[
\text{auxiliary intervals}
\cap
\text{CCM intervals}
\longrightarrow
\text{exact LDL certificate}.
\]

解析路线：

\[
\text{source functions}
\longrightarrow
\text{one global integer kernel}
\longrightarrow
\text{all centered sections}
\longrightarrow
\text{dense infinite space}.
\]

两者在固定 cutoff 上必须严格一致，但不能用有限 overlap 代替
“所有 cutoff 正定”。

## 尚未闭合的接口

1. 证明 sine-chord 的两个整数节点闭式并完成积分下微分，由此解除
   `ArchimedeanSourceIncrementCompatible`；
2. 将现有 actual archimedean improper-tail 极限识别为
   archimedean source cutoff 的 cutoff-free 尾增量；
3. 对 \(N>200\) 建立统一正性、截断误差，或 Schur coupling 估计；
4. 构造目标 Weil 函数空间、稠密嵌入和连续性证明。

当前 \(c=13,N=200\) 证书完成的是固定 cutoff 的计算层，不是以上
第 3、4 项。
