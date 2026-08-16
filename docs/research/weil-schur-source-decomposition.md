# Weil 矩阵的 Loewner–秩二分解与有限到无限瓶颈

## 1. 已从实现中确认的精确结构

CCM 路线不是一个不可解释的数值黑箱。令

\[
L(f)_{mn}=
\begin{cases}
\dfrac{f(m)-f(n)}{m-n},&m\ne n,\\[6pt]
f'(n),&m=n.
\end{cases}
\]

当前严格区间公式逐项给出

\[
Q=L(\alpha)+L(p_{\mathrm{prime}})
  +2cc^{\mathsf T}-2ss^{\mathsf T}.
\]

其中：

- `L(alpha)` 是阿基米德特殊函数项；
- `L(p_prime)` 是有限个素数幂产生的差商项；
- `2ccᵀ-2ssᵀ` 是极点项，秩至多为二；
- `-2ssᵀ` 是明确的负秩一方向，不能被忽略。

`weil_extremal_interval_ccm.py` 现在分别返回这三个严格 Arb 区间矩阵及其总和。分解没有假定任何一项正定。

## 2. 正确的候选归一化

第一候选参考算子取为

\[
A=L(\alpha).
\]

其余部分记为

\[
K=L(p_{\mathrm{prime}})+2cc^{\mathsf T}-2ss^{\mathsf T},
\qquad Q=A+K.
\]

只有在先证明 \(A\) 是稠密定义、闭、自伴且具有统一强制性

\[
\langle x,Ax\rangle\ge a\lVert x\rVert^2,\qquad a>0,
\]

之后，才允许定义

\[
\widetilde Q=A^{-1/2}QA^{-1/2}
 =I+A^{-1/2}KA^{-1/2}.
\]

因此“把对角元缩放到一”不是可接受的归一化；必须证明 \(A^{-1/2}\) 在目标 Hilbert 空间上存在并受控。

## 3. Schur 补闭合条件

对低频投影 \(P_M\) 与高频投影 \(R_M=I-P_M\)，写成

\[
\widetilde Q=
\begin{pmatrix}
Q_{00}&B\\
B^*&Q_{11}
\end{pmatrix}.
\]

若能严格证明

\[
Q_{00}\succeq \varepsilon_M I,\qquad
Q_{11}\succeq \gamma_M I,\qquad
\lVert B\rVert^2\le \beta_M^2,
\]

并且

\[
\varepsilon_M\gamma_M>\beta_M^2,
\]

则 Schur 补推出整个归一化算子严格正定。仓库中的 `FiniteToInfiniteSchur.lean` 已形式化这一传递器的抽象版本；缺口不在有限维线性代数，而在下面的统一解析估计。

## 4. 新诊断能证明什么

`weil_schur_source_decomposition.py` 对有限窗口

\[
[-N,N]=[-M,M]\cup\{M<|n|\le N\}
\]

执行以下严格计算：

- 对每个源项检查对称区间重叠；
- 检查三个源区间之和与总矩阵区间重叠；
- 用有理 Gershgorin 下界估计低频块和有限壳层块；
- 用 \(\lVert B\rVert^2\le\lVert B\rVert_1\lVert B\rVert_\infty\) 估计耦合；
- 生成确定性 JSON 与 SHA-256 指纹。

这只是有限壳层可行性诊断。即使它显示 `FINITE_SCHUR_STRICTLY_CLOSES`，也只证明所选有限窗口内的充分条件成立，不涉及所有 \(|n|>N\)。

## 5. 真正剩余的四个解析目标

要完成有限到无限桥，至少需要：

1. 证明 \(L(\alpha)\) 在选定加权 \(\ell^2\) 空间上的统一强制下界；
2. 控制素数差商项在无限高频壳层上的算子范数；
3. 控制秩二极点向量经过 \(A^{-1/2}\) 后的范数与低高频耦合；
4. 证明归一化余项的高频尾范数趋于零，并给出显式速率。

当前实现第一次把阻断点压缩到了这些具体对象。最关键、也最可能决定路线成败的是第 1 项：若 \(L(\alpha)\) 没有统一正下界，则必须更换参考算子或 Hilbert 空间权重，单纯扩大 \(N\) 不会解决问题。

## 6. 声明边界

当前成果是：

- 双路线区间装配与有限矩阵证书；
- 解析源项的严格区间分解；
- 可重放的有限壳层 Schur 可行性诊断；
- 抽象的 Lean Schur 传递框架。

当前没有证明：

- \(L(\alpha)\) 的无限维强制性；
- 无限尾误差趋于零；
- 无限维 Weil 判据；
- RH。
