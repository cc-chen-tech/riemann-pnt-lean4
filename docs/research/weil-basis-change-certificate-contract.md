# Weil 有限矩阵的基变换证书合同

## 目标

数值或 LDL 证书中的矩阵必须与论文声明中的 Fourier/Galerkin 矩阵通过一个精确、可重放的合同变换联系起来。仅说明“两个矩阵数值上相似”不构成数学桥。

设原坐标矩阵为 \(A\in\mathbb R^{n\times n}\)，基嵌入为
\(B\in\mathbb R^{n\times m}\)。目标矩阵必须定义为

\[
A_B=B^{\mathsf T}AB.
\]

Lean 模块 `WeilExtremalKernels/BasisChangeTransfer.lean` 证明

\[
q_{A_B}(x)=q_A(Bx).
\]

## 必须进入 artifact 的字段

- `schema_version`
- `source_matrix_sha256`
- `target_matrix_sha256`
- `rows`
- `columns`
- `source_index_convention`
- `target_index_convention`
- `basis_matrix_entries`，全部为精确有理数
- `basis_matrix_sha256`
- `congruence_identity_sha256`
- `left_inverse_entries`，严格正定传递时必需
- `left_inverse_sha256`
- `generator`
- `generator_sha256`

解析时不得先经过 binary floating point。

## 三种不同结论

### 任意矩形 \(B\)

如果 \(A\succeq0\)，则

\[
B^{\mathsf T}AB\succeq0.
\]

这只给出从 full matrix 到子空间或 even sector 的单向结论。

### 有左逆的矩形 \(B\)

若存在精确矩阵 \(C\) 满足

\[
CB=I_m,
\]

则 \(B\) 的核为零。此时 \(A\succ0\) 可推出

\[
B^{\mathsf T}AB\succ0.
\]

### 可逆方阵 \(B\)

只有同时提供两个方向的精确逆关系，才能把正定性或半正定性写成坐标无关的等价命题。不能从 even-sector 的正定反推 full matrix 正定。

## 与阿基米德尾的连接

若 cutoff-free 矩阵写成

\[
Q=A+H,\qquad H\succeq0,
\]

则

\[
B^{\mathsf T}QB
 =B^{\mathsf T}AB+B^{\mathsf T}HB,
\qquad
B^{\mathsf T}HB\succeq0.
\]

因此现有完整阿基米德尾定理可以在精确基变换后继续使用。这里不产生额外的“基变换误差”；只有当实际 artifact 使用近似 \(B\) 时，才需要单独的区间误差预算。

## 当前未完成实例

现在完成的是通用 Lean 传递器，不是具体 Weil 基变换。下一实例必须给出：

1. Groskin 有限字典中的注册 Fourier 基；
2. 证书矩阵实际使用的基和缩放；
3. 两者之间逐项精确的 \(B\)；
4. full/even 情形各自的维数和索引顺序；
5. 需要严格正定传递时的精确左逆。

这五项全部闭合后，才可以说 `c=13,N=200` 的有限 LDL 证书已经与注册数学矩阵完成基变换绑定。

## Full 坐标审计结论

对当前 full-matrix 装配链，具体坐标桥已经确定为恒等矩阵：

- Python 装配器强制 `index_order = [-N, ..., N]`；
- artifact 第 `i` 行对应整数 `-N+i`；
- Lean 的 `centeredIndexCoordinate N i` 定义为 `i.val-N`；
- 两者没有额外缩放、置换或 even-sector 收缩。

`WeilExtremalKernels/WeilCoordinateBridge.lean` 给出逐项坐标等式、恒等
基矩阵、自身左逆以及合同后矩阵不变的定理。

`experiments/rh/weil_identity_basis_certificate.py` 从一个 canonical source
manifest 生成确定性的稀疏恒等矩阵 artifact，并绑定：

- source 文件 SHA-256；
- source payload SHA-256；
- `c,N,dimension,index_order`；
- 恒等基矩阵及左逆的 SHA-256；
- source/target 坐标约定。

这关闭的是 full artifact 到 Lean finite-tail 坐标的身份绑定。它尚未：

- 将现场 `/tmp` 中的 `c=13,N=200` manifest 固化进仓库；
- 验证 full-to-even 的矩形嵌入；
- 建立所有 \(N\) 的无限维极限。
