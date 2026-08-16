# Weil 有限到无限的精确门槛

## 已形式化的两条合法路线

`WeilFiniteToInfiniteGate.lean` 给出两种不会越界的有限到无限定理。

### 路线一：所有 centered cutoff

若对同一个全局整数核 \(K(m,n)\)，每个

\[
K_N=K|_{\{-N,\ldots,N\}^2}
\]

都半正定，并且有限支撑坐标在目标空间中稠密、目标二次型连续，则
无限二次型半正定。

若进一步存在与 \(N\) 无关的 \(\varepsilon>0\)，使

\[
\varepsilon\lVert x\rVert^2
\leq \langle x,K_Nx\rangle
\]

对所有 \(N\) 成立，则同一强制性下界传递到无限空间。

Lean 入口：

- `infinite_nonneg_of_all_centered_cutoffs`;
- `infinite_coercive_of_uniform_centered_cutoffs`.

### 路线二：一个近似算子加严格误差界

若某个有限或可计算近似 \(Q_N\) 满足

\[
\varepsilon_N\lVert x\rVert^2
\leq Q_N(x)
\]

且目标二次型满足

\[
|Q(x)-Q_N(x)|
\leq\delta_N\lVert x\rVert^2,
\]

那么

\[
\delta_N\leq\varepsilon_N
\]

推出 \(Q(x)\geq0\)。若
\(\delta_N<\varepsilon_N\)，并且非零向量的范数严格为正，则推出严格
正性。

Lean 入口：

- `nonneg_of_coercive_approximation_and_error`;
- `pos_of_coercive_approximation_and_strict_error`;
- `nonneg_of_exists_finite_section_margin`.

## 当前 \(c=13,N=200\) 证书能提供什么

当前证书提供一个固定的 \(401\times401\) 矩阵严格正定结论。全局核的
centered nesting 自动给出 \(N\leq200\) 的所有较小截面正定。

它不能提供：

- \(N>200\) 的正定性；
- 与 \(N\) 无关的统一强制性常数；
- 从 \(N=200\) 截断到目标无限二次型的算子误差 \(\delta_{200}\)；
- \(\delta_{200}<\varepsilon_{200}\)。

LDL 主元下界也不能直接当作标准欧氏范数下的最小特征值下界；必须
连同三角因子的逆范数或等价的基条件数一起转换。现有
`IntervalLDLCoercivity` 层正是完成这一转换的位置。

## 现在真正需要证明的数学命题

要让有限结果推进到无限 Weil 判据，至少完成以下之一：

1. 对所有 \(N\) 证明同一全局 source kernel 的 centered cutoff
   半正定；
2. 构造归一化近似 \(Q_N\)，给出可求值的
   \(\varepsilon_N,\delta_N\)，并在某个 \(N\) 严格验证
   \(\delta_N<\varepsilon_N\)；
3. 找到 Schur 补或尾块结构，使 \(N>200\) 的新增自由度由一个统一
   正尾和可控耦合支配。

第 3 条若可实现，最接近新的有限到无限数学理论。它需要新的解析
估计，不能由增加 Arb 精度或重复 LDL 自动得到。

## Schur 尾块框架已经形式化

`WeilSchurTailGate.lean` 将扩大的截面写成

\[
Q_{\mathrm{big}}(x,y)
=Q_{\mathrm{core}}(x)
+2B(x,y)
+Q_{\mathrm{tail}}(y).
\]

设核心和尾块分别有强制性预算

\[
Q_{\mathrm{core}}(x)
\geq(\eta_c+r_c)\lVert x\rVert^2,
\qquad
Q_{\mathrm{tail}}(y)
\geq(\eta_t+r_t)\lVert y\rVert^2,
\]

并且耦合满足

\[
2|B(x,y)|
\leq
\eta_c\lVert x\rVert^2+
\eta_t\lVert y\rVert^2.
\]

那么 Lean 已证明

\[
Q_{\mathrm{big}}(x,y)
\geq
r_c\lVert x\rVert^2+
r_t\lVert y\rVert^2.
\]

因此：

- \(r_c,r_t\geq0\) 给出扩大截面的半正定性；
- \(r_c,r_t>0\) 给出非零向量上的严格正定性；
- 核心证书的强制性可以明确拆成“吸收 coupling 的花费”和“保留下来
  的余量”。

对应 Lean 入口：

- `blockQuadraticForm_nonneg_of_schur_budget`;
- `blockQuadraticForm_ge_reserve_of_schur_budget`;
- `blockQuadraticForm_pos_of_schur_reserve`;
- `certified_core_extends_through_schur_tail`.

对 \(N=200\) 之后的 Weil 截面，真正需要的新解析估计现在被压缩为：

1. 新增高频尾块的统一下界；
2. 核心与新增频率之间的 coupling 上界；
3. 两个上界消耗量严格小于已有核心强制性和尾块强制性。

这三项若能对所有后续频率统一成立，就能迭代越过 \(N=200\)；单纯计算
更大的 LDL 只能提供更多有限样本，不能替代这些统一估计。

## 声明边界

这些 Lean 定理证明了“什么条件足以完成有限到无限传递”，并没有
证明这些条件已经对 Weil 核成立。因此当前结论仍是有限证书方法与
精确研究门槛，不是 RH 证明。
