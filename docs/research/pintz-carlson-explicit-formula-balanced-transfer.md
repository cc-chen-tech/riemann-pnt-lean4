# Pintz-Carlson-explicit-formula balanced transfer: audited theorem chain

This note records the exact formal boundary of the actual-zeta balanced
transfer chain on `feat/explicit-formula-unified-next`. It is a theorem-chain
audit, not an RH claim and not an unconditional oscillation claim.

## 1. Common PNT object

All final transfers act on the same genuine relative Chebyshev error:

```lean
relativeChebyshevPsi0Error
```

The finite visible main term is:

```lean
dynamicVisibleClusterPNTMain
```

The common decomposition has the form

```text
actual relative PNT error
  = visible finite zero cluster
  + signed outside-cluster zero complement
  + real-axis term
  + selected-height contour remainder.
```

The zero contributions use the actual zeta kernel and analytic multiplicity.
Carlson density controls the aggregated outside-cluster positive-zero tail.
Conjugation transfers that control to the complete nonreal zero sum. The
real-ordinate term remains explicit and is not silently discarded.

## 2. Dynamic Carlson residual theorem

The automatic canonical two-strip theorem is:

```lean
selectedUniformGoodHeightActualCarlsonCanonicalTwoStripPNTClusterResidual_automatic
```

It removes the earlier abstract bucket input and the manually supplied
positive norm lower bound. The low strip is the canonical predicate
`rho.re <= sigma`; the high strip is treated by the actual Carlson dyadic
tail.

The balanced specialization is:

```lean
selectedUniformGoodHeightActualCarlsonBalancedPNTClusterResidual_automatic
```

Its conclusion is:

```text
relativeChebyshevPsi0Error - dynamicVisibleClusterPNTMain
  = o(targetZeroPowerAmplitude beta)
```

along natural points, where the selected polynomial height exponent is

```text
alpha = (1 - sigma) / 2.
```

## 3. Exact truncation-height certificate

The contour and low-strip powers require the strict window

```text
1 - beta < alpha < beta - sigma.
```

The formal exact feasibility theorem is:

```lean
actualCarlsonHeightWindow_nonempty_iff
```

It proves:

```text
(exists alpha, 1 - beta < alpha and alpha < beta - sigma)
  iff
(1 + sigma) / 2 < beta.
```

The robust margin is:

```text
min (alpha - (1 - beta)) ((beta - sigma) - alpha).
```

The midpoint is the unique optimizer. The quantitative stability identity is:

```lean
actualCarlsonHeightRobustMargin_eq_balanced_sub_abs
```

which proves:

```text
robustMargin(beta, sigma, alpha)
  = (2 * beta - 1 - sigma) / 2
      - abs(alpha - (1 - sigma) / 2).
```

Thus moving the truncation exponent by `d` loses exactly `abs d` from the
minimum power margin.

## 4. Boundary-mass extension

The positive-exponent moving-gap route does not justify letting a pointwise
real-part gap shrink to zero: density growth and contour admissibility force a
fixed exponent gap in that aggregation scheme. This obstruction is isolated in

```text
ZeroDensityLayerBudgetMovingGapBarrier.lean
```

The replacement is a summable actual-kernel argument. For high-strip zeros
outside `S` satisfying only

```text
Re rho <= beta,
```

the normalized weighted tail converges to the exact nondecaying mass on the
boundary `Re rho = beta`:

```lean
actualCarlsonOutsideClusterBoundaryMass

actualCarlsonOutsideClusterNormalizedKernelTail_tendsto_boundaryMass
```

Strict pointwise separation remains available as the zero-boundary-mass special
case:

```lean
actualCarlsonOutsideClusterBoundaryMass_eq_zero_of_lt
```

After the conjugate negative-ordinate zeros are restored, the complete nonreal
zero contribution has coefficient `2 * boundaryMass`. The generic actual-PNT
transfer is:

```lean
eventually_abs_actualCarlsonSelectedHeightPNTClusterResidual_lt_boundaryCoefficient_mul_targetAmplitude
```

The canonical balanced specialization is:

```lean
eventually_abs_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTClusterResidual_lt_automatic
```

It proves, for every `delta > 0`,

```text
abs(actual PNT error - visible cluster)
  < (2 * boundaryMass + delta) * targetZeroPowerAmplitude beta
```

eventually along natural points. The balanced exponent, canonical two-strip
input, uniform zero-kernel norm lower bound, and selected-height contour
certificate are all constructed internally.

## 5. Forward upper and lower transfers

### Empty cluster: zero gap to PNT upper bound

```lean
selectedUniformGoodHeightActualCarlsonBalancedPNTUpperTransfer_automatic
```

With `S = empty`, a global strict real-part gap gives:

```text
relativeChebyshevPsi0Error = o(targetZeroPowerAmplitude beta)
```

along natural points.

This theorem does not derive the strict zero gap from Carlson density. The gap
is an explicit input.

### Finite cluster: conditional unsigned lower transfer

```lean
selectedUniformGoodHeightActualCarlsonBalancedPNTLowerTransfer_automatic
```

An external far-point witness for the visible finite cluster survives in the
actual PNT error with the standard factor `1 / 2` used to absorb the
target-negligible complement.

### Finite cluster: conditional signed lower transfer

```lean
selectedUniformGoodHeightActualCarlsonBalancedPNTSharpSignedTransfer_automatic
```

External positive and negative visible-cluster witnesses with coefficient
`c` transfer to actual PNT witnesses with every coefficient `q` satisfying

```text
0 <= q < c.
```

Neither lower theorem constructs the finite-cluster witness. In particular,
the local pi/2 anti-cancellation theorem belongs to the separate sharp
oscillation task.

### Boundary zeros: exact net cluster coefficient

The unsigned boundary-mass transfer is:

```lean
selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTHasFarNaturalPoint_belowNetClusterConstant
```

If the visible cluster has an external witness with coefficient `c`, then every
nonnegative coefficient

```text
q < c - 2 * boundaryMass
```

survives in the actual PNT error. The proof chooses

```text
delta = c - q - 2 * boundaryMass,
```

so the actual residual bound is exactly `(c - q) * A_beta`; there is no
artificial factor `1 / 2`.

The signed version is:

```lean
selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpSignedTransfer_automatic
```

It transfers external positive and negative cluster witnesses throughout the
same strict net range `q < c - 2 * boundaryMass`.

The exact nontriviality criterion is formalized as:

```lean
exists_pos_lt_cluster_sub_two_mul_boundary_iff
```

It proves:

```text
(exists q > 0, q < c - 2 * boundaryMass)
  iff
2 * boundaryMass < c.
```

Consequently the following theorems automatically produce some common positive
coefficient on the actual PNT target scale:

```lean
exists_pos_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTHasFarNaturalPoint

exists_pos_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpSignedWitnesses
```

The second conclusion is conditional `Omega_+-style` data along natural points:
it still requires the external positive and negative visible-cluster witnesses,
but no longer requires the caller to guess a transferable coefficient.

The real-variable target-scale interfaces are:

```lean
HasFarPositiveTargetAmplitudeWitness

HasFarNegativeTargetAmplitudeWitness

HasFarSignedTargetAmplitudeWitnesses
```

Natural-point signed witnesses embed into these interfaces, so the final
conditional conclusions act directly on
`relativeChebyshevPsi0Error : Real -> Real`:

```lean
exists_pos_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTHasFarRealPoint

exists_pos_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpSignedRealWitnesses
```

Under `2 * boundaryMass < c`, the first produces an unsigned real-variable
target-scale witness with some coefficient `q > 0`; the second produces one
common `q > 0` with arbitrarily far positive and negative real witnesses. These
are transfer theorems, not unconditional `Omega` or `Omega_+-` theorems, because
their visible-cluster witness hypotheses remain external.

This quantifies why a single zero or an arbitrary finite cluster is not enough
by itself. Finiteness supplies neither an unsigned nor a signed witness
coefficient `c`, and even a supplied coefficient yields a nontrivial actual-PNT
conclusion only when it exceeds the boundary loss `2 * boundaryMass`.

### Capturing the complete boundary layer

The boundary coefficient is antitone in the visible cluster:

```lean
actualCarlsonOutsideClusterBoundaryMass_antitone
```

Thus enlarging `S` cannot worsen the complementary-zero loss. If `S` contains
every indexed positive zero with `Re rho = beta`, then:

```lean
actualCarlsonOutsideClusterBoundaryMass_eq_zero_of_boundary_captured
```

proves that the loss vanishes exactly. The balanced residual then becomes
arbitrarily small on the target scale:

```lean
eventually_abs_selectedUniformGoodHeightActualCarlsonBalancedBoundaryCapturedPNTClusterResidual_lt_automatic
```

and the unsigned and signed transfers recover the full strict range `q < c`:

```lean
selectedUniformGoodHeightActualCarlsonBalancedBoundaryCapturedPNTHasFarNaturalPoint_belowClusterConstant

selectedUniformGoodHeightActualCarlsonBalancedBoundaryCapturedPNTSharpSignedTransfer_automatic
```

This is weaker than assuming every outside zero satisfies `Re rho < beta` at
the interface level: outside zeros are only bounded by `beta`, while the entire
equality layer is assigned explicitly to the finite main cluster. It still does
not construct the required cluster witness.

## 6. Quantitative reverse transfers

The two-sided reverse theorem is:

```lean
selectedUniformGoodHeightActualCarlsonBalancedPNTEventualUpper_forces_emptyCluster_automatic
```

If the actual PNT error is eventually bounded by `q A_beta`, while any
nonempty visible cluster would have a `c A_beta` far-point witness and
`q < c`, then the cluster is empty.

The one-sided versions are:

```lean
selectedUniformGoodHeightActualCarlsonBalancedPNTEventualUpper_forces_emptyCluster_of_positiveWitness_automatic

selectedUniformGoodHeightActualCarlsonBalancedPNTEventualLower_forces_emptyCluster_of_negativeWitness_automatic
```

They require only the corresponding one-sided PNT bound and signed cluster
witness.

The boundary-mass branch has the parallel declarations:

```lean
selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTEventualUpper_forces_emptyCluster_automatic

selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTEventualUpper_forces_emptyCluster_of_positiveWitness_automatic

selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTEventualLower_forces_emptyCluster_of_negativeWitness_automatic
```

Here the sharp comparison hypothesis is no longer `q < c`, but

```text
q < c - 2 * boundaryMass.
```

Thus the same explicit boundary coefficient governs forward unsigned transfer,
forward signed transfer, two-sided reverse exclusion, and one-sided reverse
exclusion.

These reverse theorems do not imply RH. They are conditional exclusion
principles with explicit zero-gap and cluster-witness inputs.

## 7. Remaining mathematical hypotheses

The actual Carlson-explicit-formula residual machinery is internalized, but
the following assumptions remain external:

1. `S` is a finite conjugation-invariant cluster.
2. On the boundary-mass branch, every actual positive zero outside `S` and to
   the right of the Carlson low strip has real part at most `beta`; equality is
   retained quantitatively in `actualCarlsonOutsideClusterBoundaryMass`.
3. Every real-ordinate nontrivial zero outside `S` has real part strictly
   below `beta`.
4. For lower or reverse oscillation conclusions, the visible cluster supplies
   the required unsigned or signed far-point witness.
5. Balanced feasibility requires `(1 + sigma) / 2 < beta`.

Assumptions 2 and 4 are the main density/oscillation boundary. Carlson density
bounds the summable kernel mass and exposes the exact boundary coefficient; it
does not by itself produce a positive cluster witness or prove that its
coefficient dominates twice that boundary mass.

If another zero has the same real part as the target and is not in `S`, it is
not silently treated as target-negligible. It contributes to the audited
boundary mass. It may instead be included in the visible cluster if the
separate oscillation theorem supplies a witness for the enlarged cluster.

No abstract exceptional-zero reproduction tree is introduced here. The next
mathematical bridge remains the separate local finite-cluster oscillation
theorem supplying `hmain`, `hmainPos`, or `hmainNeg`.

## 8. Validation boundary

Each module in this chain has:

1. a focused `lake -Kjobs=1 build`;
2. a contract file checking the exported declarations;
3. a focused axiom audit.

The audited declarations report only:

```text
[propext, Classical.choice, Quot.sound]
```

No Guth-Maynard theorem, zero-reproduction tree, unconditional Omega theorem,
or RH theorem is asserted by this chain.

## 未归一化 PNT 误差的目标尺度转移

`ZeroDensityLayerBudgetPNTUnnormalizedTargetAmplitudeTransfer.lean` 现在把真实相对误差见证

\[
q x^{\beta-1}\leq \left|\frac{\psi_0(x)-x}{x}\right|
\]

在任意远的正实数取样点上无损转成

\[
q x^\beta\leq |\psi_0(x)-x|.
\]

形式化证明显式使用
`chebyshevPsi0Error x = x * relativeChebyshevPsi0Error x` 与
`x * targetZeroPowerAmplitude beta x = x ^ beta`，因此不会在归一化转换时损失常数 `q`。同一模块同时覆盖无符号、正向、负向和双向见证。

`ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTUnnormalizedOscillation.lean`
进一步把 balanced Carlson boundary transfer 专门化到真实对象
`chebyshevPsi0Error x = chebyshevPsi0 x - x`。在

\[
2\,B_{\partial}(\beta,S)<c
\]

以及外部可见主簇见证成立时，它给出某个 `q > 0`，使任意远实点上保留
`q * x ^ beta` 级无符号振荡；正、负主簇见证同时成立时，则给出同一个正 `q` 的双向振荡证书。

这里的 `q` 可以继承外部显式公式主项中已经编码的解析重数和
`1 / |rho|` 系数，但 `hmain`、`hmainPos`、`hmainNeg` 仍是外部输入。
所以当前结论是经过审计的条件转移定理，不是无条件 `Omega`、不是 `Omega_±` 的最终闭环，也不推出 RH。

## 边界层完全捕获后的无损转移

`ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTUnnormalizedBoundaryCapturedOscillation.lean`
把已有的 boundary-capture 结论提升到了真实未归一化误差。若有限可见簇 `S` 包含每个满足 `Re rho = beta` 的 Carlson 正零点索引，则外部边界质量严格为零。于是：

- 对每个 `0 <= q < c`，无符号主簇见证转成 `|psi_0(x)-x| >= q*x^beta` 的任意远实点见证；
- 对每个 `0 <= q < c`，正、负主簇见证转成同一个 `q*x^beta` 尺度的双向任意远实点见证；
- 若 `0 < c`，可以规范地取显式正常数 `q=c/2`。

这说明 Carlson 补集在目标实部边界上的全部常数损失确实集中于未捕获边界质量 `B_partial(beta,S)`；一旦边界层被主簇吸收，转移阈值从 `q<c-2B_partial` 恢复为 `q<c`。剩余未闭合项仍是外部主簇的无符号或双向振荡见证，而不是密度/显式公式余项。

## 可求和边界层的有限 ε-捕获

`ZeroDensityLayerBudgetActualCarlsonBoundaryMassFiniteCapture.lean` 证明了此前缺失的有限逼近定理。对 `1/2 < sigma < 1`、任意目标实部 `beta` 和任意 `epsilon > 0`，存在共轭稳定有限簇 `S` 使

`actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S < epsilon`。

证明不是把无限边界层假设成有限，而是对完整的非负、可求和边界项应用 `summable_iff_vanishing_norm`：先选有限索引集捕获除 `epsilon/2` 外的全部有限尾和，再映射成真实零点 Finset，最后取共轭闭包并用边界质量反单调性保持严格上界。

因此，即便 `Re rho = beta` 上可能有无限多个零点，Carlson 边界常数损失也可由某个有限主簇压到任意小。这比“整个边界层本来就是有限簇”的假设更弱，并为把任意 `q<c` 近似保真地接入实际 `psi_0(x)-x` 转移提供了定量基础。它仍不自动提供该随 `epsilon` 选择的簇的主项振荡见证；该项属于外部局部振荡任务。

## 有限捕获自动适配任意严格振幅间隙

`ZeroDensityLayerBudgetActualCarlsonBoundaryMassFiniteGapCapture.lean` 把 epsilon-捕获直接改写成 transfer 所需条件：只要 `q<c`，就存在共轭稳定有限簇 `S` 使 `2*B_partial(beta,S)<c-q`。特别地，若 `c>0`，存在有限稳定簇满足 `2*B_partial(beta,S)<c`。

因此在 Carlson/显式公式侧，不需要假设整条 `Re rho=beta` 边界只含有限多个零点，也不需要完全捕获边界层；可求和性已经保证任何严格次于主簇系数 `c` 的目标常数都能留出足够的有限簇余量。尚未自动化的唯一相关输入，是这个按间隙选出的有限簇本身必须满足相应的主项振荡见证和外部实部条件。

## 有限 transfer 簇的结构条件自动构造

`ZeroDensityLayerBudgetActualCarlsonFiniteGapTransferCluster.lean` 继续消除了
有限捕获簇上的结构性外部条件。给定任意有限簇 `S`，定义
`actualCarlsonAdjoinRealOrdinateZeros S`，把高度零处全部非平凡零点并入
`S`。该高度切片是有限集；其成员在复共轭下逐点不变。因此：

- 若 `S` 共轭稳定，并入后的有限簇仍共轭稳定；
- 并入后，实轴纵坐标零点的簇外补集严格为空；
- 扩大主簇只会减小 Carlson 簇外边界质量。

于是，只要全局给定实际 Carlson 正零点的实部上界

\[
\operatorname{Re}\rho\leq\beta,
\]

并且 `q<c`，就存在一个有限共轭稳定簇同时满足：

- 所有簇外正纵坐标零点的实部不超过 `beta`；
- 所有簇外实轴纵坐标零点的实部严格小于 `beta`，因为该补集为空；
- `2*B_partial(beta,S)<c-q`。

这正是 balanced-boundary transfer 在 Carlson 侧需要的完整结构证书。
它没有构造该有限簇的主项振荡；`hmain`、`hmainPos`、`hmainNeg` 仍由
独立的局部有限簇振荡任务提供。因此此处闭合的是密度与补集余项条件，
不是无条件 `Omega` 或 `Omega_±` 定理。

## 选定有限簇到真实 PNT 误差的直接转移

`ZeroDensityLayerBudgetActualCarlsonFiniteGapPNTUnnormalizedTransfer.lean`
把有限 transfer 簇的存在定理与 balanced Carlson lower transfer、自然数
取样到实数取样、相对误差到未归一化误差三个步骤直接复合。

对任意 `0 <= q < c`，在平衡条件
`(1+sigma)/2 < beta` 和全局 `Re rho <= beta` 下，定理自动选择一个有限
共轭稳定簇 `S`，并同时返回全部结构证书及以下唯一剩余蕴含：

\[
\text{visible-cluster hmain at coefficient }c
\quad\Longrightarrow\quad
|\psi_0(x)-x|\geq qx^\beta
\text{ at arbitrarily large real }x.
\]

因此 Carlson 密度、实轴补集、边界质量损失和显式公式余项不再需要由
调用者逐项组装。剩余缺口被精确收缩为：独立局部振荡任务必须对这个
按 `q<c` 选择的有限簇给出 `dynamicVisibleClusterPNTMain` 的 `hmain`。
该接口没有假设或声称已经证明这个局部振荡输入。

`ZeroDensityLayerBudgetActualCarlsonFiniteGapPNTSignedUnnormalizedTransfer.lean`
给出同一选择过程的双向版本。它只选择一个有限共轭稳定簇，并要求该簇
在相同系数 `c` 下分别提供正向和负向主项见证；结论是在同一个严格次级
系数 `q<c` 上得到 `psi_0(x)-x` 的正、负任意远实点见证。因而双向链的
Carlson 侧也已经内部化，但这仍是条件性的 `Omega_±` 转移接口。

`ZeroDensityLayerBudgetActualCarlsonFiniteGapPNTCanonicalUnnormalizedTransfer.lean`
在 `c>0` 时进一步固定 `q=c/2`。Lean 同时证明该规范系数严格为正，并
自动选择满足 `2*B_partial<c-c/2` 的有限簇。无符号与双向定理因此都向
局部振荡任务暴露一个无需额外算术选择的具体目标常数。

## 保留有限最右种子簇的 Carlson 扩张

`ZeroDensityLayerBudgetActualCarlsonFiniteSeedGapTransferCluster.lean` 把
此前的全局 Carlson 索引上界替换为更自然的 zeta 层条件。给定有限共轭
稳定种子簇 `S₀`，只要求

\[
\texttt{OutsideClusterRealPartCap }S_0\,\beta,
\]

即每个 `S₀` 外非平凡 zeta 零点满足 `Re rho <= beta`。定理自动构造有限
簇 `S`，使 `S₀ subset S`，并把 Carlson 边界有限捕获簇和全部实轴纵坐标
零点并入 `S`。扩大簇使边界质量反单调，因此仍保持
`2*B_partial(beta,S)<c-q`。

这一区别是实质性的：`S₀` 内部可以保留不满足该 cap 的有限异常或最右
零点，只有其补集受上界约束。模块同时证明 zeta 层 cap 自动作用于真实
Carlson 正零点索引，从而不要求最大实部层了解 Carlson 的枚举实现。

`ZeroDensityLayerBudgetActualCarlsonFiniteSeedGapPNTUnnormalizedTransfer.lean`
把该扩张直接接到 `psi_0(x)-x`。对任意 `0<=q<c`，它给出包含 `S₀` 的
实际有限簇，并分别提供无符号和同一 `q*x^beta` 尺度的双向条件转移。
尚未闭合的输入仍精确是扩张后有限簇的 `hmain` 或
`hmainPos`/`hmainNeg`，而不是 Carlson 补集条件。

`ZeroDensityLayerBudgetActualCarlsonFiniteSeedGapPNTCanonicalUnnormalizedTransfer.lean`
在 `c>0` 时固定 `q=c/2`，并保留 `S₀ subset S` 证书。由此，最大实部层
只需交付有限共轭稳定种子簇及其补集 cap；局部振荡层则针对自动扩张后
的有限簇证明主项见证，最终 PNT 振荡常数已经明确为严格正的 `c/2`。

自动扩张现在还保留
`OutsideClusterRealPartCap S beta` 本身，而不只导出 Carlson 枚举上的
`hreHigh`。这是由 `S₀ subset S` 的补集单调性得到的。因而后续模块可以
继续把最终簇作为 zeta 层对象使用，最大实部证书不会在进入 Carlson
求和层后丢失。
