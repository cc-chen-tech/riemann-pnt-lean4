# Zero-density amplification audit (fully inside `research/zero-density-amplification-audit`)

本文件只记录审计链：**已在仓库中已有的 Carlson 可实例化定理**与参数化接口分开。

## 1) 局部簇到全局 `N(σ,T)` 的不重叠累加

已新增桥接：

- `PrimeNumberTheorem.disjointWindowFamilyLowerCount_eventually_le_zeroDensity`

输入条件
1. 每个窗口切片
   `disjointWindowClusterSlice` 之间在 `atTop` 以后两两不交；
2. 每个窗口切片都包含于同一个 `ambient (T + H)`；
3. `ambient` 的基数受控于 `ZeroDensity.zeroDensityCount`。

结论是逐点（`Filter.atTop`）

```lean
_disjointWindowFamilyLowerCount ≤ (ambient (T + H)).card ≤ zeroDensityCount (σ, T+H)
```

这一步是避免重复计数的形式化核心。`Finset.biUnion` 与 pairwise 不交假设提供
`sum card = card (biUnion)`，再用 `card_le_of_subset` 进入 ambient 计数。

## 2) 固定有限簇为何不够

已新增

- `PrimeNumberTheorem.finiteDisjointWindowFamily_gap_not_tendsto_atTop`

给出精确结论：当 `windows` 固定为有限族时，

```lean
disjointWindowFamilyLowerCount ... T ≤ B := ∑ card(cluster i)
```

是一个全局常数上界，因此不可能使
`lower(T) - upper(T) → +∞`，进而不可能触发 `cluster_density_contradiction_of_gap_tendsto_atTop`。

这直接回答“一个或有限多个簇不够”的问题。

## 3) Carlson 实例化链路（真实仓库定理）

已新增

- `PrimeNumberTheorem.disjointWindowFamily_carlson_contradiction`
- `PrimeNumberTheorem.disjointWindowFamily_carlson_instance_contradiction`

第一个定理：给定具体 `hCarlson : CarlsonEventualMajorant σ`，把
`hgap : disjointWindowFamilyLowerCount - (C * ‖(T + H)^(4σ(1-σ)) * (log (T + H))^4‖) → +∞`
与零密度下界 `hlower` 一起直接矛盾。

第二个定理给出可实例化到仓库定理的接口：

- 假设 `hσ : 1/2 < σ`, `hσ1 : σ < 1`；
- `exists_carlsonEventualMajorant hσ hσ1` 取 `C`；
- 将 `hgap` 写成以该 `Classical.choice` 上的 `C` 为系数。

这样得到的是**仓库已有 Carlson 的条件化矛盾定理**，不是新的 Carlson/Guth–Maynard 公理。

这里是直接实例化仓库已有的 `exists_carlsonEventualMajorant`（可由标准证明库输出），不依赖新假设。

与“每窗贡献常数 κ”一致的定量解释：若存在 `κ > 0` 和 `T0` 使得
`∀ T ≥ T0, ∀ i ∈ windows T, localClusterLowerBound ... ≥ κ`，
则

`disjointWindowFamilyLowerCount ... T ≥ κ * |windows T|`.

要与 Carlson 主项竞争，必须满足

`κ * |windows T|` 至少与 `T^(4σ(1-σ)) (log T)^4` 同阶或更大，即窗口数需要支配

`|windows T| ≳ (1/κ) * T^(4σ(1-σ)) (log T)^4`.

因此若窗口数仅有 polylog（如 `O((log T)^k)`，任意固定 `k`）增长，不能触发 Carlson 型 `hgap` 矛盾。

## 4) half-isolated 分支的最小 quantitative contract

已定义并沿用：

- `PrimeNumberTheorem.HalfIsolatedDetectorContractOutput` (即 `IsEventuallyHalfSmall detector amplitude`)

已有传递定理：

- `PrimeNumberTheorem.halfIsolatedDetectorOutput_survives_signed_witnesses`
- `PrimeNumberTheorem.halfIsolatedDetectorOutput_survives_along_dynamic_budget`

说明：仅有“检测器最终半小 + 有主项证据 + 分解关系”即可传递；
不要求在本文件中直接写出 detector 引理的具体构造，即不把未证明输出当作矛盾。

## 5) 目前边界/待补齐

- Guth–Maynard 在仓库中未形式化；只能保留为**参数化 corollary**。
- 若实际 Carlson 类型在未来变更（如对 `atTop` 区间、对数幂次或取绝对值标准变动）
  且不能一一对齐，则该接口会阻断于：`hgap` 系数项表达式类型/定义不能匹配到
  `CarlsonEventualMajorant.bound` 的 RHS。
