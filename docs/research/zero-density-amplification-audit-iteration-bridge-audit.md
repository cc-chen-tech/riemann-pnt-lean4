# zero-density amplification: iteration bridge audit

本文件记录第三阶段：把“局部分支证书”提升为 Carlson 反证所需的全局放大桥。

## 1) 可迭代局部分支/邻接证书定义

新增 `IterativeLocalBranchCertificate`，字段（与深度 `n`）包括：

- `windows : ℕ → ℝ → Finset ι`
- `cluster : ℕ → ι → Finset ρ`
- `windowStart : ℕ → ι → ℝ`
- `branchCount : ℕ → ℝ → ℕ`
- `localContribution : ℕ`
- 邻接分离：`windowStartPairwiseSeparated`（当前窗口起点满足 `start i + H ≤ start j` 或反向）
- 每窗局部贡献下界：每窗口局部计数至少 `localContribution`
- 分支计数抽取：`branchCount n T ≤ (windows n T).card`

并给出引理：邻接分离可推出 `((windows n T : Set ι).PairwiseDisjoint fun i => disjointWindowClusterSlice ...)`，即防止重复计数的分离条件。

## 2) 从深度/分支数提取显式零点/窗口数量下界

引理 `iterativeBranch_lowerCount_ge_q` 给出：

	a) 对每个 `n < depth`，若上述证书条件在 `atTop` 下成立，
	则

	`disjointWindowFamilyLowerCount ... T ≥ (localContribution : ℝ) * branchCount n T`

	（即至少每个窗口贡献 `k`，共有 `branchCount n T` 个窗口）。

新增 `iterativeBranch_qpow_lowerCount_ge_qpow`，把分支关系强化为指数形式：

- 若固定层 `n` 满足 `∀ᶠ T, q(T)^n ≤ branchCount n T`，
  则

  `disjointWindowFamilyLowerCount ... T ≥ (localContribution : ℝ) * q(T)^n`。

这给出“分支增长率下界”与“全局窗口累计下界”的明确算术通道。

## 3) 与 Carlson 反证连接并读取增长率

引理 `iterativeBranch_carlson_contradiction`：

- 假设 `hgap` 给出
	`((localContribution : ℝ) * branchCount n T) - C * ‖...‖ → +∞`
- 并给出零计数上界 `hlower`：局部累计下界 ≤ `ZeroDensity.zeroDensityCount`。

则调用既有 `disjointWindowFamily_carlson_instance_contradiction` 得到 `False`。

第四阶段新增 `iterativeBranch_qpow_carlson_contradiction`，将 `hgap` 写为

- `((localContribution : ℝ) * q(T)^n) - C * ‖...‖ → +∞`

时也可直接得出 `False`。因此显式充分条件可以写成：

- `q(T)^n ≳ (1/localContribution) · ‖(T+H)^{4σ(1-σ)} (log(T+H))^4‖`.

若 `n` 为常数层，则要想达到 Carlson 主项，`q(T)` 本身必须至少和 Carlson 主项同阶；
若 `q(T)` 为常数（特别是 `q>1` 固定），则 `n(T)=o(log T)` 不会满足主项支配。

## 3') 固定深度与不足条件

为了避免“单一层次”误判，新增反面模板：

- `iterativeBranch_qpow_not_enough_for_divergence_if_eventually_subdominant`：
  若 `k·q(T)^n` 终将不超过 Carlson 主项（而非仅略低于），
  则 `(k·q(T)^n - Carlson(T))` 不可能趋于 `+∞`。

这一模板与一线的 `one_offline_zero_certificate_does_not_yield_diverging_gap` 一起，形成“固定深度 + 未达主项” 的定量拒绝路径。

## 4) “单个离线零点”不可推出该证书（反模型）

定理 `one_offline_zero_certificate_does_not_yield_diverging_gap` 给出严格反证：

- 若对每个高度 `T` 只有一个窗口（`(windows T).card ≤ 1`），每簇大小也有上界 `1`，
- 且 Carlson 主项（例如 `C * ‖...‖`）在 `atTop` 下发散，

则

`
(fun T => disjointWindowFamilyLowerCount ... - C*‖...‖)
`
不可能趋于 `+∞`。

这给出的是可执行的否定结论，不是“缺输入”式声明：现有输入下，单零点/固定窗口证书不能满足第三阶段所需的放大增长前提。
