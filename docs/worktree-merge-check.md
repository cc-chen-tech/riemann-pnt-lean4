# Worktree Merge Candidates (2026-06-03)

本地同时存在 4 个副分支 worktree，但当前仅有部分命名差异；尚未出现可直接用于主证明的 `def ... : Prop` 目标收敛。

## 已扫描的分支

- `codex/rh-computational-experiments` (`681ef12`)
- `codex/rh-explicit-formula` (`f06b79b`)
- `codex/rh-li-criterion` (`74a63a8`)
- `codex/rh-xi-function` (`a68fc5`)

## 最近一次扫描（2026-06-03）

`scripts/scan-worktrees-targets.py` 报告结果如下：

- 4 个 worktree 的目标声明并非与主分支一致；差异主要在命名与目标覆盖范围上。
- 这些分支有额外的 `def` 目标（例如 `IsSimplePoleOfGamma`, `IsTrivialZero`, `Statement` 等），
  同时缺失主分支的 23 个核心目标之一部分（例如 `classical_zero_free_region`, `vinogradov_korobov_zero_free_region`, 各类 RH/Hardy 目标等）。

因此当前不建议直接合并；需先在分支内按主分支目标命名与链路对齐后再评估可复用内容。

## 可合并内容（人工核对）

- 上述分支新增文件主要是实验/记录用途：
  - `experiments/rh/*`
  - `tests/test_*.py`
  - `docs/research/*.md`
  - `docs/research/*`

- 当前主干 (`main`) 与这些分支相比，未发现新增的可直接 cherry-pick 的核心 `*.lean` 证明性进展；其差异集中在目标命名和实验性补充。
  - 也就是说，**没有可直接 cherry-pick 的缺失链路定理证明**。

## 当前主干状态确认

- `lake build` 通过（无 `sorry`/`admit`/`axiom`）。
- `scripts/check-targets-consistent.py` 输出目标数为 `23`，与 `docs/current-target-status.json` 一致。

## 建议

- 若要继续推进证明完成度，优先顺序仍是：
  1. `ZeroFreeRegion.classical_zero_free_region`
  2. `PrimeNumberTheorem.explicit_formula_von_mangoldt`
  3. `PrimeNumberTheorem.rh_iff_optimal_error`
  4. `HardyTheorem` 深度目标链（`hardy_two_signed_moments_target` 等）
