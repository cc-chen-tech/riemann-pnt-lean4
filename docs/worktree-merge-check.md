# Worktree Merge Candidates (2026-06-03)

本地同时存在 4 个副分支 worktree，但它们当前都未引入可直接用于主证明的 Lean 代码。

## 已扫描的分支

- `codex/rh-computational-experiments` (`681ef12`)
- `codex/rh-explicit-formula` (`f06b79b`)
- `codex/rh-li-criterion` (`74a63a8`)
- `codex/rh-xi-function` (`a68fc5`)

## 可合并内容（人工核对）

- 上述分支新增文件主要是实验/记录用途：
  - `experiments/rh/*`
  - `tests/test_*.py`
  - `docs/research/*.md`
  - `docs/research/*`

- 当前主干 (`main`) 与这些分支相比，未发现新增的 `*.lean` theorem/lemma 目标之外的代码性进展。
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

