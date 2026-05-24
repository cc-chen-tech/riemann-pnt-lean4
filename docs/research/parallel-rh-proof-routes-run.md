# Parallel RH Proof Routes Run

## Purpose

Coordinate three independent RH-adjacent worktrees. These tasks are separated
because the xi foundation, Li criterion computations, and explicit formula
route have different write scopes and different risk profiles.

## Base

Shared baseline commit:

```text
4cc33e0 add RH computational experiment scaffolding
```

## Worktrees

### Xi Foundation

Branch: `codex/rh-xi-function`

Path:

```text
/Users/luicy/.config/superpowers/worktrees/riemann-pnt-lean4/codex-rh-xi-function
```

Owned outputs:

- `XiFunction.lean`
- `docs/research/xi-function-implementation-plan.md`

### Li Criterion Computational Route

Branch: `codex/rh-li-criterion`

Path:

```text
/Users/luicy/.config/superpowers/worktrees/riemann-pnt-lean4/codex-rh-li-criterion
```

Owned outputs:

- `experiments/rh/li_coefficients.py`
- `experiments/rh/zeros_fixture.*`
- `experiments/rh/output/*`
- `tests/test_li_coefficients.py`
- `docs/research/li-criterion-computational-plan.md`

### Explicit Formula Route

Branch: `codex/rh-explicit-formula`

Path:

```text
/Users/luicy/.config/superpowers/worktrees/riemann-pnt-lean4/codex-rh-explicit-formula
```

Owned outputs:

- `experiments/rh/explicit_formula.py`
- `experiments/rh/output/explicit_formula_report.md`
- `tests/test_explicit_formula.py`
- `docs/research/explicit-formula-route.md`

## Integration Rule

Each branch should finish independently and pass its focused tests. Integration
back to `codex/rh-computational-experiments` should happen only after review.

