# Xi Function Implementation Plan

## Current Result

This branch records a minimal project-facing xi boundary, but it does not keep
`XiFunction.lean` yet because this isolated worktree cannot currently build
Lean files. The intended file should reuse the existing local definition
`RiemannHypothesis.completedZeta` from `RiemannExplorer.lean`:

```lean
noncomputable def xiFunction (s : ℂ) : ℂ :=
  completedZeta s
```

The first target API lemmas are intentionally small:

- `xiFunction_eq_completedZeta`
- `xiFunction_one_sub`
- `xiFunction_sub_one`

These should use the existing local theorem
`RiemannHypothesis.functional_equation`.

The initial probe file had this shape:

```lean
import RiemannExplorer

open Complex

namespace RiemannHypothesis

noncomputable def xiFunction (s : ℂ) : ℂ :=
  completedZeta s

theorem xiFunction_eq_completedZeta (s : ℂ) :
    xiFunction s = completedZeta s := by
  rfl

theorem xiFunction_one_sub (s : ℂ) :
    xiFunction s = xiFunction (1 - s) := by
  simp [xiFunction, functional_equation s]

theorem xiFunction_sub_one (s : ℂ) :
    xiFunction (1 - s) = xiFunction s := by
  exact (xiFunction_one_sub s).symm

end RiemannHypothesis
```

## Why This Boundary Is Conservative

The repository already contains a completed-zeta expression named
`completedZeta` and proves a functional equation for it. Reusing that object is
safer than introducing a second, potentially incompatible expression for

```text
xi(s) = 1/2 * s * (s - 1) * pi^(-s/2) * Gamma(s/2) * zeta(s).
```

The wrapper would give future Li, Weil, and Hadamard-route files one stable
name to depend on while preserving the option to replace the implementation
later.

## Mathlib and Local Names

Names already used by the local project:

- `completedRiemannZeta₀`
- `completedRiemannZeta₀_one_sub`
- `completedZeta`
- `functional_equation`
- `RiemannHypothesis.Statement`
- `RiemannHypothesis.IsNontrivialZero`

Names that should be audited before deeper xi work:

- `completedRiemannZeta`
- `completedRiemannZeta_eq`
- `riemannZeta_eq_completed_div_Gamma`
- `Gammaℝ`
- `Gammaℝ_def`
- `differentiable_completedZeta₀`

## Build Status

Attempted command:

```bash
lake build XiFunction
```

Observed blocker:

```text
manifest out of date: git revision of dependency 'mathlib' changed
error: .lake/packages/mathlib: revision not found 'main'
```

This is a Lake/manifest dependency issue in this isolated worktree. To avoid
leaving an unverified Lean file, the probe `XiFunction.lean` was removed from
the branch and preserved above as the next implementation target. The branch
should not update `lake-manifest.json` as part of this xi boundary step because
other Lean work is ongoing in separate branches.

## Next Lean Targets

After the Lake dependency state is stabilized, extend `XiFunction.lean` in this
order:

1. Prove agreement with the classical expression in the half-plane `1 < Re(s)`.
2. Prove or restate differentiability/entireness through `completedRiemannZeta₀`.
3. Prove zero correspondence between `xiFunction` and local nontrivial zeta
   zeros away from `0` and `1`.
4. Export a minimal API for Li criterion work.

## What Not To Add Yet

- Do not add Li coefficients to `XiFunction.lean`.
- Do not add Hadamard product statements with `sorry`.
- Do not claim this proves any part of RH beyond naming and functional-equation
  plumbing.
