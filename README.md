# Riemann Zeta Function and Prime Number Theorem — Lean 4 Formalization

A Lean 4 project developing formalized infrastructure around the Riemann zeta
function, Hardy's theorem, zero-free regions, and Prime Number Theorem statements.
It is built on Mathlib and currently serves as a buildable proof framework with
explicitly isolated unproved target statements.

## Status

`lake build` succeeds with Lean 4.29.1 / Mathlib 4.29.1. The repository is not
a completed proof of the Prime Number Theorem or the Riemann Hypothesis.

Current code status:

| File | `sorry` count | Unproved targets |
|---|---:|---|
| `GammaResidue.lean` | 0 | General Gamma residue formula completed |
| `HardyTheorem.lean` | 0 | Hardy-Z phase facts proved; corrected integral asymptotic, positivity and zero-counting targets |
| `PrimeNumberTheorem.lean` | 0 | Bounded-height zero finiteness proved; RH error equivalence and von Mangoldt explicit formula targets |
| `ZeroFreeRegion.lean` | 0 | 3-4-1 and compact zero-free region proved; quantitative zero-free-region targets |

Total: 0 syntactic `sorry` occurrences in Lean source files.

Unresolved target declarations (currently not promoted to theorems): **23**.

 - `HardyTheorem` namespace: 11
 - `PrimeNumberTheorem` namespace: 9
 - `ZeroFreeRegion` namespace: 2
 - `RiemannExplorer` namespace: 1

## File Overview

| File | Description | Status |
|---|---|---|
| `RiemannPNT.lean` | Build entry point importing all top-level modules | sorry-free |
| `RiemannExplorer.lean` | Riemann Hypothesis statement, zeta definitions, functional equation, trivial zeros | sorry-free |
| `EulerAndLfunctions.lean` | Thin wrappers around Mathlib zeta/Euler product/L-function facts | sorry-free |
| `GammaResidue.lean` | Gamma residue facts and numerical special cases | sorry-free |
| `HardyTheorem.lean` | Hardy Z-function setup with corrected target statements for critical-line zeros | sorry-free, targets unproved |
| `PrimeNumberTheorem.lean` | PNT forms, equivalences, Li(x) asymptotics, zero symmetry, bounded-height zero finiteness, explicit formula target | sorry-free, targets unproved |
| `ZeroFreeRegion.lean` | 3-4-1 setup, log derivative series, compact zero-free region, quantitative zero-free-region targets | sorry-free, quantitative targets unproved |

## Verified Components

The project currently verifies several supporting statements, including:

- the formal RH statement restricted to nontrivial zeros;
- zeta special-value and Euler-product wrappers available in Mathlib;
- basic PNT-form equivalence scaffolding and asymptotic lemmas;
- the trigonometric identity `3 + 4cos θ + cos 2θ = 2(1+cos θ)² ≥ 0`;
- the full 3-4-1 logarithmic-derivative nonnegativity combination;
- several zeta nonvanishing and pole-behavior wrappers from Mathlib;
- the Gamma residue formula at negative integers and numerical special cases;
- the compact zero-free region near `Re(s)=1` for each bounded height;
- finiteness of nontrivial zeros in each bounded-height strip.

## Unfinished Core Targets

### 3-4-1 Logarithmic-Derivative Combination

```
3·Re(-ζ'/ζ(σ)) + 4·Re(-ζ'/ζ(σ+it)) + Re(-ζ'/ζ(σ+2it)) ≥ 0
```

The full infinite-series combination is proved in
`ZeroFreeRegion.log_deriv_zeta_nonneg_combination`.

### Compact Zero-Free Region

For any T ≥ 2, there exists d > 0 such that ζ(s) has no zeros in
{|Im(s)| ≤ T, Re(s) ≥ 1-d}.

This is proved in `ZeroFreeRegion.classical_zero_free_region_compact`.

### Prime Number Theorem Equivalences

The three classical forms are equivalent:
1. π(x) ~ x/log x
2. π(x) ~ Li(x)
3. ψ(x) ~ x

### Von Mangoldt Explicit Formula

The current repository contains this as a corrected `Prop` target statement,
not as a proved theorem.  The Lean target now uses the midpoint convention
`chebyshevPsi0` and a height-truncated zero contribution
`finiteNontrivialZeroSum`, rather than an unconditional unordered `tsum` over
all nontrivial zeros.

## Quick Start

### Prerequisites

- [Lean 4](https://lean-lang.org/) via `elan`
- [Elan](https://github.com/leanprover/elan) (Lean version manager)
- The checked-in `lean-toolchain` pins Lean to `leanprover/lean4:v4.29.1`

### Build

```bash
# Install Lean 4 via elan (if not already installed)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Clone and build
git clone https://github.com/cc-chen-tech/riemann-pnt-lean4.git
cd riemann-pnt-lean4
lake build
```

This checkout is configured to use a local path dependency at `vendor/mathlib`.
That directory is ignored by git because it is large. For a fresh clone, either
place Mathlib 4.29.1 at `vendor/mathlib`, or change `lakefile.lean` back to a
git dependency and regenerate the manifest.

## Infrastructure Gaps

See [`PUBLISHING.md`](PUBLISHING.md) for the exact release-readiness checklist
and the commands used to verify the current proof-gap count.

See [`docs/mathematical-contributions.md`](docs/mathematical-contributions.md)
for a precise mathematical description of the project-local verified
contributions and their proof routes.

See [`docs/formal-theorem-inventory.md`](docs/formal-theorem-inventory.md)
for a reviewer-oriented inventory separating proved declarations from target
statements.

See [`docs/implementation-standards.md`](docs/implementation-standards.md)
for the standard that prevents target statements from being reported as proved
theorems.

See [`docs/missing-chains-index.md`](docs/missing-chains-index.md) for the
parallel work breakdown of the remaining analytic chains.

| Theorem | Missing Mathlib Component | Difficulty |
|---|---|---|
| Explicit formula (Perron) | Contour integration / Residue theorem | High |
| Classical zero-free region (σ ≥ 1-c/log|t|) | Hadamard factorization or Borel-Carathéodory | Medium |
| Vinogradov-Korobov zero-free region | Exponential sum estimates | Very High |
| Hardy's theorem targets | Corrected moment estimates and asymptotic expansions of special functions | Medium–High |

### Easiest Path Forward

The **Borel-Carathéodory** route is lighter than full Hadamard factorization,
but this repository still needs additional zeta growth and logarithmic-derivative
estimates before the quantitative zero-free region can be closed.

## Related Work

- [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (Lean 4) — PNT via Wiener-Ikehara
- Avigad et al. (2007) — Elementary PNT in Isabelle
- Harrison (2009) — Newman's analytic PNT in HOL Light
- Mathlib's `riemannZeta` — Zeta function basics by Loeffler & Stoll

## Citation

If you use this work in your research, please cite:

```bibtex
@software{riemann_pnt_lean4,
  title = {Lean 4 Infrastructure Toward Analytic Prime Number Theorem Formalization},
  year = {2026},
  url = {https://github.com/cc-chen-tech/riemann-pnt-lean4}
}
```

## License

Apache 2.0 — same as Mathlib.
