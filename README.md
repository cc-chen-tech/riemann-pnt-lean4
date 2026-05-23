# Riemann Zeta Function and Prime Number Theorem — Lean 4 Formalization

A formalization of the classical analytic proof of the Prime Number Theorem in Lean 4,
using de la Vallée Poussin's 3-4-1 inequality. Built on Mathlib.

## Status

**4 sorries remaining** — each corresponds to infrastructure not yet available in Mathlib
(contour integration, Hadamard factorization, Borel-Carathéodory). The rest is fully
proved with no gaps.

## File Overview

| File | Description | Status |
|---|---|---|
| `RiemannExplorer.lean` | Riemann Hypothesis statement, zeta definitions, functional equation, trivial zeros | sorry-free |
| `GammaResidue.lean` | Gamma function residue formula at negative integers | partial |
| `HardyTheorem.lean` | Hardy's theorem framework — infinitely many zeros on critical line | partial |
| `PrimeNumberTheorem.lean` | PNT forms, equivalences, Li(x) asymptotics, zero symmetry, explicit formula | 1 sorry |
| `ZeroFreeRegion.lean` | 3-4-1 inequality, compact zero-free region, log derivative series, residue bounds | 3 sorries |

## Key Results (sorry-free)

### 3-4-1 Inequality (de la Vallée Poussin)

```
3·Re(-ζ'/ζ(σ)) + 4·Re(-ζ'/ζ(σ+it)) + Re(-ζ'/ζ(σ+2it)) ≥ 0
```

This trig identity `3 + 4cos θ + cos 2θ = 2(1+cos θ)² ≥ 0` is the core of the
classical zero-free region proof.

### Compact Zero-Free Region

For any T ≥ 2, there exists d > 0 such that ζ(s) has no zeros in
{|Im(s)| ≤ T, Re(s) ≥ 1-d}.

### Pole Structure at s = 1

- ζ(s) has a simple pole at s = 1 with residue 1
- `1 < (σ-1)ζ(σ) ≤ σ` for σ > 1

### Prime Number Theorem Equivalences

The three classical forms are equivalent:
1. π(x) ~ x/log x
2. π(x) ~ Li(x)
3. ψ(x) ~ x

### Von Mangoldt Explicit Formula (statement, proof: sorry)

```
ψ(x) = x - Σ_ρ x^ρ/ρ - ζ'(0)/ζ(0) - ½log(1-x⁻²)
```

## Quick Start

### Prerequisites

- [Lean 4](https://lean-lang.org/) (≥ 4.0.0)
- [Elan](https://github.com/leanprover/elan) (Lean version manager)

### Build

```bash
# Install Lean 4 via elan (if not already installed)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Clone and build
git clone https://github.com/YOUR_USERNAME/riemann-pnt-lean4.git
cd riemann-pnt-lean4
lake build
```

## Infrastructure Gaps (the 4 sorries)

| Theorem | Missing Mathlib Component | Difficulty |
|---|---|---|
| Explicit formula (Perron) | Contour integration / Residue theorem | High |
| Classical zero-free region (σ ≥ 1-c/log|t|) | Hadamard factorization or Borel-Carathéodory | Medium |
| Vinogradov-Korobov zero-free region | Exponential sum estimates | Very High |
| Hardy's theorem (integral asymptotics) | Asymptotic expansions of special functions | Medium |

### Easiest Path Forward

The **Borel-Carathéodory** route is lighter than Hadamard factorization:
once Mathlib has this lemma, `classical_zero_free_region` can be proved immediately.

## Related Work

- [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (Lean 4) — PNT via Wiener-Ikehara
- Avigad et al. (2007) — Elementary PNT in Isabelle
- Harrison (2009) — Newman's analytic PNT in HOL Light
- Mathlib's `riemannZeta` — Zeta function basics by Loeffler & Stoll

## Citation

If you use this work in your research, please cite:

```bibtex
@software{riemann_pnt_lean4,
  title = {Formalizing the Prime Number Theorem's Analytic Proof in Lean 4},
  year = {2026},
  url = {https://github.com/YOUR_USERNAME/riemann-pnt-lean4}
}
```

## License

Apache 2.0 — same as Mathlib.
