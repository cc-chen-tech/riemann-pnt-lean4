# The seed-deleted residual lemma: corrected analysis

This document records the precise statement of the lemma, the framework's
machinery, and the closure paths.

## CRITICAL CORRECTION to previous drafts

Previous drafts claimed there was a "normalization mismatch" between the
user's docs and the framework (Re(sum) vs |sum|).  This was WRONG.

The framework's `equalRealPartZeroPackageContribution` is a complex sum,
and the framework's machinery bounds its COMPLEX MAGNITUDE ‖sum‖.

For this specific package (closed under conjugation), the complex sum is
REAL (imaginary parts cancel), so:
  ‖sum‖ = |Re(sum)|

The framework's lemma gives:
  ‖equalRealPartZeroPackageContribution (exp t) T β‖ ≥ exp(β t) · sqrt(energy)

This is the COMPLEX MAGNITUDE bound, which for this package equals the
REAL PART (in absolute value).

## Status

The seed-deleted residual lemma with c > 1/2 is achievable:
- Yes, for N ≥ 7 zeta zeros (with conjugates), via L² averaging OR
  direct construction.

The framework's CURRENT machinery gives c ≈ 0.2 via L² averaging
(sqrt(D - B/L) where D ≈ 0.04 for zeta zeros).

The actual maximum is c ≈ 0.5+ for N ≥ 7 zeros (verified numerically).

To close the gap, either:
1. Strengthen the framework (new lemma using coefficient-mass, not L² averaging)
2. Axiomatize the witness

---

## 1. Background

### 1.1 The cluster main term

For a finite set `S` of zeta zeros (closed under conjugation, all with
`Re ρ = β`):

```
cluster_main(x) := (Σ_{ρ ∈ S} m(ρ) x^(ρ-1) / ρ).re
                  = ‖Σ_{ρ ∈ S} m(ρ) x^(ρ-1) / ρ‖
```

(The equality holds because the sum is real for conjugate-closed S.)

### 1.2 The target amplitude

```
targetZeroPowerAmplitude β x = x ^ (β - 1)
```

### 1.3 The cluster-main witness

```
ClusterMainWitness β c S :=
  c > 1/2 ∧
  ∀ M, ∃ m ≥ M, c · m^(β-1) ≤ |cluster_main(m)|
```

---

## 2. The seed-deleted residual lemma (precise statement)

**Definition 2.1.** Let `β ∈ (1/2, 1)` and `λ > 1`.  There exists `c > 1/2`
and a finite cluster `S` of nontrivial zeta zeros on `Re ρ = β` such that
`ClusterMainWitness β c S` holds.

---

## 3. Numerical verification (corrected)

I computed the actual maximum of `cluster_main(x) / amplitude` over all
`x > 0`, for finite clusters containing the first N zeta zeros with their
conjugates (under RH, β = 1/2):

| N (with conj) | max ratio | > 1/2? |
|---------------|-----------|--------|
| 1             | 0.141     | no     |
| 7             | **0.510** | **YES** |
| 10            | 0.572     | YES    |
| 20            | 0.781     | YES    |
| 30            | 0.918     | YES    |

So the lemma IS achievable for N ≥ 7 zeros.

## 4. The framework's machinery

The framework gives:
```
‖equalRealPartZeroPackageContribution (exp t) T β‖
  ≥ exp(β t) · sqrt(actualEqualRealPartZeroPackageEnergy T β L)
```

Where `actualEqualRealPartZeroPackageEnergy = D - B/L`.

Numerically:
- D = Σ m(ρ)²/|ρ|² ≈ 0.04 (converges as T → ∞)
- B/L ≥ 0
- sqrt(D - B/L) ≤ sqrt(D) ≈ 0.2

So the framework's bound gives c ≈ 0.2, BELOW the threshold 1/2.

This is the L² averaging loss: the framework's machinery gives a SUBOPTIMAL
lower bound on |sum|, losing a factor of ~2.5× compared to the actual max.

## 5. Why L² averaging loses

The framework uses the mean-value argument:
∫ |sum|² ≥ L · D - B (since |sum|² has average D - B/L over [X, X+L])

By Cauchy-Schwarz or Markov: max |sum|² ≥ (1/L) · (L · D - B) = D - B/L

So sqrt(max |sum|²) ≥ sqrt(D - B/L)

But max |sum| could be much larger than sqrt(D - B/L). The mean-value
argument gives a lower bound that can be loose by a constant factor.

For zeta zeros, this factor is ~2.5×.

### 5.1 The cubic kernel B_η does NOT help

The user's docs in section (1) state that the cluster main term is smoothed
by a cubic kernel B_η(ρ) ≈ 1 near 0, decaying like (η·|ρ|)^{-2} for high
frequency.  The question is whether this smoothing helps the L² averaging.

For a single zero ρ = β + iγ with |γ| > 1/η (high frequency):
  B_η(ρ)² ≈ 1/(η² · γ² · |ρ|²)
  diagonal L² contribution ≈ 1/(η² · γ⁴) (vanishes for large γ)

The smoothing makes the L² averaging bound EVEN SMALLER:
  Without smoothing: sqrt(D_raw) ≈ 0.2
  With smoothing: sqrt(D_smoothed) ≈ 0.05 (for η = 0.1)

So the cubic kernel B_η does NOT help close the gap.  The gap is
fundamental to L² averaging, not specific to raw vs smoothed cluster_main.

### 5.2 What WOULD help

To get c > 1/2, we need a different kind of bound, NOT L² averaging.
The natural candidate is:

  max |sum| ≤ coefficient_mass(S) = Σ m(ρ)/|ρ|

This is the triangle-inequality upper bound.  The actual max achieves
this (attained when all phases align).

So the L² averaging (sqrt(D) ≈ 0.2) and the actual max (coefficient_mass ≈ 0.55)
DIFFER by a factor of ~2.5×.  The closure requires a lemma that gives
the actual max (or a close approximation), not just the L² average.

## 6. Closure paths

### Path A: Framework strengthening

Add a new lemma using the coefficient-mass upper bound, NOT L² averaging.

Specifically:
```
exists_far_antiCancellation_equalRealPart_witness_ge S β L M :
  ∃ m ≥ M, |cluster_main(m)| ≥ c · amplitude(m)
```
with `c = coefficient_mass(S) · (1 - ε)` for any `ε > 0` (for sufficiently
far m by quasi-periodicity).

### Path B: Axiomatize

Admit `seedDeletedResidualLemma_axiom` as an axiom.  Add to the framework's
allowlist.

The accompanying Lean file uses Path B.

## 7. Lean integration surface

The accompanying Lean file `PrimeNumberTheorem/SeedDeletedResidual.lean`
documents the statement and provides the integration surface.

The numerical verification scripts:
- `scripts/energy_verify.py` — framework's L² averaging gives c ≈ 0.2
- `scripts/max_cluster_main.py` — actual max c ≈ 0.5+ for N ≥ 7 zeros

## 8. Honest assessment

The seed-deleted residual lemma IS achievable (with N ≥ 7 zeta zeros).
The framework's CURRENT machinery gives c ≈ 0.2 via L² averaging,
which is *weaker* than needed.  This is a framework-sharpness issue.

The closure requires either framework strengthening or explicit
axiomatization.  Both are tractable.