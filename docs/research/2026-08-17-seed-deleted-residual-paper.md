# The seed-deleted residual lemma: a paper-style analysis

This is the "independent paper" that the chain
`seed-deleted residual lemma → sharp transfer → omega witness` requires
as its single non-trivial mathematical input.  It documents the precise
statement of the lemma, the obstructions to its proof, the framework's
existing machinery (which is *insufficient* for `c > 1/2`), and the
genuine mathematical gap.

## Status

The lemma is **not provable** from existing framework machinery or
classical results.  The proof requires a genuinely new result that is
not in the literature.

---

## 1. Background and notation

### 1.1 The explicit formula

For `x ≥ 1` and any nontrivial zero `ρ = σ + iγ` of ζ, write

```
pntRelativeZeroContribution x rho =
  -analyticOrderNatAt riemannZeta rho * x ^ (rho - 1) / rho
```

### 1.2 The framework's cluster main term

For a *finite* set `S ⊂ ℂ` of zeta zeros, the *cluster main term* is

```
clusterMainTerm S x
  = (Σ_{rho in S} pntRelativeZeroContribution x rho).re
```

### 1.3 The target amplitude

```
targetZeroPowerAmplitude β x = x ^ (β - 1)
```

### 1.4 The cluster-main witness

The sharp-constant transfer consumes the hypothesis

```
ClusterMainWitness β c S :=
  c > 1/2 ∧
  ∀ M, ∃ m ≥ M, c · m^(β-1) ≤ |clusterMainTerm S m|
```

---

## 2. The seed-deleted residual lemma (precise statement)

**Definition 2.1 (Seed-deleted residual lemma).** Let `β₀ ∈ (1/2, 1)` and
`λ > 1`.  The *seed-deleted residual lemma* asserts the existence of a
constant `c > 1/2` and a finite cluster `S` of nontrivial zeta zeros, all
lying on the line `Re ρ = β₀`, such that `ClusterMainWitness β₀ c S` holds.

---

## 3. The numerical reality of the gap

I computed the relevant quantities numerically for the equal-real-part
zeta-zero package (assuming RH, so `Re ρ = 1/2`):

```
T      N    coef_mass    D         sqrt(D)
50     20   0.582        0.0214    0.146
100    58   1.117        0.0290    0.170
200    138  1.804        0.0339    0.184
500    396  2.947        0.0375    0.194
1000   871  3.989        0.0391    0.198
5000   5398 7.003        0.0408    0.202
```

The "D" column is `Σ m(ρ)²/|ρ|²` over the package (with conjugates),
which is exactly the diagonal energy in
`actualEqualRealPartZeroPackageEnergy`.  The "sqrt(D)" column is the
coefficient that the framework's
`hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster` actually
delivers (asymptotically in L).

**The framework's machinery delivers c ≈ 0.2, NOT c > 0.5.**

To obtain `c > 0.5`, we would need `sqrt(D - B/L) > 1/2`, i.e.,
`D - B/L > 1/4 = 0.25`.  But `D` converges to ≈ 0.04 as `T → ∞`.  Even
with `L → ∞` (so `B/L → 0`), `D - B/L ≈ 0.04 < 0.25`.

**The framework's machinery is fundamentally insufficient** for the
cluster-main witness with `c > 1/2`.  This is the precise mathematical
gap.

---

## 4. The obstruction (more precisely)

The sharp-constant transfer's loss term is `(1/2) · amplitude`.  So the
cluster-main coefficient `c` must exceed `1/2` to deliver a positive
result.  But:

1. **Single-zero upper bound.** For `S = {ρ₀}`,
   `|cluster_main(m)| ≤ m^(β-1) / |ρ₀|`.  The smallest nontrivial
   zero has `|ρ₀| ≈ 14.13`, so `c ≤ 0.071`.  Insufficient.

2. **Multi-zero coefficient-mass upper bound.** For `S` containing
   zeros with `Re ρ = β₀`, the cluster-main is bounded by the
   coefficient mass `Σ m(ρ)/|ρ|` multiplied by `m^(β-1)`.  For the
   equal-real-part package with `T = 100`, coefficient mass ≈ 1.12
   (with conjugates).  This is the *upper* bound; the *actual* value
   depends on phases.

3. **Framework's L² lower bound.** The framework's machinery
   (`hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster`)
   delivers a far-point witness with coefficient
   `sqrt(actualEqualRealPartZeroPackageEnergy)`.  This is bounded
   above by `sqrt(D) ≈ 0.2`.  NOT > 1/2.

4. **Worst-case LOWER bound from Weyl equidistribution.** For generic
   phases, the cluster-main at a "random" point `m` is approximately
   `sqrt(D) ≈ 0.2`.  This is what the framework essentially delivers.

To exceed `c = 1/2`, we would need *constructive interference* in the
phases, which is not provable from known results.  This is the genuine
gap.

---

## 5. Reduction to known results (none useful)

### 5.1 Ingham-Ford

Classical oscillation results (Ingham 1932, Ford 2008) give:

```
lim sup_{x → ∞} |ψ(x) - x| / (x · exp(-c' log x / log log x)) > 0
```

This delivers a far-point witness at the *outer* Chebyshev scale but
does **not** factor through the cluster-main witness.  The bridge is
not available.

### 5.2 Under RH

Assuming RH, all zeros lie on `Re ρ = 1/2`.  The framework's machinery
becomes more concrete.  But the coefficient-mass / D analysis above
remains valid: the L² lower bound is at most `sqrt(D) ≈ 0.2`.

---

## 6. The complete argument (gap analysis)

The seed-deleted residual lemma is **not provable** from existing
framework machinery.  Specifically:

1. **Framework's `hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster`**
   delivers coefficient `sqrt(actualEqualRealPartZeroPackageEnergy)`.

2. **`actualEqualRealPartZeroPackageEnergy = D - B/L`** where
   `D = Σ m(ρ)²/|ρ|² ≈ 0.04` (regardless of `T`).

3. **`sqrt(D - B/L) ≤ sqrt(D) ≈ 0.2`**, which is **strictly less
   than 1/2**.

4. To reach `c > 1/2`, we would need a different *lower* bound on the
   cluster-main term, specifically one that captures constructive
   interference in the phases.

None of the existing framework machinery provides this.  The classical
Ingham-Ford result gives the *outer* Chebyshev oscillation but not
through the cluster-main witness.

---

## 7. What would close the gap

A genuine proof of the seed-deleted residual lemma would require one of:

**(a) An explicit anti-cancellation bound for the cluster main term.**
Show that for some specific cluster `S` and specific point `m`,
`|Σ_{ρ ∈ S} m(ρ) e^{iγ log m}/ρ| > 1/2`.  This requires detailed knowledge
of the actual zeta zero locations and their phase alignment.

**(b) A new structural oscillation bound.**  Show that `|ψ(x) - x|`
exceeds some specific multiple of `x^{β₀ - 1}` at every `x` in a long
interval — not just at *some* `x` as Ingham-Ford delivers.  This is a
stronger oscillation claim than classical results.

**(c) A Siegel-type mass formula.**  Show that the explicit formula's
zero contribution has a *signed* lower bound sufficient to control the
cluster main term.  This is in the spirit of Montgomery-Vaughan but for
the explicit formula itself.

None of (a), (b), (c) is in the current literature.

---

## 8. Honest assessment

The seed-deleted residual lemma is a **genuine mathematical gap**, not a
Lean engineering task.  The framework's other layers (Carlson
summability, explicit-formula decomposition, layer-budget transfer)
are all clean and well-implemented.  The single external input the
framework requires is the lemma above.

The most realistic path forward is one of:

1. *Admit the lemma as an external axiom*, document its role, and
   complete the framework mechanically.  This is the "engineering
   surface" answer.

2. *Reduce the lemma to a known result*.  As §5 documents, classical
   results do not deliver the lemma.  A genuine reduction would
   require new ideas.

3. *Prove the lemma* via a new technique.  As §3 documents, the
   obstruction is non-trivial, and the proof would constitute new
   research.

---

## 9. Lean integration surface

The accompanying Lean file `PrimeNumberTheorem/SeedDeletedResidual.lean`
documents the statement and provides a clean integration surface for the
lemma once it is supplied.

The numerical verification script `scripts/energy_verify.py` confirms
the framework's machinery gives `c ≈ 0.2`, not `c > 1/2`.

---

## 10. Conclusion

The seed-deleted residual lemma is a **genuine mathematical gap**.  My
earlier claim that it was provable from framework machinery was based
on a misreading of the energy computation.  The framework's machinery
gives `c ≈ sqrt(D) ≈ 0.2`, which is below the threshold `c > 1/2`
required by the sharp-constant transfer.

The accompanying Lean file formalizes the lemma as a statement of record.
The accompanying analysis document (`2026-08-17-seed-deleted-residual-analysis.md`)
explains the precise obstructions at the level of a research paper.

This is the best that can be done without genuine new research.
We acknowledge the gap honestly rather than papering over it.