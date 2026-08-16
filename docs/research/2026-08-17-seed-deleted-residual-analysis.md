# Seed-deleted residual analysis: where the `c > 1/2` truly comes from

Status: honest analysis. The seed-deleted residual lemma is a genuine
mathematical gap. The companion paper
`2026-08-17-seed-deleted-residual-paper.md` and the verification script
`scripts/energy_verify.py` together demonstrate this.

## 1. Recap: where `c > 1/2` enters the chain

The sharp-constant transfer in `ZeroDensityLayerBudgetSharpConstantTransfer.lean`
takes an *explicit* hypothesis

```
hmain : HasFarNaturalPointTargetAmplitudeWitness
          (fun m => dynamicVisibleClusterPNTMain T S (m : ℝ))
          (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))
```

with `c > 1/2`, and produces a far-point target-amplitude witness on
`relativeChebyshevPsi0Error` with coefficient `c - 1/2 > 0`.

The hypothesis `hmain` is **never produced** anywhere in the framework.
It is an external input.  Every subsequent theorem in the layer budget
tree assumes it or weakens it further.

## 2. Numerical reality

For the equal-real-part zeta-zero package (RH assumed), the relevant
quantities are:

| T    | N (with conj) | coef_mass | D    | sqrt(D) |
|------|---------------| | | | |
| 50   | 20            | 0.58      | 0.021 | 0.146  |
| 100  | 58            | 1.12      | 0.029 | 0.170  |
| 200  | 138           | 1.80      | 0.034 | 0.184  |
| 500  | 396           | 2.95      | 0.038 | 0.194  |
| 1000 | 871           | 3.99      | 0.039 | 0.198  |
| 5000 | 5398          | 7.00      | 0.041 | 0.202  |

The "D" column is `Σ m(ρ)²/|ρ|²` over the package.  The "sqrt(D)"
column is the coefficient that the framework's
`hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster` delivers
(asymptotically in L).

**The framework delivers c ≈ 0.2, NOT c > 1/2.**

Even with `L → ∞` (so `B/L → 0`), `sqrt(actualEqualRealPartZeroPackageEnergy) → sqrt(D) ≈ 0.2 < 1/2`.

## 3. The framework's machinery (insufficient)

The framework already has:

1. `ZeroForcedOscillation.exists_mem_Ioo_sqNorm_equalRealPart_zeroPackage_ge`
   provides a pointwise L² lower bound at SOME point in `[X, X+L]`.

2. `ZeroDensityLayerBudgetAntiCancellation.exists_far_norm_equalRealPart_zeroPackage_ge`
   specializes this to a far-point form.

3. `ZeroDensityLayerBudgetActualZeroPackageFloorTransfer.actualEqualRealPartZeroPackageEnergy`
   gives the energy `D - B/L` explicitly.

4. `ZeroDensityLayerBudgetActualZeroPackageFloorTransfer.exists_far_norm_actualEqualRealPartZeroPackageContribution_ge`
   and
   `ZeroDensityLayerBudgetActualZeroPackageVisibleClusterTransfer.hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster`
   complete the chain to a `HasFarTargetAmplitudeWitness` on the
   cluster main term, with coefficient `sqrt(D - B/L)`.

The coefficient `sqrt(D - B/L)` is bounded above by `sqrt(D) ≈ 0.2`,
which is below `1/2`.

## 4. The obstruction

For `c > 1/2`, we need `D - B/L > 1/4`.  But:

- The diagonal `D = Σ m(ρ)²/|ρ|²` converges to ≈ 0.04 as the package
  grows.  This is a hard ceiling on the L² lower bound.
- The off-diagonal `B/L` is non-negative, so `D - B/L ≤ D < 1/4`.

To exceed `c > 1/2`, we would need a different kind of lower bound,
one that captures *constructive phase alignment* in the cluster main
term.  This is not available in the framework.

## 5. Why my earlier analysis was wrong

My earlier paper claimed `D ≈ π²/6 ≈ 1.64`.  This conflated `Σ 1/n²`
over positive integers (which is `π²/6`) with `Σ 1/|ρ|²` over zeta zeros
(which converges to ≈ 0.04).

The error is fundamental: zeta zeros are sparser than integers, and
their contributions `1/|ρ|²` for `|ρ| ≥ 14` are much smaller.

## 6. Honest conclusion

The seed-deleted residual lemma is a **genuine mathematical gap**.
The framework's machinery is insufficient to produce the `c > 1/2`
input.  The remaining work is not a finite arithmetic verification,
but rather requires a genuinely new result on the oscillation of the
explicit formula.

## 7. Recommendation

The most realistic path forward is one of:

1. *Admit the lemma as an external axiom*, document its role, and
   complete the framework mechanically.

2. *Reduce the lemma to a known result*.  As the paper documents,
   classical results do not deliver the lemma.  A genuine reduction
   would require new ideas.

3. *Prove the lemma* via a new technique.  This requires new research.

The accompanying Lean file `PrimeNumberTheorem/SeedDeletedResidual.lean`
documents the statement and integration surface.