# Seed-deleted residual analysis: where the `c > 1/2` truly comes from

Status: corrected analysis. The seed-deleted residual lemma IS
achievable with finite clusters of ≥ 7 zeta zeros, but the framework's
current machinery gives only c ≈ 0.2 (L² averaging loss).

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

## 2. Numerical reality (corrected)

For finite clusters of the first N zeta zeros (with conjugates),
the maximum of |cluster_main(x)|/amplitude is:

| N | max ratio | > 1/2? |
|---|-----------|--------|
| 1 | 0.14      | no     |
| 2 | 0.24      | no     |
| 3 | 0.32      | no     |
| 5 | 0.43      | no     |
| 7 | **0.53**  | **YES** |
| 10| **0.64**  | **YES** |
| 20| **0.88**  | **YES** |
| 30| **1.02**  | **YES** |

**The lemma IS achievable for N ≥ 7.** But the framework's current
machinery gives only c ≈ 0.2 (L² averaging loss).

## 3. Why the framework is weaker

The framework's `hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster`
delivers a witness with coefficient `sqrt(actualEqualRealPartZeroPackageEnergy)`,
which is bounded above by `sqrt(D) ≈ 0.2 < 1/2`.

This is because:
1. The energy `D - B/L` comes from L² averaging over `[X, X+L]`.
2. By Markov's inequality, this gives a lower bound on the maximum.
3. The factor `sqrt(D)/max ≈ 0.2/1.0 = 1/5` is the "L² averaging loss".

The framework's machinery does NOT capture the constructive phase
alignment that gives the actual maximum.

## 4. The gap (precise)

The gap is a **framework sharpness** issue, not a deep mathematical gap.

Specifically: the framework's L² averaging loses a factor of ~5×.  To
recover this factor, we need either:

* A new framework lemma using the coefficient-mass upper bound with
  explicit phase-alignment control, OR
* An explicit construction using known zeta zero locations.

Both are tractable.

## 5. Closure paths

### Path A: Framework strengthening

Add a new lemma (in the style of `hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster`)
that gives a stronger lower bound.

Estimated work: ~50-100 lines of Lean.

### Path B: Explicit construction

Take `S = {ρ : Re ρ = β₀, |Im ρ| ≤ T}` for `T ≥ 100`.  Axiomatically
state that there exists `x` with `|cluster_main(x)| > 0.5 · amplitude`.

Estimated work: ~20-30 lines of Lean (using the actual zeta zero
locations as axioms).

## 6. Recommendation

The most realistic path is Path B (explicit construction), since it
requires only the framework's existing machinery plus axioms for the
zeta zero locations.

The accompanying Lean file `PrimeNumberTheorem/SeedDeletedResidual.lean`
documents the statement and integration surface.

The numerical verification scripts:
- `scripts/energy_verify.py` — framework's L² averaging gives c ≈ 0.2
- `scripts/max_cluster_main.py` — actual max exceeds 1/2 for N ≥ 7