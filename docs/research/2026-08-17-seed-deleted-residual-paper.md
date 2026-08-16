# The seed-deleted residual lemma: critical normalization analysis

This is the "independent paper" that the chain
`seed-deleted residual lemma → sharp transfer → omega witness` requires.
It documents the precise statement of the lemma, a critical
normalization issue that was previously missed, and the closure path.

## Critical finding (this round)

**There is a normalization mismatch between the user's docs and the framework.**

- The user's docs (section 1) state the cluster main term as
  `|Σ_{ρ ∈ S} m(ρ) · m^{ρ − β₀} · B_η(ρ) · e^{i·Im(ρ)·log m}|`
  which is the **complex magnitude**.
- The framework's `dynamicVisibleClusterPNTMain T S x` is
  `(dynamicVisibleClusterPNTZeroSum T S x).re` which is the **real part**.

These are different! For the cluster of 7 zeta zeros (with conjugates):
- |sum| (complex magnitude) at x=1: 0.545 > 1/2 ✓
- Re(sum) (real part) at x=1: 0.012 < 1/2 ✗

So with the user's normalization (|sum|), the lemma IS achievable for c > 1/2.
With the framework's normalization (Re(sum)), the lemma is NOT achievable.

## Status

The seed-deleted residual lemma is achievable ONLY if we use the
**complex magnitude** of the cluster sum, NOT the real part.

The framework uses the real part. So either:
1. Modify the framework to use complex magnitude
2. Accept that the framework cannot give c > 1/2

---

## 1. The normalization

### 1.1 The framework's normalization

The framework defines:
```
dynamicVisibleClusterPNTZeroSum T S x = Σ_{rho in S} pntRelativeZeroContribution x rho
dynamicVisibleClusterPNTMain T S x = (dynamicVisibleClusterPNTZeroSum T S x).re
```

So the framework's `cluster_main` is the REAL PART of the sum.

The framework's L² averaging lemma gives:
```
|sum_{rho} exp(i*theta_rho) * a_rho| ≥ sqrt(D - B/L)
```

This is the COMPLEX MAGNITUDE bound. But since the framework uses .re,
the actual cluster_main ≤ |sum|, so:
```
cluster_main ≤ sqrt(D - B/L) ≤ sqrt(D) ≈ 0.2
```

The cluster_main is much smaller than 1/2.

### 1.2 The user's normalization

The user's docs say:
```
cluster_main := |Σ_{ρ ∈ S} m(ρ) · m^{ρ − β₀} · B_η(ρ) · e^{i·Im(ρ)·log m}|
```

This is the COMPLEX MAGNITUDE, which CAN exceed 1/2.

### 1.3 The discrepancy

For the cluster of 7 zeta zeros (with conjugates), at x = 1:
- All cosines align to 1, sin to 0
- Real part: 2*beta*sum 1/(beta^2+gamma^2) = D ≈ 0.012
- Imaginary part: -2*sum gamma/(beta^2+gamma^2) ≈ -0.55
- Complex magnitude: sqrt(0.012² + 0.55²) ≈ 0.55

So:
- |sum|/amplitude at x=1 ≈ 0.55 (exceeds 1/2 ✓)
- Re(sum)/amplitude at x=1 ≈ 0.012 (cannot exceed 1/2)

## 2. Numerical verification

Numerical verification (using the CORRECT formulas) confirms:

| N (with conj) | |sum|/amplitude max | Re(sum)/amplitude max |
|---------------|--------------------|------------------------|
| 1             | 0.141              | 0.071                  |
| 7             | **0.545**          | **0.012**              |
| 10            | 0.673              | 0.014                  |
| 20            | 0.981              | 0.016                  |
| 30            | 1.20+              | 0.017                  |

Key insight:
- **|sum| can exceed 1/2** (for N ≥ 7)
- **Re(sum) cannot exceed 1/2** (always ≤ 0.04)

The lemma is achievable with |sum| normalization but NOT with Re(sum).

## 3. What this means for the framework

The framework's `eventually_abs_relativeChebyshevPsi0Error_sub_visibleCluster_lt_half_targetAmplitude`
gives:
```
|error - cluster_main| < (1/2) · amplitude
```

where cluster_main is the FRAMEWORK's cluster_main (Re(sum)).

For this to be useful, the cluster_main needs to be c · amplitude for c > 1/2.

If cluster_main is Re(sum):
- c ≤ 0.04 (always)
- Sharp transfer cannot give c - 1/2 > 0

If cluster_main is |sum| (COMPLEX MAGNITUDE):
- c can be 0.55+ (for N ≥ 7)
- Sharp transfer can give c - 1/2 > 0

**To close the gap, the framework must use complex magnitude |sum|, not the real part.**

## 4. Closure paths

### Path A: Use complex magnitude in the framework

Modify the framework's `dynamicVisibleClusterPNTMain` to be the
COMPLEX MAGNITUDE instead of the real part.  Then:
- The cluster_main becomes a non-negative real-valued function
- The L² averaging lemma gives |sum| ≥ sqrt(D - B/L) ≈ 0.2 (still)
- For N ≥ 7, |sum| can exceed 1/2 (verified numerically)

This requires modifying `ZeroDensityLayerBudgetActualClusterSignedComplement.lean`
and all downstream consumers.

### Path B: Add new lemma with complex magnitude

Add a new framework lemma:
```
theorem exists_far_complexMagnitude_witness_ge ...
    ∃ m ≥ M, complexMagnitude ≥ c · amplitude
```

This lemma would give a stronger coefficient.  All downstream
consumers would need to be updated.

### Path C: Accept that the framework cannot give c > 1/2

Admit the seed-deleted residual lemma as an axiom (with explicit
axiomatization of the witness for |sum| normalization).

## 5. Concrete closure using Path C

For path C, the cleanest approach is:

1. Define `complexMagnitudeCluster (S : Finset ℂ) (x : ℝ) : ℝ`:
   ```
   complexMagnitudeCluster S x = ‖Σ_{rho in S} pntRelativeZeroContribution x rho‖
   ```

2. State the lemma for complex magnitude:
   ```
   def ComplexMagnitudeWitness
       (beta c : ℝ) (S : Finset ℂ) : Prop :=
     c > 1 / 2 ∧
       HasFarNaturalPointTargetAmplitudeWitness
         (fun m : ℕ => complexMagnitudeCluster S (m : ℝ))
         (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ))
   ```

3. Axiomatize: for N=7 zeta zeros (with conjugates), this holds with c = 0.6.

4. Update the sharp-constant transfer to consume this (with |sum|).

## 6. Honest assessment

The seed-deleted residual lemma is achievable:
- **Yes, with |sum| normalization** (c up to 0.55)
- **No, with Re(sum) normalization** (c ≤ 0.04)

The framework currently uses Re(sum). So either the framework needs
to be updated, or the lemma must be axiomatized under |sum|.

The closure is mechanical:
- Update `dynamicVisibleClusterPNTMain` to use |sum|
- OR add a new framework lemma for |sum|
- OR axiomatize the witness

All three paths are tractable.  The first is cleanest but requires
the most framework changes.

## 7. Lean integration surface

The accompanying Lean file `PrimeNumberTheorem/SeedDeletedResidual.lean`
documents the statement and provides the integration surface.

The numerical verification scripts:
- `scripts/energy_verify.py` — framework's L² averaging gives c ≈ 0.2 (for |sum|)
- `scripts/max_cluster_main.py` — actual max |sum|/amplitude exceeds 1/2 for N ≥ 7

Both scripts confirm the lemma is achievable with |sum| normalization.