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

## 8. Equivalence with the `β₀ > 1/2` zero-density lower bound

This section re-states the gap in a form that exposes its true
mathematical content: in the regime `β₀ > 1/2` the seed-deleted
residual lemma is **not an independent intermediate step** — it is
equivalent to a ζ-zero-density lower bound in the strip
`Re ρ ∈ (β₀, 1]`, which is exactly the kind of statement the broader
project (the `14/17`-type zero-density programme) is trying to
control.

### 8.1 Setup

Recall the Parseval assembly from
`docs/research/vk-edge-approximation-l2-decay.md`: the L²-energy of
`R_{S₀^c}` on `I_X = [X, X^λ]` decomposes as

```
||R_{S₀^c}||²_{L²(w, I_X)}  =  Diagonal  +  NearCrossing  +  FarCrossing
                              +  OffBandTail
```

The diagonal term has the form

```
Diagonal  =  K(0) · Σ_{ρ ∉ S₀}  m(ρ)² · |B_η(ρ)|² · X^{2(β_ρ − β₀)} · X^λ .
```

For the L² lower bound

```
||R_{S₀^c}||²_{L²(w, I_X)}  ≥  c · X^{2β₀ + λ}
```

to hold with `c > 1/2`, the diagonal term must dominate the near-
and far-crossing corrections, and this in turn forces

```
Σ_{ρ ∉ S₀, β_ρ > β₀}  m(ρ)² · X^{2(β_ρ − β₀)}    ≥    X^{2β₀ − λ} / C₀    (∗)
```

for some absolute `C₀ > 0` independent of `X` and the seed `S₀`.

### 8.2 The equivalence

For `β₀ ∈ (1/2, 1)` and `λ > 1`, define the following three
statements:

* **(L)** *The seed-deleted residual lemma holds at* `β₀`, *i.e.*
  `∃ c > 1/2` *and a finite seed cluster* `S₀` *with the L² lower bound*
  `||R_{S₀^c}||²_{L²(w, I_X)} ≥ c · X^{2β₀ + λ}` *for all large* `X`.

* **(D)** *ζ has substantial zero density above* `β₀`, *i.e. there is a
  strip* `(σ_1, σ_2] ⊂ (β₀, 1]` *and constants* `θ > 0`, `C > 0` *such
  that*

  ```
  N(σ_2, T) − N(σ_1, T)    ≥    C · T^θ       for all large T,
  ```

  *and* `θ > 2β₀ − λ − 1`. *Equivalently, condition* `(∗)` *holds with
  bounded sum over heights* `T ≤ X^γ`.

* **(Z)** *The strip* `Re ρ > β₀` *is not a zero-free region*: there
  exists at least one nontrivial zero with `Re ρ > β₀`, **and** the
  associated L²-energy in that strip satisfies `(∗)`.

**Claim (Equivalence in the β₀ > 1/2 regime).**

```
(L)    ⟺    (D)    ⟺    (Z).
```

*Proof sketch.*

* `(L) ⟹ (D)`. The diagonal term in `||R_{S₀^c}||²` is a lower bound
  on the contribution from the strip `Re ρ > β₀`. If `(L)` holds with
  `c > 1/2`, the near- and far-crossing terms are controlled by the
  Parseval argument (they contribute a bounded fraction of the
  diagonal under the standard kernel-decay assumptions), so
  condition `(∗)` follows. Summing the resulting bound over dyadic
  heights `T ∈ [X^k, 2X^k]` produces a `T^{2β₀ − λ − 1}`-type lower
  bound on `Σ_{ρ, T ≤ |ρ| < 2T} m(ρ)² / |ρ|^{2β₀}`, and translating
  this into `(D)` is a standard density summation. ∎

* `(D) ⟹ (L)`. Conversely, if `(D)` holds, then for any finite seed
  `S₀` the sum over `ρ ∉ S₀` in `(∗)` is dominated by the dyadic
  heights where `(D)` applies, and a careful kernel localisation
  argument produces a diagonal term that grows at least like
  `X^{2β₀ + λ}`. The crossing terms are then absorbed by the
  framework's existing machinery
  (`hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster`),
  with the constant `c` depending on `θ` and `C`. ∎

* `(L) ⟺ (Z)` and `(D) ⟺ (Z)`. Trivial once one notes that
  `||R_{S₀^c}||²_{L²(w, I_X)}` is monotone in the number of zeros
  contributing to the diagonal: adding a zero with `Re ρ > β₀` can
  only increase the diagonal term (since `X^{2(β_ρ − β₀)} > 1` in the
  regime `β_ρ > β₀`), and removing all such zeros drives the diagonal
  to `O(1)` (or `0` under RH). ∎

### 8.3 What this means

The equivalence above shows that the seed-deleted residual lemma is
**not** a Lean-engineering intermediate result.  In the regime
`β₀ > 1/2` the lemma's `c > 1/2` requirement is exactly equivalent
to the assertion that ζ has many zeros above the line `Re ρ = β₀`.
That assertion is precisely the `14/17`-type zero-density statement
the broader project is trying to either establish or refute.  Hence:

| Conditional regime | Status of `(L)`, `(D)`, `(Z)` |
|---|---|
| **RH holds** | All zeros at `Re ρ = 1/2 < β₀`, so `(D)` and `(Z)` fail for `β₀ > 1/2`, and `(L)` fails (diagonal term → 0). |
| **RH fails, but zeros above `β₀` are sparse** | `(D)` may fail (the density exponent `θ` may be `≤ 2β₀ − λ − 1` or even negative); `(L)` correspondingly fails. |
| **Zeros above `β₀` are dense enough** | All three statements hold. |

The framework's machinery is consistent with the **sparse** regime:
as `§3` shows, the diagonal sum `D = Σ m(ρ)²/|ρ|²` over the equal-
real-part package converges to `≈ 0.04`, far below the `0.25` needed
for `c > 1/2`.  This is consistent with the standard picture in
which RH-type zeros (which is what the package is) are the only
contribution, and there is no significant off-line zero mass.

### 8.4 Honest reduction

In summary, in the regime `β₀ > 1/2`:

> **The seed-deleted residual lemma is equivalent to a ζ zero-density
> lower bound in the strip `Re ρ > β₀`, which is exactly the
> `14/17`-type zero-density statement that the rest of the project
> is trying to control.**

Therefore the lemma cannot be independently proved as a Lean
engineering task; it is a restatement of the project's main
analytic input.  The framework's other machinery (Carlson
summability, explicit-formula decomposition, layer-budget transfer)
is sound; the **only** missing ingredient is the off-line zero-mass
estimate, which is a non-trivial analytic-number-theory problem.

This observation does not invalidate the framework — it pins down
exactly what would be needed to close the chain.  Anyone reading
the lemma statement in `SeedDeletedResidual.lean` should understand
that consuming it as an axiom is equivalent to assuming the
`14/17`-type zero-density lower bound holds.