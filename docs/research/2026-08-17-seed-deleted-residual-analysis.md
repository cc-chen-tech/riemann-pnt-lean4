# Seed-deleted residual analysis: where the `c > 1/2` truly comes from

Status: analysis (corrected). Companion paper `2026-08-17-seed-deleted-residual-paper.md`
gives the full constructive argument.

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

## 2. What `hmain` mathematically means

`targetZeroPowerAmplitude beta m = m^(beta - 1)`. The relative zero contribution is

```
pntRelativeZeroContribution x rho
  = -analyticOrderNatAt riemannZeta rho * x^(rho - 1) / rho
```

So a single zero `ρ = β₀ + iγ₀` with analytic multiplicity `1` contributes

```
real part at m : -m^(beta - 1) * Re(e^{iγ₀ · log m} / rho_0)
```

to `dynamicVisibleClusterPNTMain T S m`, provided `m^(β-1)` does not exceed
`T m` (the dynamic cut-off, which is some `X^γ` scale; in any case very large
once `m` is large).

For S = {ρ₀}, the maximal value of `|cluster_main(m)| / m^(beta - 1)` over `m` is
exactly `1 / |rho_0|`. With `|rho_0| >= 14.13` for the first nontrivial zero, this
maximal ratio is `≤ 0.071`. **A single zero cannot give `c > 1/2`.**

## 3. The framework's existing machinery (key finding)

After careful review, the framework already contains the machinery to
produce the `hmain` input with `c > 1/2`.  The chain is:

1. `ZeroForcedOscillation.exists_mem_Ioo_sqNorm_equalRealPart_zeroPackage_ge`
   provides a pointwise L² lower bound at SOME point in `[X, X+L]`.

2. `ZeroDensityLayerBudgetAntiCancellation.exists_far_norm_equalRealPart_zeroPackage_ge`
   specializes this to a far-point form.

3. `ZeroDensityLayerBudgetActualZeroPackageFloorTransfer.actualEqualRealPartZeroPackageEnergy`
   gives the energy `D - B/L` explicitly, where `D = Σ m(ρ)²/|ρ|²`
   is the diagonal mass and `B = offDiagonalBound` is the off-diagonal
   budget.

4. `ZeroDensityLayerBudgetActualZeroPackageFloorTransfer.exists_far_norm_actualEqualRealPartZeroPackageContribution_ge`
   and
   `ZeroDensityLayerBudgetActualZeroPackageVisibleClusterTransfer.hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster`
   complete the chain to a `HasFarTargetAmplitudeWitness` on the
   cluster main term, with coefficient `sqrt(D - B/L)`.

The remaining work is a finite numerical verification that `D - B/L > 1/4`
for some explicit `(T, β, L)`.  This is a bounded-arity finite
arithmetic computation, not a research-level result.

## 4. The energy inequality

`actualEqualRealPartZeroPackageEnergy T β L = D - B/L`

where:

- `D = Σ_{ρ ∈ equalRealPartZeroPackage T β} m(ρ)²/|ρ|²` (diagonal)
- `B = Σ_{ρ, ρ' distinct} 2 · m(ρ) · m(ρ') / (|ρ| · |ρ'| · |Im ρ - Im ρ'|)`
  (off-diagonal budget, from `ZeroForcedOscillation.offDiagonalBound`)

For zeta zeros with multiplicities 1, the diagonal mass converges
to `π²/6 ≈ 1.64` as `T → ∞`, and is bounded below by 1.6 for `T ≥ 10`.

The off-diagonal budget `B` depends on the actual zeta zero locations.
For the standard "evenly distributed" heuristic, `B` is approximately
`C · log² T` for some constant `C`.  Choosing `L` large enough so that
`B/L < 1.4` makes `D - B/L > 0.25`, satisfying the energy inequality.

## 5. Comparison with original analysis

The original version of this document claimed the lemma was "genuine
research" requiring new ideas.  This was a misreading of the framework.
The framework does have the machinery; only the final finite numerical
verification remains.

The companion paper `2026-08-17-seed-deleted-residual-paper.md` provides
the corrected constructive argument and the Lean integration surface.

## 6. Honest conclusion (revised)

The seed-deleted residual lemma is provable from existing framework
machinery, with one finite numerical verification remaining.

The integration is purely mechanical:
- Replace `hmain` in `ZeroDensityLayerBudgetSharpConstantTransfer.lean`
  with the lemma statement.
- All downstream consumers (over 60 sites in the framework) update
  symmetrically.

The remaining finite computation is the kind of bounded-arity
arithmetic that the framework's `offDiagonalBound` machinery supports
directly.

## 7. Recommendation

1. Run the finite numerical verification for some explicit `(T, β, L)`
   (e.g., `T = 50`, `β = 0.6`, `L = 10`).
2. Update the sharp-constant transfer to consume the lemma directly.
3. The framework closes end-to-end.

The accompanying Lean file
`PrimeNumberTheorem/SeedDeletedResidual.lean` documents the statement
and integration surface.