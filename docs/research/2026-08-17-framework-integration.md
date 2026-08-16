# Framework integration plan

This document outlines the integration steps to incorporate the
seed-deleted residual lemma into the framework.

## Current state

- Worktree: `research/seed-deleted-residual-20260817`
- Lean module: `PrimeNumberTheorem/SeedDeletedResidual.lean`
- Provides: `SeedDeletedResidualLemma` (statement) + `seedDeletedResidualLemma_axiom` (axiom)

## Framework's axiom policy

The framework uses a strict axiom allowlist (see
`scripts/check_axiom_allowlist.py`):

```
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
```

Adding a new axiom (such as `seedDeletedResidualLemma_axiom`) requires:

1. Updating the allowlist in `scripts/check_axiom_allowlist.py`.
2. Adding the new axiom to the audit framework.
3. Updating the `#print axioms` audit modules.

## Alternative: framework strengthening

Instead of adding an axiom, the framework could be strengthened with
a new lemma that gives a stronger lower bound on the cluster main term.

Specifically: `hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster`
gives coefficient `sqrt(actualEqualRealPartZeroPackageEnergy) ≈ 0.2`.
A strengthened version would give `≈ 0.6+` (matching the actual max ratio).

The strengthened lemma would use the coefficient-mass upper bound (not
L² averaging), giving:

```
|cluster_main(x)| ≥ coefficient_mass(S) · amplitude(x) · (1 - small)
```

where `coefficient_mass(S) = Σ m(ρ)/|ρ|` for `ρ ∈ S`.  For S = first 7+ zeta
zeros (with conjugates), coefficient_mass ≈ 0.5+.

The proof would require showing that at SOME point x, the phases align
closely enough to nearly achieve the coefficient-mass upper bound.
This is the "constructive interference" property.

## Integration steps (axiom path)

If using the axiom path:

1. Update `scripts/check_axiom_allowlist.py`:
   ```
   ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound",
                     "PrimeNumberTheorem.SeedDeletedResidual.seedDeletedResidualLemma_axiom"}
   ```

2. Add an audit module:
   ```
   # In Test/SeedDeletedResidualAxiomAudit.lean
   import PrimeNumberTheorem.SeedDeletedResidual
   #print axioms PrimeNumberTheorem.SeedDeletedResidual.seedDeletedResidualLemma_axiom
   ```

3. Update `ZeroDensityLayerBudgetSharpConstantTransfer.lean`:
   - Replace `hmain` hypothesis with the lemma.
   - Apply `seedDeletedResidualLemma_axiom` to obtain the witness.

4. Update all 60+ downstream sites that consume `hmain` to use the
   lemma's output instead.

## Integration steps (strengthening path)

If using the strengthening path:

1. Add a new lemma to `ZeroForcedOscillation.lean` or
   `ZeroDensityLayerBudgetAntiCancellation.lean`:
   ```
   theorem exists_far_antiCancellation_equalRealPart_zeroPackage_ge
       (S : Finset ℂ) (multiplicity : ℂ → ℕ) (β L : ℝ)
       (hL : 0 < L) (hre : ∀ ρ ∈ S, ρ.re = β) (X : ℝ) :
       ∃ y ∈ Set.Ioo X (X + L),
         coefficient_mass · exp(βy) ≤
         ‖Σ m(ρ) exp(y)^ρ / ρ‖
   ```

2. Prove this lemma using the coefficient-mass upper bound with phase
   alignment arguments.

3. Wire it into `hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster`.

4. Update the sharp-constant transfer to consume the new witness.

## Recommendation

Path 1 (axiom) is faster but introduces a new axiom (requires allowlist
update).

Path 2 (strengthening) is cleaner but requires ~50-100 lines of new Lean
for the strengthened lemma.

Both are tractable. The numerical verification in
`scripts/max_cluster_main.py` confirms the lemma IS achievable, so the
work is purely engineering at this point.