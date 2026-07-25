# VK-edge conditional package (envelope-local): preregistration (stage-5 update)

## Scope baseline

Step 1 baseline check:
`32cd327` in `research/vk-edge-pi-over-two` is docs-only and introduced no required code artifacts for this branch.

The current stage records a closed half-isolated bridge and a closed clustered bridge under explicit finite-window hypotheses, then isolates the unresolved global-expansion clause (recursion to a new higher cluster/window).

## Fixed inputs retained from code

### Half-isolated route

1. `hY : 1 < Y`, `hC : 1 < C`, and `hWindow : log Y < log (Y^C)`.
2. `hFiniteVertical : (equalRealPartZeroPackage T ρ₀.re).card ≤ M`.
3. Spectral inequality `hSpectralLower` on `I = [log Y, log (Y^C)]`.
4. Remainder bound `hRemainderWindow`:

```text
|zeroPackageExplicitFormulaRemainder(y)| ≤ ε * exp(ρ₀.re * y) * |a_{ρ0}|
```

5. Coefficient normalisation:

```text
1 / max(1, ‖ρ₀‖) ≤ |a_{ρ0}|,
 a_{ρ0}=(analyticOrderNatAt riemannZeta ρ₀:ℂ)*ρ₀⁻¹
```

### Clustered route (explicit nondegeneracy and tail transfer)

1. Fixed window family with bounded cardinality in `equalRealPartZeroPackage`.
2. Global gap assumptions (`hClusterFrequencyGap`, pairwise gap).
3. Explicit surrogate spectral inequality `hClusterGapLower`.
4. The same uniform remainder bound and coefficient normalisation as in half-isolated.
5. Additional practical BY-scale tail control lemma now proved as

```text
|R_Y(y)| ≤ (ε * K * max(1,‖ρ₀‖)) * (exp(ρ₀.re * y) / max(1,‖ρ₀‖))

```

under an extra explicit upper input `|a_{ρ0}| ≤ K`.

## Closed status

- [x] `halfIsolatedEnvelopeBridge` is a genuine theorem.
- [x] `clusteredEnvelopeBridge` is a genuine theorem via pairwise-gap reduction.
- [x] `equalRealPartZeroPackage_mono` proved for recursive window comparisons: nontrivial zeros with fixed real part do not disappear as `T` increases.
- [x] `clustered_tailsum_byBY_scale` proved as strongest explicit BY-normalised tail step from current assumptions plus `|a_{ρ0}| ≤ K`.

## Unresolved recursion blocker

- [ ] The branch does not yet contain an automatic theorem that a bounded-cluster bridge at height `T` implies a strict new isolated contribution (new zero or non-overlap window) at higher heights. This requires an external zeta/VK expansion criterion beyond the current cluster package fields.

## Blocking inequalities now explicit

- `|a_{ρ0}|` remains lower-bounded by `1 / max(1,‖ρ₀‖)` but is not upper-controlled in `ClusteredEnvelopeInput`.
- Therefore `o(B_Y)` for a fixed `B_Y = exp(ρ₀.re y)/max(1,‖ρ₀‖)` is not derivable from current inputs alone.
- Any recursion claim needs a separate expansion hypothesis (e.g. coefficient upper control, non-recurrence of finite clusters, or explicit new non-overlap window guarantee).
