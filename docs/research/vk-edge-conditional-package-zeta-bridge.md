# VK-edge conditional package: zeta/VK envelope bridge with clustered expansion checks

This note records bridge data needed for envelope-local finite packages in half-isolated and clustered modes.

## Baseline source check

Step 1 verification done against source branch commit:
`32cd327 (research/vk-edge-pi-over-two)`, which touches only `docs/research/*` and has no changes that must be
ported into the conditional-package code files (`PrimeNumberTheorem/*` or `docs/research/vk-edge-conditional-package-*`).

## Lean bridge statement (`halfIsolatedEnvelopeBridge`)

Given `h : HalfIsolatedEnvelopeInput`, the theorem proves

```lean
HalfIsolatedConclusion h
```
with
`HalfIsolatedConclusion h := ∃ x ∈ Icc Y (Y^C),
|ψ₀(x)-x| ≥ (π/2+δ) * (exp(ρ0.re * log x) / max 1 ‖ρ0‖)`.

## Inequalities used by the proof

- `h.hWindow : log Y < log (Y^C)` gives a non-empty log interval.
- `h.hSpectralLower` gives

```lean
(∑ |a_ρ|^2 - offDiagonalBound / (log(Y^C)-log Y)) ≥ (π/2+δ+ε)^2 * |a_{ρ0}|^2
```

- `h.hRemainderWindow` gives uniform remainder control

```lean
|zeroPackageExplicitFormulaRemainder y T rho0.re| ≤ ε * exp(ρ0.re*y) * |a_{ρ0}|,
∀ y ∈ Icc (log Y) (log(Y^C))
```

- `h.hCoeffLower` bridges target normalisation

```lean
1/max(1,‖ρ0‖) ≤ |a_{ρ0}|
```

The proof chain is:

1. `exists_mem_Ioo_sqNorm_equalRealPartZeroPackageContribution_ge`
   gives a point `y` with package squared lower bound.
2. `h.hSpectralLower` upgrades this to an explicit linear package lower bound
   with margin `(π/2+δ+ε)`.
3. `h.hRemainderWindow` and
   `norm_zeroPackage_sub_norm_remainder_le_norm_chebyshev...`
   transfer package dominance to `Δ(x)` dominance.
4. `h.hCoeffLower` converts coefficient to the final normalisation `max 1 ‖ρ0‖`.

## Clustered channel extensions (fifth-phase status)

1. **Window inclusion for recursive input transport.**

   `equalRealPartZeroPackage` is monotone in height:

```lean
theorem equalRealPartZeroPackage_mono
    {T U β : ℝ} (hTU : T ≤ U) :
    (↑(equalRealPartZeroPackage T β) : Set ℂ) ⊆
      (↑(equalRealPartZeroPackage U β) : Set ℂ)
```

   This gives the only reliable global transfer: frequency separation and Gram estimates already proved at height `T`
   transfer to the *same* selected package at higher heights, but they do not force additional frequencies.

2. **Clustered bridge from explicit pairwise gap.**

   `clustered_offDiagonalBound_le_pairwise_gap` gives

```text
offDiagonalBound(S,c,im) ≤ (2M/gap) * Σ|cρ|^2
```

under explicit gap + card bound. The theorem `clustered_spectralLower_from_gap` and
`clusteredEnvelopeBridge` are genuine Lean proofs from these inputs.

3. **BY-normalised tail control (strongest current condition).**

   The original `hRemainderWindow` only gives

```text
|R_Y(y)| ≤ ε · exp(β y) · |a_{ρ0}|.
```

To express a universal bound of the form `|R_Y(y)| ≤ ε_Y·B_Y`, where

```text
B_Y := exp(β y) / max(1, ‖ρ0‖),
```
one needs an additional coefficient upper bound

```text
|a_{ρ0}| ≤ K.
```

The current strongest Lean lemma is:

```lean
clustered_tailsum_byBY_scale (h : ClusteredEnvelopeInput) (K : ℝ)
  (hK : 0 ≤ K) (hCoeffUpper : |a_{ρ0}| ≤ K) :
  ∀ y ∈ Icc(log Y, log(Y^C)),
    |R_Y(y)| ≤ (ε · K · max 1 ‖ρ0‖) * B_Y
```

It is a concrete translation of `hRemainderWindow` into BY-scale, and it shows why no `o(B_Y)` claim is derivable from
the current inputs alone unless the extra coefficient upper hypothesis is supplied.

4. **Blocker/anti-model (non-extension).**

   Without `hCoeffUpper`, near-collision or repeated finite clusters can satisfy the current explicit clustered hypotheses
   but keep `|a_{ρ0}|` arbitrarily large, so the BY-scaled factor does not contract to `0`. This is recorded in the checklist below:
   clustered closure without extra input is not an automatic promotion theorem.

## Remaining explicit blocker inequalities (clustered side or stronger o(1) variants)

1. **clustered bridge** (not in this file yet): no formal clustered inversion theorem instantiated;
   blocked by missing clustered spectral recurrence/invertibility inequalities.

2. If one wishes to deduce `h.hRemainderWindow` directly from primitive contour terms,
   the missing explicit inequality is exactly:

```text
sup_{y∈I} | zeroPackageExplicitFormulaRemainder y T β₀ | ≤ ε * exp(β₀*y) * |a_{ρ0}|
```

uniformly on the chosen window.

3. If this inequality is only available as little-o notation, it must be converted into an
   effective `ε` bound that is fixed before the final `δ` loss step.

4. For the clustered route, an explicit BY-normalised form requires a supplementary coefficient upper input for `ρ0`, as above.

No RH, no `PrimeNumberTheorem` unproven assertions are used in the bridge statement.
