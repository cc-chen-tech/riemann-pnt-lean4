# VK-edge conditional package: explicit half-isolated bridge inequalities

This note records the current bridge from an envelope-local finite package to a local oscillation inequality.

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

No RH, no `PrimeNumberTheorem` unproven assertions are used in the bridge statement.
