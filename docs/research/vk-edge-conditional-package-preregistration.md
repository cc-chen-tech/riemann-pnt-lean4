# VK-edge conditional package (envelope-local): preregistration (revised)

## Scope of this phase

Step 1 baseline check:
`32cd327` in `research/vk-edge-pi-over-two` is docs-only and has no required code artifacts to cherry-pick into
this branch.

This phase targets a **half-isolated** input-to-output bridge under an explicit finite-envelope
window.

The task is now to show, in Lean, that:

- finite equal-real-part family control on `equalRealPartZeroPackage T h.rho0.re`,
- finite-`M` spectral lower input,
- explicit uniform remainder control on the log-window,
- and coefficient normalisation

implies

`∃ x ∈ [Y, Y^C], |ψ₀(x)-x| ≥ (π/2+δ) * x^β / max(1,‖ρ₀‖)`.

## Fixed conditions used in `HalfIsolatedEnvelopeInput`

1. `hY : 1 < Y`, `hC : 1 < C`, and `hWindow : log Y < log (Y^C)`.
2. `hFiniteVertical : (equalRealPartZeroPackage T ρ₀.re).card ≤ M`.
3. `hSpectralLower` inequality on that window:

```text
∑_{ρ ∈ equalRealPartZeroPackage} |a_ρ|^2 - offDiag / (log(Y^C)-log Y)
≥ (π/2 + δ + ε)^2 * |a_{ρ0}|^2
```

4. `hRemainderWindow` inequality on the same interval:

```text
|zeroPackageExplicitFormulaRemainder(y)| ≤ ε * e^{β y} * |a_{ρ0}|,
	y ∈ [log Y, log(Y^C)]
```

5. `hCoeffLower`:

```text
1 / max(1, ‖ρ₀‖) ≤ |a_{ρ0}|,
  a_{ρ0}=(analyticOrderNatAt riemannZeta ρ₀:ℂ) / ρ₀
```

## What is proved here

- In `PrimeNumberTheorem.VKEdgeConditionalPackage`:
  - `halfIsolatedEnvelopeBridge` is now a theorem (not axiom).
  - It composes:
    - `exists_mem_Ioo_sqNorm_equalRealPartZeroPackageContribution_ge`,
    - explicit spectral lower bound (`hSpectralLower`),
    - explicit remainder bound on window (`hRemainderWindow`),
    - transfer inequality (`norm_zeroPackage_sub_norm_remainder_le_norm_chebyshev...`).

- `VKEdgeConditionalPackageContract` now calls this theorem directly for the half-isolated branch.

- `VKEdgeConditionalPackageContract` deliberately has no clustered contract theorem in this branch.

## Closed/open status

- `half-isolated`: branch closed under explicit assumptions listed in this file.
- `clustered`: remains blocked and intentionally not instantiated as contract theorem (pure blocker documentation only).
