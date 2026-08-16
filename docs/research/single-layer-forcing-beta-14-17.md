# Single-layer forcing: partial exclusion for beta > 14/17

## Status

Route specification replacing the withdrawn directed windowed detector
(`L3-defect-record.md`) as the immediate target.  This is a partial
result: it excludes non-trivial zeros with `Re rho > 14/17 = 0.8235...`,
not all of `(2/3, 1)`.  All analytic pieces exist in the current
mechanism family; no new mechanism is required.

## The argument (one layer, no iteration)

Fix a counterfactual seed `rho_0`, `beta = Re rho_0 > 14/17`.  Fix
`sigma in (2/3, beta)` and the cubic design parameters (`lambda`, `gamma`,
`theta = 0`).  The coherent window-energy forcing (the F_R/F_L budget of
the cubic design, section 3) gives: if the `sigma`-right zero count in the
height window is at most `M`, the tail energy is at most

```text
X^(2 lam sigma + lam + gamma (q(sigma) - 2)) * M * log^O(1)
```

while the seed energy is `X^(2 lam beta + lam - 2 gamma)`.  Contradiction
with the oscillation witness forces

```text
N(sigma, X^gamma) >= c X^(2 lam (beta - sigma) - gamma q(sigma)) * log^-O(1),
```

i.e. an exponent `e_M = 2 lam (beta - sigma) - gamma q(sigma)` relative to
`X`, or `e_M / gamma` relative to the height `T = X^gamma`.  With the
optimal `gamma -> g = lam (1 - beta)` and `sigma -> 2/3+`:

```text
e_M / gamma = 2 (beta - 2/3) / (1 - beta) - 8/9.
```

This exceeds the Carlson exponent `q(sigma) = 8/9` exactly when

```text
2 (beta - 2/3) > 2 gamma q(sigma)   with gamma -> g = lam (1 - beta),
i.e.  beta - 2/3 > lam (1 - beta) * 8/9   (sigma -> 2/3+),
```

with exact-fraction solutions `beta > (6 + 8 lam)/(9 + 8 lam)`:

| lambda | threshold |
|--------|-----------|
| 1 (limit) | 14/17 = 0.8235 |
| 1.01 | 352/427 = 0.8244 |
| 1.1  | 74/89 = 0.8315 |

The `lambda -> 1+` limit is 14/17; a fixed `lambda > 1` raises the
threshold slightly (the window-length exponent cancels in the energy
ratio, but `gamma = lam (1 - beta)` carries the factor into the density
comparison).  At `beta = 0.85` the exponent margin is still positive for
every `lambda < 1.22`.

By the proved Mellin–Landau backend
(`psiPowerErrorBound_excludes_riemannZeta_zero_right`), the resulting
`psi` power bound excludes every zero with `Re > sigma'` for any
`sigma' in (sigma, beta)`, hence every seed with `beta > 14/17`.

## Lean dependencies (all present or in the assembly PR)

1. cubic design F_R/F_L budget: `ZeroDensityLayerBudget*` family
   (worktree `actual-cubic-two-height-l2-tail`) — the tail bound with the
   `X^(-1/20)` fixed-grid margin;
2. Carlson majorant: proved on `main`
   (`carlson_zeroDensity_isBigO`);
3. the single-window contradiction assembly:
   `disjointWindowFamily_carlson_contradiction`
   (`ZeroDensityAmplificationAudit`, in PR #466) — a one-layer instance of
   the iterative contradiction with `depth = 1`;
4. Mellin–Landau backend: proved on `main`.

## Work plan

1. Port/reuse the cubic tail theorem (item 1) as the forcing input.
2. Prove the one-layer lower count for `N(sigma, X^gamma)` (the F_R/F_L
   contradiction in counting form).
3. Instantiate `disjointWindowFamily_carlson_contradiction` with
   `depth = 1` to obtain `False` from a seed with `beta > 14/17`.
4. Close with the Mellin–Landau backend to obtain the exclusion theorem
   `Re rho > 14/17  ==>  contradiction`, stated as
   `∀ ρ, IsNontrivialZero ρ → ρ.re ≤ 14/17`.

## Status of the full objective

The full `Re > 2/3` objective remains open: the strip
`(2/3, 14/17]` still needs either the directed mechanism (blocked, see
`L3-defect-record.md`) or a strictly better capacity model.  This route
delivers the first unconditional partial theorem and keeps the gate
contract (#467) as the container for the full statement.

## Threshold improvement analysis (2026-08-16)

1. **Ingham density** (exponent `3(1-σ)/(2-σ)`, smaller than Carlson's
   `4σ(1-σ)` for `σ > 2/3`): the contradiction threshold becomes
   `β > 17/21 ≈ 0.8095` (exact fractions: `β - 2/3 > (3/4)(1-β)`).
   NOT available on main (only `carlson_zeroDensity_isBigO` is proved);
   proving an Ingham-type density is a self-contained classical target
   that would improve this route's threshold.
2. **Guth–Maynard** (`30/13 (1-σ)` for `σ ≥ 3/4`): threshold
   `β > 69/82 ≈ 0.8415` — worse than 14/17, because the `σ ≥ 3/4`
   restriction raises the optimal σ; not helpful.
3. **Naive orthogonal capacity** (per-zero diagonal, no density input):
   gives `M ≤ X^(2(β-σ))` and, against the linear count `N(T) ~ T log T`,
   the threshold `β > 0.785` — better, BUT the cross terms need pairwise
   separation of the window zeros by a constant, which no mechanism
   supplies (window zeros can cluster at spacing `1/log T`).  Confirmed
   dead end, consistent with the fixed-gap obstruction.
4. Conclusion: within the proved-on-main density family (Carlson), 14/17
   is the optimal single-layer threshold; the strip (2/3, 14/17] remains
   the open part of the full objective.

## Boundaries

Specification only; the numeric threshold 14/17 is an exact-fraction
computation, the analytic pieces are the existing proved modules.
