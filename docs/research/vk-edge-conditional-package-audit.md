# VK-edge conditional package: audit (half-isolated vs clustered blockers)

## Current audit status

The following is a strict audit record of what is **assumed**, what is **proved** in
this branch, and what is currently **blocking**.

## Baseline source check

`32cd327` (source branch `research/vk-edge-pi-over-two`) has been checked and is docs-only; no changes from that commit were
ported into this branch's theorem code.

This branch is conditional. It does not claim a new RH consequence, and it does not
replace any unproved envelope lemmas with unconditional zeta statements.

## Proven (within repo context)

- `PrimeNumberTheorem.ZeroForcedOscillation` and related files provide:
  - finite equal-real-part package algebra,
  - off-diagonal mean-square expansion and bounds,
  - frequency-sum structure needed by fixed-\(M\) spectral statements.
- `docs/research/vk-edge-pi-over-two-proof-record.md` gives an explicit
  fixed-\(M\) spectral gap \(L_M > \pi/2\) under the admissible finite-class
  assumptions.

## Not proved in this branch (required by block list)

### Half-isolated branch blockers

1. **Recurrence-modulus inequality for selected package**

Need an explicit lower bound

```text
len(I_Y) >= C_rec * offDiagonalBudget(Z_Y)/B_Y^2
```

from envelope-local arithmetic, where

```text
offDiagonalBudget(Z_Y)= Σ_{ρ≠σ∈Z_Y} 2|a_ρ||a_σ| / |Im ρ - Im σ|.
```

2. **Uniform tail suppression**

Need a quantified \(o(B_Y)\) estimate for all complement contributions with
controllable constants:

```text
sup_{u∈I_Y} |R_Y(u)| <= ε_Y B_Y,   ε_Y -> 0.
```

3. **Package cardinality and line-count invariance**

Need proof that the selected family remains bounded by fixed \(M_A\) for the
branch assumptions (finite vertical lines) and does not grow with the moving
scale.

### Clustered branch blockers

1. **Cluster spectral non-degeneracy**

Need an explicit finite-dimensional bound of the form

```text
λ_min(G_Y) >= η_M > 0,
```

uniformly for admissible clustered configurations in the selected envelope window.

2. **Cluster recursion control**

Need a mechanism converting local clusters into a uniform recurrence lemma with
error \(o(B_Y)\), without reducing the item-bound below \(M_A\).

3. **Cluster-tail interaction**

Need a uniform estimate for clustered complementary terms:

```text
∑_{clusters} tail_cluster(Y,window) <= ε_Y B_Y,   ε_Y -> 0.
```

## Blocking checklist required to close the branch

- [x] formalize the half-isolated bridge hypothesis as a Lean `structure`;
- [x] prove the half-isolated transfer as a real theorem (`halfIsolatedEnvelopeBridge`);
- [ ] formalize and close the clustered bridge hypothesis as a Lean `structure` plus spectral
  bridge theorem (not done in this branch).
- [ ] use the fixed-\(M\) spectral theorem only through a closed contract bridge.

No line in this document should be interpreted as a completed unconditional theorem.
