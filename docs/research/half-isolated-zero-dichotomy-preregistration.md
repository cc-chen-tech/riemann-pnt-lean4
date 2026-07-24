# Half-Isolated Zero Dichotomy — Stage-0 Preregistration

Date fixed: 2026-07-25  
Worktree: `research/half-isolated-zero-dichotomy`  
Branch: `research/half-isolated-zero-dichotomy`  
Frozen baseline commit: `029d3376ae91ab2fb4f2a281bfaf1f6ad9687f07`  

## Scope and non-goals

- Scope: formal interface engineering for the local-dichotomy statement of rightmost
  nontrivial zeros at finite height.
- Non-goals for phase 0:
  - no RH claim,
  - no claim that one zero automatically replicates into infinitely many new zeros,
  - no new asymptotic theorem claimed from this phase’s outputs.

## Working definitions (to be frozen in code only)

Definitions below are for this milestone only and must be kept as explicit assumptions
when no proof is available:

1. `TopLayer(T, β)`:
   `{ρ | RiemannHypothesis.IsNontrivialZero ρ ∧ |ρ.im| ≤ T ∧ ρ.re = β}`.
2. `HalfIsolated(ρ, T, β, δ)`:
   `ρ ∈ TopLayer(T, β)` and all other zeros in `TopLayer(T, β)` are `δ`-separated in
   imaginary part.
3. `QuantitativeLocalCluster(T, β, δ, ρ)`:
   finite certified zero package in `TopLayer(T, β)` containing `ρ`, with size at least `2`
   and explicit radius bound by `δ`.
4. `ZeroDichotomy(T, β, δ, ρ)`:
   `HalfIsolated ... ρ` `∨` `QuantitativeLocalCluster ... ρ`.
5. `MaynardPrattDetector`:
   explicit function/instance that returns the right side of `ZeroDichotomy`.
   If not implemented, it must stay as an explicit assumption interface.

## Deliverable gates (all conjunctive)

1. **Contract-only delivery**
   - Add `PrimeNumberTheorem/HalfIsolatedZeroDichotomy/Contract.lean` with only definitions
     and API declarations; no theorem of the final dichotomy should be imported as solved.

2. **Audit interface delivery**
   - Add `PrimeNumberTheorem/HalfIsolatedZeroDichotomy/Audit.lean` listing the unresolved
     cluster-to-many-zeros assumptions as explicit typeclass fields.

3. **Preregistration consistency**
   - Add `docs/research/half-isolated-zero-dichotomy-prior-art-audit.md` and this file under
     the required path prefix.

4. **Claim-type tags**
   - Every new conclusion is tagged as one of:
     - `C`: combinatorial identity,
     - `T`: conditional theorem, or
     - `A`: analytic input.
   - No item in this phase is tagged as analytic result (`RH` or global theorem completion).

5. **No cross-worktree edits**
   - Keep files restricted to this worktree and prefix.

## Formal success condition for phase-0

Phase-0 is complete when:

- repository state remains clean except for the new prefixed files,
- explicit `MaynardPrattDetector` API exists as an assumption object and is not replaced
  by an unproven theorem of the same statement,
- each deliverable in gate 1–4 is implemented and linked to the branch-specific
  baseline commit record above.
