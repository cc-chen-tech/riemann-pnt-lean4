# VK-edge zero-cluster remainder L2 design

## Scope

Continue the actual-standard-psi bridge from
`VKEdgeZeroClusterExplicitFormulaL2` by removing the midpoint jump term from
continuous logarithmic-coordinate second moments.

This stage does not estimate:

- the complementary zero sum;
- the finite-height explicit-formula approximation error;
- Carlson zero density;
- any RH contradiction.

## Mathematical observation

The real jump term

```lean
jumpVonMangoldt (Real.exp y)
```

can be nonzero only when `Real.exp y` is a natural number.  The preimage of
the countable set of natural-number casts under the injective real
exponential is countable, hence has Lebesgue measure zero.  Therefore the
jump term is zero almost everywhere in `y`.

Consequently, deleting the jump correction does not change any continuous
local second moment.

## Public API

Add `PrimeNumberTheorem/VKEdgeZeroClusterRemainderL2.lean` with:

1. `jumpVonMangoldt_exp_ae_eq_zero`;
2. `finiteZeroClusterPsiExplicitFormulaRemainderWithoutJump`;
3. `normalizedFiniteZeroClusterPsiRemainderWithoutJump`;
4. `normalizedFiniteZeroClusterPsiRemainderWithoutJumpSecondMoment`;
5. almost-everywhere equality between the existing remainder and the
   no-jump remainder;
6. equality of their local second moments;
7. an almost-everywhere actual-standard-psi decomposition using the no-jump
   remainder.

## Verification

- Exact-type contract for every public theorem.
- Dedicated axiom audit plus central multiplicity audit registration.
- Central axiom allowlist registration.
- Focused module and contract builds.
- `./scripts/verify-baseline.sh`.

## Claim boundary

The result removes one concrete nuisance term from the actual remainder
budget.  It does not bound the remaining complement or truncation error, and
therefore does not prove an unconditional local oscillation theorem,
Carlson contradiction, or RH.
